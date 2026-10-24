module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Site
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Contracts
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Arith.Common

/-!
# ML-DSA on PPC64LE: calling the primitives on the buffers of a `Site`

As on 32-bit ARM (`Proof/MlDsa/Arm/KeyGen/Call.lean`, `CallArith.lean`,
`CallSample.lean`, `CallPack.lean`): a call of each primitive key generation
calls, with its arguments pointers into the buffers of a `Site` (`PtrIn`):
the callee's precondition from the layout (`ip_preS`, …), what the call
changes and what its postcondition says (`ip_ok`, …), and that two runs of
it with the same pointers leak the same (`ip_tr`, …).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.KeyGen

open VG VG.PPC64LE VG.Proof.MlKem.PPC64LE
open VG.Impl.MlDsa.PPC64LE.KeyGen
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## Arguments -/

section
variable {L : Lay} {Wb : List Nat} {STK : Nat} {s : State} (hs : Site L Wb STK s)
include hs

/-- A pointer argument's register, as the callee sees it. -/
theorem Site.vG {as : List (Reg × Arg)} (hg : glueOk as = true) (hn : (as.map Prod.fst).Nodup) {d : Reg} {q : Ptr}
    (hm : (d, .ptr q) ∈ as) (hq : argOk (.ptr q) = true) (hd : d ∉ linkRegs) (rd wr : List Region) :
    (view (glueSt s as) rd wr).gpr d = lpa L q := by
  rw [view_gpr _ _ _ hd, hs.gE hg hn hm hq]

/-- The depth of a callee's stack is in the address space. -/
theorem Site.depth {c : Prog isa} {S : Nat} (h1 : sdepth c ≤ S) (h2 : S ≤ STK) : sdepth c < 2 ^ 64 :=
  Nat.lt_of_le_of_lt (Nat.le_trans h1 (Nat.le_trans h2 hs.spk)) s.sp.isLt

end

/-- An integer argument's register, as the callee sees it. -/
theorem vI {s : State} {as : List (Reg × Arg)} (hg : glueOk as = true) (hn : (as.map Prod.fst).Nodup) {d : Reg}
    {v : Nat} (hm : (d, .imm v) ∈ as) (hd : d ∉ linkRegs) (rd wr : List Region) :
    (view (glueSt s as) rd wr).gpr d = BitVec.ofNat 64 v := by
  rw [view_gpr _ _ _ hd, glueSt_arg s hg hn hm]; rfl

/-! ## `vg_mldsa_ntt`, `vg_mldsa_inv_ntt` -/

section
variable {L : Lay} {Wb : List Nat} {STK S : Nat} {t : Poly → Poly} {f w : Ptr}

abbrev ipArgs (f w : Ptr) : List (Reg × Arg) := [(.r3, .ptr f), (.r4, .ptr w)]
abbrev ipWr (L : Lay) (f w : Ptr) : List Region := [L.R (ix f.1) f.2 1024, L.R (ix w.1) w.2 1024]

/-- The facts the NTTs need of their pointers. -/
structure IpOk (L : Lay) (Wb : List Nat) (f w : Ptr) : Prop where
  pf : PtrIn L f 1024
  pw : PtrIn L w 1024
  wf : ix f.1 ∈ Wb
  ww : ix w.1 ∈ Wb
  d : sepB L.sizes (tri f 1024) (tri w 1024) = true

theorem IpOk.hg (m : IpOk L Wb f w) : glueOk (ipArgs f w) = true := by
  simp [glueOk, argReg, m.pf.1, m.pw.1]

theorem ipArgs_nodup : ((ipArgs f w).map Prod.fst).Nodup := by simp only [List.map_cons, List.map_nil]; decide

theorem ip_cov {s : State} (hs : Site L Wb STK s) (m : IpOk L Wb f w) :
    Covers ([] ++ ipWr L f w) (s.rd ++ s.wr) ∧ Covers (ipWr L f w) s.wr :=
  ⟨Covers.right (Covers.cons (hs.cwE m.pf m.wf) (Covers.cons (hs.cwE m.pw m.ww) Covers.nil)),
    Covers.cons (hs.cwE m.pf m.wf) (Covers.cons (hs.cwE m.pw m.ww) Covers.nil)⟩

theorem ip_preS {s : State} (hs : Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (m : IpOk L Wb f w)
    (hr : Reduced s.mem (lpa L f)) :
    (inPlaceContract PPC64LE.abi t stk).pre (view (glueSt s (ipArgs f w)) [] (ipWr L f w)) := by
  have hsp := view_glue_sp s (ipArgs f w) [] (ipWr L f w)
  refine ip_pre (hs.vG m.hg ipArgs_nodup (by simp) m.pf.1 (by decide) _ _)
    (hs.vG m.hg ipArgs_nodup (by simp) m.pw.1 (by decide) _ _) rfl rfl
    (by rw [hsp]; exact Nat.le_trans hstk hs.spk) (hs.dE m.d (.inl m.wf)) (hs.kE m.pf hstk hsp)
    (hs.kE m.pw hstk hsp) (hs.fitE m.pf (by decide)) (hs.fitE m.pw (by decide)) ?_
  rw [view_glue_mem]; exact hr

theorem ip_ok {c : Prog isa} (hc : Callee c (fun stk => inPlaceContract PPC64LE.abi t stk) S) {s : State}
    (hs : Site L Wb STK s) (hS : S ≤ STK) {name : String} (m : IpOk L Wb f w)
    (hr : Reduced s.mem (lpa L f)) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [tri f 1024, tri w 1024, (1, 0, STK)]) s s' →
      PolyIs s'.mem (lpa L f) (t (polyAt s.mem (lpa L f))) → Q s') :
    WP isa (callAt name c (ipArgs f w)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨c1, c2⟩ := ip_cov hs m
  refine callV hver.1 (hs.depth hc.stack hS) m.hg (ip_preS hs (Nat.le_trans hstk hS) m hr) c1 c2
    fun s' hk hp => hQ s' (hs.keptW [tri f 1024, tri w 1024] (Nat.le_trans hc.stack hS) hk) ?_
  have := ip_post hp
  rwa [State.withRegions_mem, hs.vG m.hg ipArgs_nodup (by simp) m.pf.1 (by decide), view_glue_mem] at this

theorem ip_tr {c : Prog isa} (hc : Callee c (fun stk => inPlaceContract PPC64LE.abi t stk) S) (hS : S ≤ STK)
    {name : String} (m : IpOk L Wb f w) {P : State → State → Prop}
    (hP : ∀ x y, P x y → Site L Wb STK x ∧ Site L Wb STK y ∧ x.sp = y.sp ∧ Reduced x.mem (lpa L f) ∧
      Reduced y.mem (lpa L f)) :
    RelCT isa P (callAt name c (ipArgs f w)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  refine callV_tr hver.1 hver.2.1 m.hg fun x y h => ?_
  obtain ⟨hx, hy, hsp, rx, ry⟩ := hP x y h
  refine ⟨[], ipWr L f w, ip_preS hx (Nat.le_trans hstk hS) m rx, ip_preS hy (Nat.le_trans hstk hS) m ry,
    ip_pub ?_ ?_ ?_, (ip_cov hx m).1, (ip_cov hx m).2, (ip_cov hy m).1, (ip_cov hy m).2⟩
  · rw [view_glue_sp, view_glue_sp, hsp]
  · rw [hx.vG m.hg ipArgs_nodup (by simp) m.pf.1 (by decide), hy.vG m.hg ipArgs_nodup (by simp) m.pf.1 (by decide)]
  · rw [hx.vG m.hg ipArgs_nodup (by simp) m.pw.1 (by decide), hy.vG m.hg ipArgs_nodup (by simp) m.pw.1 (by decide)]

end

/-! ## `vg_mldsa_multiply_ntt`, `vg_mldsa_multiply_add_ntt` -/

section
variable {L : Lay} {Wb : List Nat} {STK S : Nat} {h f g : Ptr}

abbrev mulArgs (h f g : Ptr) : List (Reg × Arg) := [(.r3, .ptr h), (.r4, .ptr f), (.r5, .ptr g)]
abbrev mulRd (L : Lay) (f g : Ptr) : List Region := [L.R (ix f.1) f.2 1024, L.R (ix g.1) g.2 1024]
abbrev mulWr (L : Lay) (h : Ptr) : List Region := [L.R (ix h.1) h.2 1024]

/-- The facts the multiplications need of their pointers. -/
structure MulOk (L : Lay) (Wb : List Nat) (h f g : Ptr) : Prop where
  ph : PtrIn L h 1024
  pf : PtrIn L f 1024
  pg : PtrIn L g 1024
  wh : ix h.1 ∈ Wb
  d1 : sepB L.sizes (tri h 1024) (tri f 1024) = true
  d2 : sepB L.sizes (tri h 1024) (tri g 1024) = true

theorem MulOk.hg (m : MulOk L Wb h f g) : glueOk (mulArgs h f g) = true := by
  simp [glueOk, argReg, m.ph.1, m.pf.1, m.pg.1]

theorem mulArgs_nodup : ((mulArgs h f g).map Prod.fst).Nodup := by simp only [List.map_cons, List.map_nil]; decide

theorem mul_cov {s : State} (hs : Site L Wb STK s) (m : MulOk L Wb h f g) :
    Covers (mulRd L f g ++ mulWr L h) (s.rd ++ s.wr) ∧ Covers (mulWr L h) s.wr :=
  ⟨Covers.append_left (Covers.cons (hs.crE m.pf) (Covers.cons (hs.crE m.pg) Covers.nil))
    (Covers.right (Covers.cons (hs.cwE m.ph m.wh) Covers.nil)), Covers.cons (hs.cwE m.ph m.wh) Covers.nil⟩

theorem mul_vg {s : State} (hs : Site L Wb STK s) (m : MulOk L Wb h f g) (rd wr : List Region) :
    (view (glueSt s (mulArgs h f g)) rd wr).gpr .r3 = lpa L h ∧
    (view (glueSt s (mulArgs h f g)) rd wr).gpr .r4 = lpa L f ∧
    (view (glueSt s (mulArgs h f g)) rd wr).gpr .r5 = lpa L g :=
  ⟨hs.vG m.hg mulArgs_nodup (by simp) m.ph.1 (by decide) _ _, hs.vG m.hg mulArgs_nodup (by simp) m.pf.1 (by decide) _ _,
    hs.vG m.hg mulArgs_nodup (by simp) m.pg.1 (by decide) _ _⟩

theorem mul_preS {s : State} (hs : Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (m : MulOk L Wb h f g)
    (rf : Reduced s.mem (lpa L f)) (rg : Reduced s.mem (lpa L g)) :
    (mulContract PPC64LE.abi stk).pre (view (glueSt s (mulArgs h f g)) (mulRd L f g) (mulWr L h)) := by
  have hsp := view_glue_sp s (mulArgs h f g) (mulRd L f g) (mulWr L h)
  obtain ⟨g3, g4, g5⟩ := mul_vg hs m (mulRd L f g) (mulWr L h)
  refine mul_pre g3 g4 g5 rfl rfl (by rw [hsp]; exact Nat.le_trans hstk hs.spk) (hs.dE m.d1 (.inl m.wh))
    (hs.dE m.d2 (.inl m.wh)) (hs.kE m.ph hstk hsp) (hs.kE m.pf hstk hsp) (hs.kE m.pg hstk hsp)
    (hs.fitE m.ph (by decide)) (hs.fitE m.pf (by decide)) (hs.fitE m.pg (by decide)) ?_ ?_
  · rw [view_glue_mem]; exact rf
  · rw [view_glue_mem]; exact rg

theorem mulAdd_preS {s : State} (hs : Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (m : MulOk L Wb h f g)
    (rh : Reduced s.mem (lpa L h)) (rf : Reduced s.mem (lpa L f)) (rg : Reduced s.mem (lpa L g)) :
    (mulAddContract PPC64LE.abi stk).pre (view (glueSt s (mulArgs h f g)) (mulRd L f g) (mulWr L h)) := by
  have hsp := view_glue_sp s (mulArgs h f g) (mulRd L f g) (mulWr L h)
  obtain ⟨g3, g4, g5⟩ := mul_vg hs m (mulRd L f g) (mulWr L h)
  refine mulAdd_pre g3 g4 g5 rfl rfl (by rw [hsp]; exact Nat.le_trans hstk hs.spk) (hs.dE m.d1 (.inl m.wh))
    (hs.dE m.d2 (.inl m.wh)) (hs.kE m.ph hstk hsp) (hs.kE m.pf hstk hsp) (hs.kE m.pg hstk hsp)
    (hs.fitE m.ph (by decide)) (hs.fitE m.pf (by decide)) (hs.fitE m.pg (by decide)) ?_ ?_ ?_
  · rw [view_glue_mem]; exact rh
  · rw [view_glue_mem]; exact rf
  · rw [view_glue_mem]; exact rg

theorem mul_ok {c : Prog isa} (hc : Callee c (fun stk => mulContract PPC64LE.abi stk) S) {s : State}
    (hs : Site L Wb STK s) (hS : S ≤ STK) {name : String} (m : MulOk L Wb h f g)
    (rf : Reduced s.mem (lpa L f)) (rg : Reduced s.mem (lpa L g)) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [tri h 1024, (1, 0, STK)]) s s' →
      PolyIs s'.mem (lpa L h) (multiplyNTT (polyAt s.mem (lpa L f)) (polyAt s.mem (lpa L g))) → Q s') :
    WP isa (callAt name c (mulArgs h f g)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨c1, c2⟩ := mul_cov hs m
  refine callV hver.1 (hs.depth hc.stack hS) m.hg (mul_preS hs (Nat.le_trans hstk hS) m rf rg) c1 c2
    fun s' hk hp => hQ s' (hs.keptW [tri h 1024] (Nat.le_trans hc.stack hS) hk) ?_
  obtain ⟨g3, g4, g5⟩ := mul_vg hs m (mulRd L f g) (mulWr L h)
  have := mul_post hp
  rwa [State.withRegions_mem, g3, g4, g5, view_glue_mem] at this

theorem mulAdd_ok {c : Prog isa} (hc : Callee c (fun stk => mulAddContract PPC64LE.abi stk) S) {s : State}
    (hs : Site L Wb STK s) (hS : S ≤ STK) {name : String} (m : MulOk L Wb h f g)
    (rh : Reduced s.mem (lpa L h)) (rf : Reduced s.mem (lpa L f)) (rg : Reduced s.mem (lpa L g))
    {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [tri h 1024, (1, 0, STK)]) s s' →
      PolyIs s'.mem (lpa L h) (add (polyAt s.mem (lpa L h))
        (multiplyNTT (polyAt s.mem (lpa L f)) (polyAt s.mem (lpa L g)))) → Q s') :
    WP isa (callAt name c (mulArgs h f g)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨c1, c2⟩ := mul_cov hs m
  refine callV hver.1 (hs.depth hc.stack hS) m.hg (mulAdd_preS hs (Nat.le_trans hstk hS) m rh rf rg) c1 c2
    fun s' hk hp => hQ s' (hs.keptW [tri h 1024] (Nat.le_trans hc.stack hS) hk) ?_
  obtain ⟨g3, g4, g5⟩ := mul_vg hs m (mulRd L f g) (mulWr L h)
  have := mulAdd_post hp
  rwa [State.withRegions_mem, g3, g4, g5, view_glue_mem] at this

theorem mul_tr {c : Prog isa} (hc : Callee c (fun stk => mulContract PPC64LE.abi stk) S) (hS : S ≤ STK)
    {name : String} (m : MulOk L Wb h f g) {P : State → State → Prop}
    (hP : ∀ x y, P x y → Site L Wb STK x ∧ Site L Wb STK y ∧ x.sp = y.sp ∧
      Reduced x.mem (lpa L f) ∧ Reduced x.mem (lpa L g) ∧ Reduced y.mem (lpa L f) ∧ Reduced y.mem (lpa L g)) :
    RelCT isa P (callAt name c (mulArgs h f g)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  refine callV_tr hver.1 hver.2.1 m.hg fun x y hxy => ?_
  obtain ⟨hx, hy, hsp, rxf, rxg, ryf, ryg⟩ := hP x y hxy
  obtain ⟨gx3, gx4, gx5⟩ := mul_vg hx m (mulRd L f g) (mulWr L h)
  obtain ⟨gy3, gy4, gy5⟩ := mul_vg hy m (mulRd L f g) (mulWr L h)
  exact ⟨mulRd L f g, mulWr L h, mul_preS hx (Nat.le_trans hstk hS) m rxf rxg,
    mul_preS hy (Nat.le_trans hstk hS) m ryf ryg,
    mul_pub (by rw [view_glue_sp, view_glue_sp, hsp]) (by rw [gx3, gy3]) (by rw [gx4, gy4]) (by rw [gx5, gy5]),
    (mul_cov hx m).1, (mul_cov hx m).2, (mul_cov hy m).1, (mul_cov hy m).2⟩

theorem mulAdd_tr {c : Prog isa} (hc : Callee c (fun stk => mulAddContract PPC64LE.abi stk) S) (hS : S ≤ STK)
    {name : String} (m : MulOk L Wb h f g) {P : State → State → Prop}
    (hP : ∀ x y, P x y → Site L Wb STK x ∧ Site L Wb STK y ∧ x.sp = y.sp ∧
      Reduced x.mem (lpa L h) ∧ Reduced x.mem (lpa L f) ∧ Reduced x.mem (lpa L g) ∧
      Reduced y.mem (lpa L h) ∧ Reduced y.mem (lpa L f) ∧ Reduced y.mem (lpa L g)) :
    RelCT isa P (callAt name c (mulArgs h f g)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  refine callV_tr hver.1 hver.2.1 m.hg fun x y hxy => ?_
  obtain ⟨hx, hy, hsp, rxh, rxf, rxg, ryh, ryf, ryg⟩ := hP x y hxy
  obtain ⟨gx3, gx4, gx5⟩ := mul_vg hx m (mulRd L f g) (mulWr L h)
  obtain ⟨gy3, gy4, gy5⟩ := mul_vg hy m (mulRd L f g) (mulWr L h)
  exact ⟨mulRd L f g, mulWr L h, mulAdd_preS hx (Nat.le_trans hstk hS) m rxh rxf rxg,
    mulAdd_preS hy (Nat.le_trans hstk hS) m ryh ryf ryg,
    mulAdd_pub (by rw [view_glue_sp, view_glue_sp, hsp]) (by rw [gx3, gy3]) (by rw [gx4, gy4]) (by rw [gx5, gy5]),
    (mul_cov hx m).1, (mul_cov hx m).2, (mul_cov hy m).1, (mul_cov hy m).2⟩

end

/-! ## `vg_mldsa_add` -/

section
variable {L : Lay} {Wb : List Nat} {STK S : Nat} {f g : Ptr}

abbrev addArgs (f g : Ptr) : List (Reg × Arg) := [(.r3, .ptr f), (.r4, .ptr g)]
abbrev addRd (L : Lay) (g : Ptr) : List Region := [L.R (ix g.1) g.2 1024]
abbrev addWr (L : Lay) (f : Ptr) : List Region := [L.R (ix f.1) f.2 1024]

/-- The facts `vg_mldsa_add` needs of its pointers. -/
structure AddOk (L : Lay) (Wb : List Nat) (f g : Ptr) : Prop where
  pf : PtrIn L f 1024
  pg : PtrIn L g 1024
  wf : ix f.1 ∈ Wb
  d : sepB L.sizes (tri f 1024) (tri g 1024) = true

theorem AddOk.hg (m : AddOk L Wb f g) : glueOk (addArgs f g) = true := by
  simp [glueOk, argReg, m.pf.1, m.pg.1]

theorem addArgs_nodup : ((addArgs f g).map Prod.fst).Nodup := by simp only [List.map_cons, List.map_nil]; decide

theorem add_cov {s : State} (hs : Site L Wb STK s) (m : AddOk L Wb f g) :
    Covers (addRd L g ++ addWr L f) (s.rd ++ s.wr) ∧ Covers (addWr L f) s.wr :=
  ⟨Covers.append_left (Covers.cons (hs.crE m.pg) Covers.nil) (Covers.right (Covers.cons (hs.cwE m.pf m.wf) Covers.nil)),
    Covers.cons (hs.cwE m.pf m.wf) Covers.nil⟩

theorem add_vg {s : State} (hs : Site L Wb STK s) (m : AddOk L Wb f g) (rd wr : List Region) :
    (view (glueSt s (addArgs f g)) rd wr).gpr .r3 = lpa L f ∧
    (view (glueSt s (addArgs f g)) rd wr).gpr .r4 = lpa L g :=
  ⟨hs.vG m.hg addArgs_nodup (by simp) m.pf.1 (by decide) _ _, hs.vG m.hg addArgs_nodup (by simp) m.pg.1 (by decide) _ _⟩

theorem add_preS {s : State} (hs : Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (m : AddOk L Wb f g)
    (rf : Reduced s.mem (lpa L f)) (rg : Reduced s.mem (lpa L g)) :
    (addContract PPC64LE.abi stk).pre (view (glueSt s (addArgs f g)) (addRd L g) (addWr L f)) := by
  have hsp := view_glue_sp s (addArgs f g) (addRd L g) (addWr L f)
  obtain ⟨g3, g4⟩ := add_vg hs m (addRd L g) (addWr L f)
  refine add_pre g3 g4 rfl rfl (by rw [hsp]; exact Nat.le_trans hstk hs.spk) (hs.dE m.d (.inl m.wf))
    (hs.kE m.pf hstk hsp) (hs.kE m.pg hstk hsp) (hs.fitE m.pf (by decide)) (hs.fitE m.pg (by decide)) ?_ ?_
  · rw [view_glue_mem]; exact rf
  · rw [view_glue_mem]; exact rg

theorem add_ok {c : Prog isa} (hc : Callee c (fun stk => addContract PPC64LE.abi stk) S) {s : State}
    (hs : Site L Wb STK s) (hS : S ≤ STK) {name : String} (m : AddOk L Wb f g)
    (rf : Reduced s.mem (lpa L f)) (rg : Reduced s.mem (lpa L g)) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [tri f 1024, (1, 0, STK)]) s s' →
      PolyIs s'.mem (lpa L f) (add (polyAt s.mem (lpa L f)) (polyAt s.mem (lpa L g))) → Q s') :
    WP isa (callAt name c (addArgs f g)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨c1, c2⟩ := add_cov hs m
  refine callV hver.1 (hs.depth hc.stack hS) m.hg (add_preS hs (Nat.le_trans hstk hS) m rf rg) c1 c2
    fun s' hk hp => hQ s' (hs.keptW [tri f 1024] (Nat.le_trans hc.stack hS) hk) ?_
  obtain ⟨g3, g4⟩ := add_vg hs m (addRd L g) (addWr L f)
  have := add_post hp
  rwa [State.withRegions_mem, g3, g4, view_glue_mem] at this

theorem add_tr {c : Prog isa} (hc : Callee c (fun stk => addContract PPC64LE.abi stk) S) (hS : S ≤ STK)
    {name : String} (m : AddOk L Wb f g) {P : State → State → Prop}
    (hP : ∀ x y, P x y → Site L Wb STK x ∧ Site L Wb STK y ∧ x.sp = y.sp ∧
      Reduced x.mem (lpa L f) ∧ Reduced x.mem (lpa L g) ∧ Reduced y.mem (lpa L f) ∧ Reduced y.mem (lpa L g)) :
    RelCT isa P (callAt name c (addArgs f g)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  refine callV_tr hver.1 hver.2.1 m.hg fun x y hxy => ?_
  obtain ⟨hx, hy, hsp, rxf, rxg, ryf, ryg⟩ := hP x y hxy
  obtain ⟨gx3, gx4⟩ := add_vg hx m (addRd L g) (addWr L f)
  obtain ⟨gy3, gy4⟩ := add_vg hy m (addRd L g) (addWr L f)
  exact ⟨addRd L g, addWr L f, add_preS hx (Nat.le_trans hstk hS) m rxf rxg, add_preS hy (Nat.le_trans hstk hS) m ryf ryg,
    add_pub (by rw [view_glue_sp, view_glue_sp, hsp]) (by rw [gx3, gy3]) (by rw [gx4, gy4]),
    (add_cov hx m).1, (add_cov hx m).2, (add_cov hy m).1, (add_cov hy m).2⟩

end

end VG.Proof.MlDsa.PPC64LE.KeyGen
