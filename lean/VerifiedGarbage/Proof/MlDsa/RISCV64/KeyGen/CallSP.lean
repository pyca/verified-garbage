module

import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.Common
public import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.Site
public import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.Contracts

/-! ### `MlDsa.RISCV64.KeyGen.Call`, which this module and modules that import it used -/

section

/-!
# ML-DSA on RISC-V: calling the primitives on the buffers of a `Site`

As on PPC64LE (`Proof/MlDsa/PPC64LE/KeyGen/CallSP.lean`, `CallArith.lean`,
`CallSample.lean`, `CallPack.lean`): a call of each primitive key generation
calls, with its arguments pointers into the buffers of a `Site` (`PtrIn`):
the callee's precondition from the layout (`ip_preS`, …), what the call
changes and what its postcondition says (`ip_ok`, …), and that two runs of
it with the same pointers leak the same (`ip_tr`, …).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.KeyGen

open VG VG.RISCV64 VG.Proof.MlKem.RISCV64
open VG.Impl.MlDsa.RISCV64.KeyGen
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

abbrev ipArgs (f w : Ptr) : List (Reg × Arg) := [(.a0, .ptr f), (.a1, .ptr w)]
abbrev ipWr (L : Lay) (f w : Ptr) : List Region := [L.R (ix f.1) f.2 1024, L.R (ix w.1) w.2 1024]

/-- The facts the NTTs need of their pointers. -/
structure IpOk (L : Lay) (Wb : List Nat) (f w : Ptr) : Prop where
  pf : PtrIn L f 1024
  pw : PtrIn L w 1024
  wf : ix f.1 ∈ Wb
  ww : ix w.1 ∈ Wb
  d : sepB L.sizes (tri f 1024) (tri w 1024) = true
  a_f : AlS f
  a_w : AlS w

theorem IpOk.hg (m : IpOk L Wb f w) : glueOk (ipArgs f w) = true := by
  simp [glueOk, argReg, m.pf.1, m.pw.1]

theorem ipArgs_nodup : ((ipArgs f w).map Prod.fst).Nodup := by simp only [List.map_cons, List.map_nil]; decide

theorem ip_cov {s : State} (hs : Site L Wb STK s) (m : IpOk L Wb f w) :
    Covers ([] ++ ipWr L f w) (s.rd ++ s.wr) ∧ Covers (ipWr L f w) s.wr :=
  ⟨Covers.right (Covers.cons (hs.cwE m.pf m.wf) (Covers.cons (hs.cwE m.pw m.ww) Covers.nil)),
    Covers.cons (hs.cwE m.pf m.wf) (Covers.cons (hs.cwE m.pw m.ww) Covers.nil)⟩

theorem ip_preS {s : State} (hs : Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (m : IpOk L Wb f w)
    (hr : Reduced s.mem (lpa L f)) :
    (inPlaceContract RISCV64.abi t stk).pre (view (glueSt s (ipArgs f w)) [] (ipWr L f w)) := by
  have hsp := view_glue_sp s (ipArgs f w) [] (ipWr L f w)
  refine ip_pre (hs.vG m.hg ipArgs_nodup (by simp) m.pf.1 (by decide) _ _)
    (hs.vG m.hg ipArgs_nodup (by simp) m.pw.1 (by decide) _ _) rfl rfl
    (by rw [hsp]; exact Nat.le_trans hstk hs.spk) (hs.alSp hsp) (hs.alS4 m.a_f) (hs.alS m.a_w) (hs.dE m.d (.inl m.wf)) (hs.kE m.pf hstk hsp)
    (hs.kE m.pw hstk hsp) (hs.fitE m.pf (by decide)) (hs.fitE m.pw (by decide)) ?_
  rw [view_glue_mem]; exact hr

theorem ip_ok {c : Prog isa} (hc : Callee c (fun stk => inPlaceContract RISCV64.abi t stk) S) {s : State}
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

theorem ip_tr {c : Prog isa} (hc : Callee c (fun stk => inPlaceContract RISCV64.abi t stk) S) (hS : S ≤ STK)
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

abbrev mulArgs (h f g : Ptr) : List (Reg × Arg) := [(.a0, .ptr h), (.a1, .ptr f), (.a2, .ptr g)]
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
  a_h : AlS h
  a_f : AlS f
  a_g : AlS g

theorem MulOk.hg (m : MulOk L Wb h f g) : glueOk (mulArgs h f g) = true := by
  simp [glueOk, argReg, m.ph.1, m.pf.1, m.pg.1]

theorem mulArgs_nodup : ((mulArgs h f g).map Prod.fst).Nodup := by simp only [List.map_cons, List.map_nil]; decide

theorem mul_cov {s : State} (hs : Site L Wb STK s) (m : MulOk L Wb h f g) :
    Covers (mulRd L f g ++ mulWr L h) (s.rd ++ s.wr) ∧ Covers (mulWr L h) s.wr :=
  ⟨Covers.append_left (Covers.cons (hs.crE m.pf) (Covers.cons (hs.crE m.pg) Covers.nil))
    (Covers.right (Covers.cons (hs.cwE m.ph m.wh) Covers.nil)), Covers.cons (hs.cwE m.ph m.wh) Covers.nil⟩

theorem mul_vg {s : State} (hs : Site L Wb STK s) (m : MulOk L Wb h f g) (rd wr : List Region) :
    (view (glueSt s (mulArgs h f g)) rd wr).gpr .a0 = lpa L h ∧
    (view (glueSt s (mulArgs h f g)) rd wr).gpr .a1 = lpa L f ∧
    (view (glueSt s (mulArgs h f g)) rd wr).gpr .a2 = lpa L g :=
  ⟨hs.vG m.hg mulArgs_nodup (by simp) m.ph.1 (by decide) _ _, hs.vG m.hg mulArgs_nodup (by simp) m.pf.1 (by decide) _ _,
    hs.vG m.hg mulArgs_nodup (by simp) m.pg.1 (by decide) _ _⟩

theorem mul_preS {s : State} (hs : Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (m : MulOk L Wb h f g)
    (rf : Reduced s.mem (lpa L f)) (rg : Reduced s.mem (lpa L g)) :
    (mulContract RISCV64.abi stk).pre (view (glueSt s (mulArgs h f g)) (mulRd L f g) (mulWr L h)) := by
  have hsp := view_glue_sp s (mulArgs h f g) (mulRd L f g) (mulWr L h)
  obtain ⟨g3, g4, g5⟩ := mul_vg hs m (mulRd L f g) (mulWr L h)
  refine mul_pre g3 g4 g5 rfl rfl (by rw [hsp]; exact Nat.le_trans hstk hs.spk) (hs.alSp hsp) (hs.alS4 m.a_h) (hs.alS4 m.a_f) (hs.alS4 m.a_g) (hs.dE m.d1 (.inl m.wh))
    (hs.dE m.d2 (.inl m.wh)) (hs.kE m.ph hstk hsp) (hs.kE m.pf hstk hsp) (hs.kE m.pg hstk hsp)
    (hs.fitE m.ph (by decide)) (hs.fitE m.pf (by decide)) (hs.fitE m.pg (by decide)) ?_ ?_
  · rw [view_glue_mem]; exact rf
  · rw [view_glue_mem]; exact rg

theorem mulAdd_preS {s : State} (hs : Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (m : MulOk L Wb h f g)
    (rh : Reduced s.mem (lpa L h)) (rf : Reduced s.mem (lpa L f)) (rg : Reduced s.mem (lpa L g)) :
    (mulAddContract RISCV64.abi stk).pre (view (glueSt s (mulArgs h f g)) (mulRd L f g) (mulWr L h)) := by
  have hsp := view_glue_sp s (mulArgs h f g) (mulRd L f g) (mulWr L h)
  obtain ⟨g3, g4, g5⟩ := mul_vg hs m (mulRd L f g) (mulWr L h)
  refine mulAdd_pre g3 g4 g5 rfl rfl (by rw [hsp]; exact Nat.le_trans hstk hs.spk) (hs.alSp hsp) (hs.alS4 m.a_h) (hs.alS4 m.a_f) (hs.alS4 m.a_g) (hs.dE m.d1 (.inl m.wh))
    (hs.dE m.d2 (.inl m.wh)) (hs.kE m.ph hstk hsp) (hs.kE m.pf hstk hsp) (hs.kE m.pg hstk hsp)
    (hs.fitE m.ph (by decide)) (hs.fitE m.pf (by decide)) (hs.fitE m.pg (by decide)) ?_ ?_ ?_
  · rw [view_glue_mem]; exact rh
  · rw [view_glue_mem]; exact rf
  · rw [view_glue_mem]; exact rg

theorem mul_ok {c : Prog isa} (hc : Callee c (fun stk => mulContract RISCV64.abi stk) S) {s : State}
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

theorem mulAdd_ok {c : Prog isa} (hc : Callee c (fun stk => mulAddContract RISCV64.abi stk) S) {s : State}
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

theorem mul_tr {c : Prog isa} (hc : Callee c (fun stk => mulContract RISCV64.abi stk) S) (hS : S ≤ STK)
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

theorem mulAdd_tr {c : Prog isa} (hc : Callee c (fun stk => mulAddContract RISCV64.abi stk) S) (hS : S ≤ STK)
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

abbrev addArgs (f g : Ptr) : List (Reg × Arg) := [(.a0, .ptr f), (.a1, .ptr g)]
abbrev addRd (L : Lay) (g : Ptr) : List Region := [L.R (ix g.1) g.2 1024]
abbrev addWr (L : Lay) (f : Ptr) : List Region := [L.R (ix f.1) f.2 1024]

/-- The facts `vg_mldsa_add` needs of its pointers. -/
structure AddOk (L : Lay) (Wb : List Nat) (f g : Ptr) : Prop where
  pf : PtrIn L f 1024
  pg : PtrIn L g 1024
  wf : ix f.1 ∈ Wb
  d : sepB L.sizes (tri f 1024) (tri g 1024) = true
  a_f : AlS f
  a_g : AlS g

theorem AddOk.hg (m : AddOk L Wb f g) : glueOk (addArgs f g) = true := by
  simp [glueOk, argReg, m.pf.1, m.pg.1]

theorem addArgs_nodup : ((addArgs f g).map Prod.fst).Nodup := by simp only [List.map_cons, List.map_nil]; decide

theorem add_cov {s : State} (hs : Site L Wb STK s) (m : AddOk L Wb f g) :
    Covers (addRd L g ++ addWr L f) (s.rd ++ s.wr) ∧ Covers (addWr L f) s.wr :=
  ⟨Covers.append_left (Covers.cons (hs.crE m.pg) Covers.nil) (Covers.right (Covers.cons (hs.cwE m.pf m.wf) Covers.nil)),
    Covers.cons (hs.cwE m.pf m.wf) Covers.nil⟩

theorem add_vg {s : State} (hs : Site L Wb STK s) (m : AddOk L Wb f g) (rd wr : List Region) :
    (view (glueSt s (addArgs f g)) rd wr).gpr .a0 = lpa L f ∧
    (view (glueSt s (addArgs f g)) rd wr).gpr .a1 = lpa L g :=
  ⟨hs.vG m.hg addArgs_nodup (by simp) m.pf.1 (by decide) _ _, hs.vG m.hg addArgs_nodup (by simp) m.pg.1 (by decide) _ _⟩

theorem add_preS {s : State} (hs : Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (m : AddOk L Wb f g)
    (rf : Reduced s.mem (lpa L f)) (rg : Reduced s.mem (lpa L g)) :
    (addContract RISCV64.abi stk).pre (view (glueSt s (addArgs f g)) (addRd L g) (addWr L f)) := by
  have hsp := view_glue_sp s (addArgs f g) (addRd L g) (addWr L f)
  obtain ⟨g3, g4⟩ := add_vg hs m (addRd L g) (addWr L f)
  refine add_pre g3 g4 rfl rfl (by rw [hsp]; exact Nat.le_trans hstk hs.spk) (hs.alSp hsp) (hs.alS4 m.a_f) (hs.alS4 m.a_g) (hs.dE m.d (.inl m.wf))
    (hs.kE m.pf hstk hsp) (hs.kE m.pg hstk hsp) (hs.fitE m.pf (by decide)) (hs.fitE m.pg (by decide)) ?_ ?_
  · rw [view_glue_mem]; exact rf
  · rw [view_glue_mem]; exact rg

theorem add_ok {c : Prog isa} (hc : Callee c (fun stk => addContract RISCV64.abi stk) S) {s : State}
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

theorem add_tr {c : Prog isa} (hc : Callee c (fun stk => addContract RISCV64.abi stk) S) (hS : S ≤ STK)
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

end VG.Proof.MlDsa.RISCV64.KeyGen

end

end

/-!
# ML-DSA on RISC-V: calling the samplers, `Power2Round` and the packing

As `ip_ok` and `ip_tr` (`Call.lean`), for `vg_mldsa_rej_ntt_poly`,
`vg_mldsa_rej_bounded_poly`, `vg_mldsa_power2round`,
`vg_mldsa_simple_bit_pack` and `vg_mldsa_bit_pack`. An integer argument is
moved to the whole register; the callees read its low word (`imm32`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.KeyGen

open VG VG.RISCV64 VG.Proof.MlKem.RISCV64
open VG.Impl.MlDsa.RISCV64.KeyGen
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

theorem imm32 {v : Nat} (h : v < 2 ^ 32) : (BitVec.ofNat 64 v).setWidth 32 = BitVec.ofNat 32 v :=
  VG.Proof.MlKem.RISCV64.setWidth32_ofNat (imm_toNat (by omega_arith)) h

theorem imm32_toNat {v : Nat} (h : v < 2 ^ 32) : (BitVec.ofNat 32 v).toNat = v := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem argOk_imm {v : Nat} (h : v < 2 ^ 31 - 2048) : argOk (.imm v) = true := by
  simp only [argOk, decide_eq_true_eq]; exact h

/-! ## `vg_mldsa_rej_ntt_poly` -/

section
variable {L : Lay} {Wb : List Nat} {STK S : Nat} {sd a w : Ptr}

abbrev rnArgs (sd a w : Ptr) : List (Reg × Arg) := [(.a0, .ptr sd), (.a1, .ptr a), (.a2, .ptr w)]
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
  a_a : AlS a
  a_w : AlS w

theorem RnOk.hg (m : RnOk L Wb sd a w) : glueOk (rnArgs sd a w) = true := by
  simp [glueOk, argReg, m.ps.1, m.pa.1, m.pw.1]

theorem rnArgs_nodup : ((rnArgs sd a w).map Prod.fst).Nodup := by simp only [List.map_cons, List.map_nil]; decide

theorem rn_vg {s : State} (hs : Site L Wb STK s) (m : RnOk L Wb sd a w) (rd wr : List Region) :
    (view (glueSt s (rnArgs sd a w)) rd wr).gpr .a0 = lpa L sd ∧
    (view (glueSt s (rnArgs sd a w)) rd wr).gpr .a1 = lpa L a ∧
    (view (glueSt s (rnArgs sd a w)) rd wr).gpr .a2 = lpa L w :=
  ⟨hs.vG m.hg rnArgs_nodup (by simp) m.ps.1 (by decide) _ _, hs.vG m.hg rnArgs_nodup (by simp) m.pa.1 (by decide) _ _,
    hs.vG m.hg rnArgs_nodup (by simp) m.pw.1 (by decide) _ _⟩

theorem rn_cov {s : State} (hs : Site L Wb STK s) (m : RnOk L Wb sd a w) :
    Covers (rnRd L sd ++ rnWr L a w) (s.rd ++ s.wr) ∧ Covers (rnWr L a w) s.wr :=
  ⟨Covers.append_left (Covers.cons (hs.crE m.ps) Covers.nil)
    (Covers.right (Covers.cons (hs.cwE m.pa m.wa) (Covers.cons (hs.cwE m.pw m.ww) Covers.nil))),
    Covers.cons (hs.cwE m.pa m.wa) (Covers.cons (hs.cwE m.pw m.ww) Covers.nil)⟩

theorem rn_preS {s : State} (hs : Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (m : RnOk L Wb sd a w) :
    (rejNTTContract RISCV64.abi stk).pre (view (glueSt s (rnArgs sd a w)) (rnRd L sd) (rnWr L a w)) := by
  have hsp := view_glue_sp s (rnArgs sd a w) (rnRd L sd) (rnWr L a w)
  obtain ⟨g3, g4, g5⟩ := rn_vg hs m (rnRd L sd) (rnWr L a w)
  exact rejNtt_pre g3 g4 g5 rfl rfl (by rw [hsp]; exact Nat.le_trans hstk hs.spk) (hs.alSp hsp) (hs.alS4 m.a_a) (hs.alS m.a_w) (hs.dE m.d1 (.inr m.wa))
    (hs.dE m.d2 (.inr m.ww)) (hs.dE m.d3 (.inl m.wa)) (hs.kE m.ps hstk hsp) (hs.kE m.pa hstk hsp)
    (hs.kE m.pw hstk hsp) (hs.fitE m.ps (by decide)) (hs.fitE m.pa (by decide)) (hs.fitE m.pw (by decide))

theorem rn_ok {c : Prog isa} (hc : Callee c (fun stk => rejNTTContract RISCV64.abi stk) S) {s : State}
    (hs : Site L Wb STK s) (hS : S ≤ STK) {name : String} (m : RnOk L Wb sd a w) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [tri a 1024, tri w 2048, (1, 0, STK)]) s s' →
      ((s'.gpr .a0).setWidth 32 = 1 → Reduced s'.mem (lpa L a)) →
      Outcome (fun b => rejNTTPoly b.rejNTT (bytesAt s.mem (lpa L sd) 34)) ((s'.gpr .a0).setWidth 32)
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

theorem rn_tr {c : Prog isa} (hc : Callee c (fun stk => rejNTTContract RISCV64.abi stk) S) (hS : S ≤ STK)
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
  [(.a0, .ptr sd), (.a1, .imm η), (.a2, .ptr a), (.a3, .ptr w)]
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
  a_a : AlS a
  a_w : AlS w

theorem RbOk.hg (m : RbOk L Wb sd a w) (hη : η = 2 ∨ η = 4) : glueOk (rbArgs sd η a w) = true := by
  have : argOk (.imm η) = true := argOk_imm (by omega_arith)
  simp [glueOk, argReg, m.ps.1, m.pa.1, m.pw.1, this]

theorem rbArgs_nodup : ((rbArgs sd η a w).map Prod.fst).Nodup := by simp only [List.map_cons, List.map_nil]; decide

theorem rb_vg {s : State} (hs : Site L Wb STK s) (m : RbOk L Wb sd a w) (hη : η = 2 ∨ η = 4) (rd wr : List Region) :
    (view (glueSt s (rbArgs sd η a w)) rd wr).gpr .a0 = lpa L sd ∧
    (view (glueSt s (rbArgs sd η a w)) rd wr).gpr .a1 = BitVec.ofNat 64 η ∧
    (view (glueSt s (rbArgs sd η a w)) rd wr).gpr .a2 = lpa L a ∧
    (view (glueSt s (rbArgs sd η a w)) rd wr).gpr .a3 = lpa L w :=
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
    (rejBoundedContract RISCV64.abi stk).pre (view (glueSt s (rbArgs sd η a w)) (rbRd L sd) (rnWr L a w)) := by
  have hsp := view_glue_sp s (rbArgs sd η a w) (rbRd L sd) (rnWr L a w)
  obtain ⟨g3, g4, g5, g6⟩ := rb_vg hs m hη (rbRd L sd) (rnWr L a w)
  have e4 : ((view (glueSt s (rbArgs sd η a w)) (rbRd L sd) (rnWr L a w)).gpr .a1).setWidth 32 = BitVec.ofNat 32 η := by
    rw [g4]; exact imm32 (by omega_arith)
  exact rejBounded_pre g3 e4 g5 g6 rfl rfl
    (by rw [hsp]; exact Nat.le_trans hstk hs.spk) (hs.alSp hsp) (hs.alS4 m.a_a) (hs.alS m.a_w) (hs.dE m.d1 (.inr m.wa))
    (hs.dE m.d2 (.inr m.ww)) (hs.dE m.d3 (.inl m.wa)) (hs.kE m.ps hstk hsp) (hs.kE m.pa hstk hsp)
    (hs.kE m.pw hstk hsp) (hs.fitE m.ps (by decide)) (hs.fitE m.pa (by decide)) (hs.fitE m.pw (by decide))
    (by rw [imm32_toNat (by omega_arith)]; exact hη)

theorem rb_ok {c : Prog isa} (hc : Callee c (fun stk => rejBoundedContract RISCV64.abi stk) S) {s : State}
    (hs : Site L Wb STK s) (hS : S ≤ STK) {name : String} (m : RbOk L Wb sd a w) (hη : η = 2 ∨ η = 4)
    {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [tri a 1024, tri w 2048, (1, 0, STK)]) s s' →
      ((s'.gpr .a0).setWidth 32 = 1 → Reduced s'.mem (lpa L a)) →
      Outcome (fun b => (rejBoundedPoly η b.rejBounded (bytesAt s.mem (lpa L sd) 66)).map toRq)
        ((s'.gpr .a0).setWidth 32) (polyAt s'.mem (lpa L a)) → Q s') :
    WP isa (callAt name c (rbArgs sd η a w)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨c1, c2⟩ := rb_cov hs m
  refine callV hver.1 (hs.depth hc.stack hS) (m.hg hη) (rb_preS hs (Nat.le_trans hstk hS) m hη) c1 c2
    fun s' hk hp => hQ s' (hs.keptW [tri a 1024, tri w 2048] (Nat.le_trans hc.stack hS) hk) ?_ ?_
  all_goals
    obtain ⟨g3, g4, g5, -⟩ := rb_vg hs m hη (rbRd L sd) (rnWr L a w)
    have := rejBounded_post hp
    rw [State.withRegions_mem, State.withRegions_gpr, g3, g4, g5, view_glue_mem, imm32 (by omega_arith),
      imm32_toNat (by omega_arith)] at this
  exacts [this.1, this.2]

theorem rb_tr {c : Prog isa} (hc : Callee c (fun stk => rejBoundedContract RISCV64.abi stk) S) (hS : S ≤ STK)
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
  rw [gx3, gy3, gx4, gy4, view_glue_mem, view_glue_mem, imm32 (by omega_arith), imm32_toNat (by omega_arith)]
  exact hl

end

/-! ## `vg_mldsa_power2round` -/

section
variable {L : Lay} {Wb : List Nat} {STK S : Nat} {t t1 t0 : Ptr}

abbrev p2rArgs (t t1 t0 : Ptr) : List (Reg × Arg) := [(.a0, .ptr t), (.a1, .ptr t1), (.a2, .ptr t0)]
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
  a_t : AlS t
  a_t1 : AlS t1
  a_t0 : AlS t0

theorem P2rOk.hg (m : P2rOk L Wb t t1 t0) : glueOk (p2rArgs t t1 t0) = true := by
  simp [glueOk, argReg, m.pt.1, m.p1.1, m.p0.1]

theorem p2rArgs_nodup : ((p2rArgs t t1 t0).map Prod.fst).Nodup := by simp only [List.map_cons, List.map_nil]; decide

theorem p2r_vg {s : State} (hs : Site L Wb STK s) (m : P2rOk L Wb t t1 t0) (rd wr : List Region) :
    (view (glueSt s (p2rArgs t t1 t0)) rd wr).gpr .a0 = lpa L t ∧
    (view (glueSt s (p2rArgs t t1 t0)) rd wr).gpr .a1 = lpa L t1 ∧
    (view (glueSt s (p2rArgs t t1 t0)) rd wr).gpr .a2 = lpa L t0 :=
  ⟨hs.vG m.hg p2rArgs_nodup (by simp) m.pt.1 (by decide) _ _, hs.vG m.hg p2rArgs_nodup (by simp) m.p1.1 (by decide) _ _,
    hs.vG m.hg p2rArgs_nodup (by simp) m.p0.1 (by decide) _ _⟩

theorem p2r_cov {s : State} (hs : Site L Wb STK s) (m : P2rOk L Wb t t1 t0) :
    Covers (p2rRd L t ++ p2rWr L t1 t0) (s.rd ++ s.wr) ∧ Covers (p2rWr L t1 t0) s.wr :=
  ⟨Covers.append_left (Covers.cons (hs.crE m.pt) Covers.nil)
    (Covers.right (Covers.cons (hs.cwE m.p1 m.w1) (Covers.cons (hs.cwE m.p0 m.w0) Covers.nil))),
    Covers.cons (hs.cwE m.p1 m.w1) (Covers.cons (hs.cwE m.p0 m.w0) Covers.nil)⟩

theorem p2r_preS {s : State} (hs : Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (m : P2rOk L Wb t t1 t0)
    (hr : Reduced s.mem (lpa L t)) :
    (power2RoundContract RISCV64.abi stk).pre (view (glueSt s (p2rArgs t t1 t0)) (p2rRd L t) (p2rWr L t1 t0)) := by
  have hsp := view_glue_sp s (p2rArgs t t1 t0) (p2rRd L t) (p2rWr L t1 t0)
  obtain ⟨g3, g4, g5⟩ := p2r_vg hs m (p2rRd L t) (p2rWr L t1 t0)
  refine p2r_pre g3 g4 g5 rfl rfl (by rw [hsp]; exact Nat.le_trans hstk hs.spk) (hs.alSp hsp) (hs.alS4 m.a_t) (hs.alS4 m.a_t1) (hs.alS4 m.a_t0) (hs.dE m.d1 (.inr m.w1))
    (hs.dE m.d2 (.inr m.w0)) (hs.dE m.d3 (.inl m.w1)) (hs.kE m.pt hstk hsp) (hs.kE m.p1 hstk hsp)
    (hs.kE m.p0 hstk hsp) (hs.fitE m.pt (by decide)) (hs.fitE m.p1 (by decide)) (hs.fitE m.p0 (by decide)) ?_
  rw [view_glue_mem]; exact hr

theorem p2r_ok {c : Prog isa} (hc : Callee c (fun stk => power2RoundContract RISCV64.abi stk) S) {s : State}
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

theorem p2r_tr {c : Prog isa} (hc : Callee c (fun stk => power2RoundContract RISCV64.abi stk) S) (hS : S ≤ STK)
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
  [(.a0, .ptr f), (.a1, .imm b), (.a2, .ptr o), (.a3, .imm l)]
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
  a_f : AlS f

theorem SbpOk.lt (m : SbpOk L Wb f b o l) : b < 2 ^ 31 - 2048 ∧ 0 < l ∧ l < 2 ^ 31 - 2048 := by
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
    (view (glueSt s (sbpArgs f b o l)) rd wr).gpr .a0 = lpa L f ∧
    (view (glueSt s (sbpArgs f b o l)) rd wr).gpr .a1 = BitVec.ofNat 64 b ∧
    (view (glueSt s (sbpArgs f b o l)) rd wr).gpr .a2 = lpa L o ∧
    (view (glueSt s (sbpArgs f b o l)) rd wr).gpr .a3 = BitVec.ofNat 64 l :=
  ⟨hs.vG m.hg sbpArgs_nodup (by simp) m.pf.1 (by decide) _ _, vI m.hg sbpArgs_nodup (by simp) (by decide) _ _,
    hs.vG m.hg sbpArgs_nodup (by simp) m.po.1 (by decide) _ _, vI m.hg sbpArgs_nodup (by simp) (by decide) _ _⟩

theorem sbp_cov {s : State} (hs : Site L Wb STK s) (m : SbpOk L Wb f b o l) :
    Covers (sbpRd L f ++ sbpWr L o l) (s.rd ++ s.wr) ∧ Covers (sbpWr L o l) s.wr :=
  ⟨Covers.append_left (Covers.cons (hs.crE m.pf) Covers.nil) (Covers.right (Covers.cons (hs.cwE m.po m.wo) Covers.nil)),
    Covers.cons (hs.cwE m.po m.wo) Covers.nil⟩

theorem sbp_preS {s : State} (hs : Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (m : SbpOk L Wb f b o l)
    (hc : ∀ i < n, (coeffAt s.mem (lpa L f) i).toNat ≤ b) :
    (simpleBitPackContract RISCV64.abi stk).pre (view (glueSt s (sbpArgs f b o l)) (sbpRd L f) (sbpWr L o l)) := by
  have hsp := view_glue_sp s (sbpArgs f b o l) (sbpRd L f) (sbpWr L o l)
  obtain ⟨g3, g4, g5, g6⟩ := sbp_vg hs m (sbpRd L f) (sbpWr L o l)
  obtain ⟨lb, l0, ll⟩ := m.lt
  have e4 : ((view (glueSt s (sbpArgs f b o l)) (sbpRd L f) (sbpWr L o l)).gpr .a1).setWidth 32 = BitVec.ofNat 32 b := by
    rw [g4]; exact imm32 (by omega_arith)
  refine sbp_pre g3 e4 g5 g6 rfl (by rw [State.withRegions_wr, imm_toNat (by omega_arith)])
    (by rw [hsp]; exact Nat.le_trans hstk hs.spk) (hs.alSp hsp) (hs.alS4 m.a_f) ?_ (hs.kE m.pf hstk hsp) ?_ (hs.fitE m.pf (by decide))
    (by rw [imm_toNat (by omega_arith)]; exact hs.fitE m.po l0)
    (by rw [imm32_toNat (by omega_arith)]; exact m.hb) (by rw [imm_toNat (by omega_arith), imm32_toNat (by omega_arith)]; exact m.hl) ?_
  · rw [imm_toNat (by omega_arith)]; exact hs.dE m.d1 (.inr m.wo)
  · rw [imm_toNat (by omega_arith)]; exact hs.kE m.po hstk hsp
  · rw [view_glue_mem, imm32_toNat (by omega_arith)]; exact hc

theorem sbp_ok {c : Prog isa} (hc : Callee c (fun stk => simpleBitPackContract RISCV64.abi stk) S) {s : State}
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
  rwa [State.withRegions_mem, g3, g4, g5, g6, view_glue_mem, imm32 (by omega_arith), imm32_toNat (by omega_arith),
    imm_toNat (by omega_arith)] at this

theorem sbp_tr {c : Prog isa} (hc : Callee c (fun stk => simpleBitPackContract RISCV64.abi stk) S) (hS : S ≤ STK)
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
  [(.a0, .ptr f), (.a1, .imm a), (.a2, .imm b), (.a3, .ptr o), (.a4, .imm l)]

/-- The facts `vg_mldsa_bit_pack` needs of its arguments. -/
structure BpOk (L : Lay) (Wb : List Nat) (f : Ptr) (a b : Nat) (o : Ptr) (l : Nat) : Prop where
  pf : PtrIn L f 1024
  po : PtrIn L o l
  wo : ix o.1 ∈ Wb
  d1 : sepB L.sizes (tri f 1024) (tri o l) = true
  hab : (a, b) ∈ bitPackParams
  hl : l = 32 * bitlen (a + b)
  a_f : AlS f

theorem BpOk.lt (m : BpOk L Wb f a b o l) : a < 2 ^ 31 - 2048 ∧ b < 2 ^ 31 - 2048 ∧ 0 < l ∧ l < 2 ^ 31 - 2048 := by
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
    (view (glueSt s (bpArgs f a b o l)) rd wr).gpr .a0 = lpa L f ∧
    (view (glueSt s (bpArgs f a b o l)) rd wr).gpr .a1 = BitVec.ofNat 64 a ∧
    (view (glueSt s (bpArgs f a b o l)) rd wr).gpr .a2 = BitVec.ofNat 64 b ∧
    (view (glueSt s (bpArgs f a b o l)) rd wr).gpr .a3 = lpa L o ∧
    (view (glueSt s (bpArgs f a b o l)) rd wr).gpr .a4 = BitVec.ofNat 64 l :=
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
    (bitPackContract RISCV64.abi stk).pre (view (glueSt s (bpArgs f a b o l)) (sbpRd L f) (sbpWr L o l)) := by
  have hsp := view_glue_sp s (bpArgs f a b o l) (sbpRd L f) (sbpWr L o l)
  obtain ⟨g3, g4, g5, g6, g7⟩ := bp_vg hs m (sbpRd L f) (sbpWr L o l)
  obtain ⟨la, lb, l0, ll⟩ := m.lt
  have e4 : ((view (glueSt s (bpArgs f a b o l)) (sbpRd L f) (sbpWr L o l)).gpr .a1).setWidth 32 = BitVec.ofNat 32 a := by
    rw [g4]; exact imm32 (by omega_arith)
  have e5 : ((view (glueSt s (bpArgs f a b o l)) (sbpRd L f) (sbpWr L o l)).gpr .a2).setWidth 32 = BitVec.ofNat 32 b := by
    rw [g5]; exact imm32 (by omega_arith)
  refine bp_pre g3 e4 e5 g6 g7 rfl
    (by rw [State.withRegions_wr, imm_toNat (by omega_arith)]) (by rw [hsp]; exact Nat.le_trans hstk hs.spk) (hs.alSp hsp) (hs.alS4 m.a_f) ?_
    (hs.kE m.pf hstk hsp) ?_ (hs.fitE m.pf (by decide)) (by rw [imm_toNat (by omega_arith)]; exact hs.fitE m.po l0)
    (by rw [imm32_toNat (by omega_arith), imm32_toNat (by omega_arith)]; exact m.hab)
    (by rw [imm_toNat (by omega_arith), imm32_toNat (by omega_arith), imm32_toNat (by omega_arith)]; exact m.hl)
    (by rw [view_glue_mem]; exact hr) ?_
  · rw [imm_toNat (by omega_arith)]; exact hs.dE m.d1 (.inr m.wo)
  · rw [imm_toNat (by omega_arith)]; exact hs.kE m.po hstk hsp
  · rw [view_glue_mem, imm32_toNat (by omega_arith), imm32_toNat (by omega_arith)]; exact hc

theorem bp_ok {c : Prog isa} (hc : Callee c (fun stk => bitPackContract RISCV64.abi stk) S) {s : State}
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
  rwa [State.withRegions_mem, g3, g4, g5, g6, g7, view_glue_mem, imm32 (by omega_arith), imm32 (by omega_arith),
    imm32_toNat (by omega_arith), imm32_toNat (by omega_arith), imm_toNat (by omega_arith)] at this

theorem bp_tr {c : Prog isa} (hc : Callee c (fun stk => bitPackContract RISCV64.abi stk) S) (hS : S ≤ STK)
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

end VG.Proof.MlDsa.RISCV64.KeyGen
