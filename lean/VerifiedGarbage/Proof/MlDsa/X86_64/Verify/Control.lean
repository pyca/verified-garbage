module

public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Flag
import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.HashCT
import VerifiedGarbage.Proof.MlKem.X86_64.Rel
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MlDsa.Arith.Representation
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Entry
import VerifiedGarbage.Proof.Sha3.X86_64.Round

/-! ### `MlDsa.X86_64.Verify.CallArith`, which the modules that import this one used -/

section

/-!
# ML-DSA verification on x86-64: calls of the arithmetic primitives

For each call of `vg_mldsa_ntt`, `vg_mldsa_inv_ntt` (`ipAt`),
`vg_mldsa_multiply_ntt`, `vg_mldsa_multiply_add_ntt` and `vg_mldsa_sub`: what
it needs of the layout (a check evaluated on the pointers, `…Chk`), what it
does (`…_ok`), and that two runs whose layout registers agree leak the same
(`…_tr`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Verify

open VG.Proof.MlDsa.Arith.Representation
variable {mont : Bool}

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Proof.MlKem.X86_64
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

def ipChk (bs : List (Reg × Nat)) (wbs : List (Reg × Nat)) (f : Ptr) : Bool :=
  sepB bs f 1024 (sc oSS) 1024 && inB bs f 1024 && inB bs (sc oSS) 1024 && inB wbs f 1024 && inB wbs (sc oSS) 1024

abbrev ipArgs (f : Ptr) : List (Reg × Arg) := [(.rdi, .ptr f), (.rsi, .ptr (sc oSS))]

theorem ip_args {bs wbs : List (Reg × Nat)} (L : LayOk bs) {f : Ptr} (hc : ipChk bs wbs f = true) :
    ∀ a ∈ ipArgs f, a.2.Ok ∧ a.1 ∈ argRegs := by
  simp only [ipChk, Bool.and_eq_true] at hc
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok L hc.1.1.1.2, by decide⟩, ⟨ptr_ok L hc.1.1.2, by decide⟩⟩

section
variable {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay rbs wbs s) {f : Ptr}
  (hc : ipChk (rbs ++ wbs) wbs f = true)
include L hc

theorem ip_cov : Covers ([] ++ [⟨pa s f, 1024⟩, ⟨pa s (sc oSS), 1024⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨pa s f, 1024⟩, ⟨pa s (sc oSS), 1024⟩] s.wr := by
  simp only [ipChk, Bool.and_eq_true] at hc
  exact ⟨Covers.right (Covers.cons (L.cW hc.1.2) (L.cW hc.2)), Covers.cons (L.cW hc.1.2) (L.cW hc.2)⟩

theorem ip_pre {t : Poly → Poly} (hr : Reduced s.mem (pa s f)) {s1 : State} (h1 : Args (ipArgs f) s s1) :
    (inPlaceContract X86_64.abi (t : Poly → Poly) 16).pre
      (s1.callEntry.withRegions [] [⟨pa s f, 1024⟩, ⟨pa s (sc oSS), 1024⟩]) := by
  simp only [ipChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨c1, c2⟩, c3⟩, _⟩, _⟩ := hc
  have g1 : s1.gpr .rdi = pa s f := h1.r0
  have g2 : s1.gpr .rsi = pa s (sc oSS) := h1.r1
  sig_pre [inPlaceContract, inPlaceSig, X86_64.abi, VG.X86_64.argRegs]
  rw [g1, g2, h1.rsp, h1.1.2]
  exact ⟨L.sp16, rfl, L.disj c1, L.ret8 c2, L.ret8 c3, L.stk16 c2, L.stk16 c3, L.nwp c2, L.nwp c3,
    L.wreduced c2 _ hr⟩

end

theorem ipAt_ok {t : Poly → Poly} {n : String} {c : Prog isa} (C : CalleeOk c (inPlaceContract X86_64.abi t 16))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay rbs wbs s) {f : Ptr} (hc : ipChk (rbs ++ wbs) wbs f = true)
    (hr : Reduced s.mem (pa s f)) :
    WP isa (callAt n c (ipArgs f)) s fun s' => PPostB s s' [(f, 1024), (sc oSS, 1024)] ∧ s'.gpr .r15 = s.gpr .r15 ∧
      PolyIs s'.mem (pa s f) (t (polyAt s.mem (pa s f))) := by
  refine WP.mono (callAt_ok C.correct C.nosp C.depth (ip_args L.ok hc) (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => ip_pre L hc hr h1) (ip_cov L hc).1 (ip_cov L hc).2)
    fun s' ⟨hP, s1, h1, s₂, hm, _, hq⟩ => ⟨hP.b, hP.cs .r15 (by decide), ?_⟩
  have g1 : s1.gpr .rdi = pa s f := h1.r0
  have c2 : inB (rbs ++ wbs) f 1024 = true := by
    simp only [ipChk, Bool.and_eq_true] at hc; exact hc.1.1.1.2
  sig_post [inPlaceContract, inPlaceSig, X86_64.abi, VG.X86_64.argRegs] at hq
  rw [g1, hm, h1.rsp, h1.1.2, L.wpolyAt c2] at hq
  exact hq

theorem ipAt_tr {t : Poly → Poly} {n : String} {c : Prog isa} (C : CalleeOk c (inPlaceContract X86_64.abi t 16))
    {rbs wbs : List (Reg × Nat)} (hS : LayOk (rbs ++ wbs)) {f : Ptr} (hc : ipChk (rbs ++ wbs) wbs f = true)
    {P : State → State → Prop}
    (hP : ∀ x y, P x y → Lay rbs wbs x ∧ Lay rbs wbs y ∧ Reduced x.mem (pa x f) ∧ Reduced y.mem (pa y f) ∧ SameB x y) :
    RelCT isa P (callAt n c (ipArgs f)) fun _ _ => True := by
  refine callAt_tr C.okMx (C.ctMx fun _ _ h => h) (ip_args hS hc) (by simp only [List.map_cons, List.map_nil]; decide) ?_
  · intro x y x1 y1 hp h1 h2
    obtain ⟨Lx, Ly, rx, ry, e⟩ := hP x y hp
    refine ⟨_, _, _, _, ip_pre (t := t) Lx hc rx h1, ip_pre (t := t) Ly hc ry h2, ?_, (ip_cov Lx hc).1, (ip_cov Lx hc).2,
      (ip_cov Ly hc).1, (ip_cov Ly hc).2, e.2⟩
    have hb : f.1 ∈ bases := by
      simp only [ipChk, Bool.and_eq_true] at hc; exact ptr_bs hS hc.1.1.1.2
    sig_pub [Contract.mxFree, inPlaceContract, inPlaceSig, X86_64.abi, VG.X86_64.argRegs]
    rw [h1.r0, h2.r0, h1.r1,
      h2.r1, h1.rsp, h2.rsp]
    exact ⟨by rw [e.2], by simp only [Arg.val]; rw [e.pa hb], by simp only [Arg.val]; rw [e.pa (by decide)]⟩


/-! ## Products -/

def mulChk (bs wbs : List (Reg × Nat)) (h f g : Ptr) : Bool :=
  sepB bs h 1024 f 1024 && sepB bs h 1024 g 1024 && inB bs h 1024 && inB bs f 1024 && inB bs g 1024 &&
    inB wbs h 1024

abbrev mulArgs (h f g : Ptr) : List (Reg × Arg) := [(.rdi, .ptr h), (.rsi, .ptr f), (.rdx, .ptr g)]

theorem mul_args {bs wbs : List (Reg × Nat)} (L : LayOk bs) {h f g : Ptr} (hc : mulChk bs wbs h f g = true) :
    ∀ a ∈ mulArgs h f g, a.2.Ok ∧ a.1 ∈ argRegs := by
  simp only [mulChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨_, c3⟩, c4⟩, c5⟩, _⟩ := hc
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok L c3, by decide⟩, ⟨ptr_ok L c4, by decide⟩, ⟨ptr_ok L c5, by decide⟩⟩

section
variable {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay rbs wbs s) {h f g : Ptr}
  (hc : mulChk (rbs ++ wbs) wbs h f g = true)
include L hc

theorem mul_cov : Covers ([⟨pa s f, 1024⟩, ⟨pa s g, 1024⟩] ++ [⟨pa s h, 1024⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨pa s h, 1024⟩] s.wr := by
  simp only [mulChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨_, c3⟩, c4⟩, c5⟩, c6⟩ := hc
  exact ⟨Covers.append_left (Covers.cons (L.cR c4) (L.cR c5)) (L.cR c3), L.cW c6⟩

theorem mul_pre (hf : Reduced s.mem (pa s f)) (hg : Reduced s.mem (pa s g)) {s1 : State}
    (h1 : Args (mulArgs h f g) s s1) :
    (productContract mont X86_64.abi 16).pre (s1.callEntry.withRegions [⟨pa s f, 1024⟩, ⟨pa s g, 1024⟩] [⟨pa s h, 1024⟩]) := by
  simp only [mulChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, _⟩ := hc
  have g1 : s1.gpr .rdi = pa s h := h1.r0
  have g2 : s1.gpr .rsi = pa s f := h1.r1
  have g3 : s1.gpr .rdx = pa s g := h1.r2
  sig_pre [productContract, mulSig, X86_64.abi, VG.X86_64.argRegs]
  rw [g1, g2, g3, h1.rsp, h1.1.2]
  exact ⟨L.sp16, rfl, rfl, L.disj c1, L.disj c2, L.ret8 c3, L.ret8 c4, L.ret8 c5, L.stk16 c3, L.stk16 c4,
    L.stk16 c5, L.nwp c3, L.nwp c4, L.nwp c5, L.wreduced c4 _ hf, L.wreduced c5 _ hg⟩

theorem mulAdd_pre (hh : Reduced s.mem (pa s h)) (hf : Reduced s.mem (pa s f)) (hg : Reduced s.mem (pa s g))
    {s1 : State} (h1 : Args (mulArgs h f g) s s1) :
    (accumulateContract mont X86_64.abi 16).pre
      (s1.callEntry.withRegions [⟨pa s f, 1024⟩, ⟨pa s g, 1024⟩] [⟨pa s h, 1024⟩]) := by
  simp only [mulChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, _⟩ := hc
  have g1 : s1.gpr .rdi = pa s h := h1.r0
  have g2 : s1.gpr .rsi = pa s f := h1.r1
  have g3 : s1.gpr .rdx = pa s g := h1.r2
  sig_pre [accumulateContract, mulSig, X86_64.abi, VG.X86_64.argRegs]
  rw [g1, g2, g3, h1.rsp, h1.1.2]
  exact ⟨L.sp16, rfl, rfl, L.disj c1, L.disj c2, L.ret8 c3, L.ret8 c4, L.ret8 c5, L.stk16 c3, L.stk16 c4,
    L.stk16 c5, L.nwp c3, L.nwp c4, L.nwp c5, L.wreduced c3 _ hh, L.wreduced c4 _ hf, L.wreduced c5 _ hg⟩

end

theorem mulAt_ok {P : Prims} (C : CalleeOk P.mul (productContract P.montgomery X86_64.abi 16)) {rbs wbs : List (Reg × Nat)}
    {s : State} (L : Lay rbs wbs s) {h f g : Ptr} (hc : mulChk (rbs ++ wbs) wbs h f g = true)
    (hf : Reduced s.mem (pa s f)) (hg : Reduced s.mem (pa s g)) :
    WP isa (mulAt P h f g) s fun s' => PPostB s s' [(h, 1024)] ∧ s'.gpr .r15 = s.gpr .r15 ∧
      PolyIs s'.mem (pa s h) (product P.montgomery (polyAt s.mem (pa s f)) (polyAt s.mem (pa s g))) := by
  refine WP.mono (callAt_ok C.correct C.nosp C.depth (mul_args L.ok hc) (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => mul_pre L hc hf hg h1) (mul_cov L hc).1 (mul_cov L hc).2)
    fun s' ⟨hP, s1, h1, s₂, hm, _, hq⟩ => ⟨hP.b, hP.cs .r15 (by decide), ?_⟩
  simp only [mulChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨_, c4⟩, c5⟩, _⟩ := hc
  sig_post [productContract, mulSig, X86_64.abi, VG.X86_64.argRegs] at hq
  rw [h1.r0, h1.r1, h1.r2, hm, h1.rsp, h1.1.2] at hq
  simp only [Arg.val] at hq
  rw [L.wpolyAt c4, L.wpolyAt c5] at hq
  exact hq

theorem mulAddAt_ok {P : Prims} (C : CalleeOk P.mulAdd (accumulateContract P.montgomery X86_64.abi 16)) {rbs wbs : List (Reg × Nat)}
    {s : State} (L : Lay rbs wbs s) {h f g : Ptr} (hc : mulChk (rbs ++ wbs) wbs h f g = true)
    (hh : Reduced s.mem (pa s h)) (hf : Reduced s.mem (pa s f)) (hg : Reduced s.mem (pa s g)) :
    WP isa (mulAddAt P h f g) s fun s' => PPostB s s' [(h, 1024)] ∧ s'.gpr .r15 = s.gpr .r15 ∧
      PolyIs s'.mem (pa s h) (add (polyAt s.mem (pa s h)) (product P.montgomery (polyAt s.mem (pa s f)) (polyAt s.mem (pa s g)))) := by
  refine WP.mono (callAt_ok C.correct C.nosp C.depth (mul_args L.ok hc) (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => mulAdd_pre L hc hh hf hg h1) (mul_cov L hc).1 (mul_cov L hc).2)
    fun s' ⟨hP, s1, h1, s₂, hm, _, hq⟩ => ⟨hP.b, hP.cs .r15 (by decide), ?_⟩
  simp only [mulChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨_, c3⟩, c4⟩, c5⟩, _⟩ := hc
  sig_post [accumulateContract, accumulate, mulSig, X86_64.abi, VG.X86_64.argRegs] at hq
  rw [h1.r0, h1.r1, h1.r2, hm, h1.rsp, h1.1.2] at hq
  simp only [Arg.val] at hq
  rw [L.wpolyAt c3, L.wpolyAt c4, L.wpolyAt c5] at hq
  exact hq

theorem mul_pub {x y x1 y1 : State} {h f g : Ptr} (hb : h.1 ∈ bases ∧ f.1 ∈ bases ∧ g.1 ∈ bases) (e : SameB x y)
    (h1 : Args (mulArgs h f g) x x1) (h2 : Args (mulArgs h f g) y y1) :
    x1.gpr .rsp - 8 = y1.gpr .rsp - 8 ∧ x1.gpr .rdi = y1.gpr .rdi ∧ x1.gpr .rsi = y1.gpr .rsi ∧
      x1.gpr .rdx = y1.gpr .rdx := by
  rw [h1.r0, h1.r1, h1.r2, h2.r0, h2.r1, h2.r2]
  simp only [Arg.val]
  refine ⟨?_, e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2⟩
  rw [h1.rsp, h2.rsp, e.2]

theorem mulAt_tr {P : Prims} (C : CalleeOk P.mul (productContract P.montgomery X86_64.abi 16)) {rbs wbs : List (Reg × Nat)}
    (hS : LayOk (rbs ++ wbs)) {h f g : Ptr} (hc : mulChk (rbs ++ wbs) wbs h f g = true) {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay rbs wbs x ∧ Lay rbs wbs y ∧ (Reduced x.mem (pa x f) ∧ Reduced x.mem (pa x g)) ∧
      (Reduced y.mem (pa y f) ∧ Reduced y.mem (pa y g)) ∧ SameB x y) :
    RelCT isa Q (mulAt P h f g) fun _ _ => True := by
  refine callAt_tr C.okMx (C.ctMx fun _ _ h => h) (mul_args hS hc) (by simp only [List.map_cons, List.map_nil]; decide) ?_
  intro x y x1 y1 hp h1 h2
  obtain ⟨Lx, Ly, rx, ry, e⟩ := hQ x y hp
  refine ⟨_, _, _, _, mul_pre (mont := P.montgomery) Lx hc rx.1 rx.2 h1, mul_pre (mont := P.montgomery) Ly hc ry.1 ry.2 h2, ?_, (mul_cov Lx hc).1, (mul_cov Lx hc).2,
    (mul_cov Ly hc).1, (mul_cov Ly hc).2, e.2⟩
  have hc' := hc
  simp only [mulChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨_, c3⟩, c4⟩, c5⟩, _⟩ := hc'
  sig_pub [Contract.mxFree, productContract, mulSig, X86_64.abi, VG.X86_64.argRegs]
  exact mul_pub ⟨ptr_bs hS c3, ptr_bs hS c4, ptr_bs hS c5⟩ e h1 h2

theorem mulAddAt_tr {P : Prims} (C : CalleeOk P.mulAdd (accumulateContract P.montgomery X86_64.abi 16)) {rbs wbs : List (Reg × Nat)}
    (hS : LayOk (rbs ++ wbs)) {h f g : Ptr} (hc : mulChk (rbs ++ wbs) wbs h f g = true) {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay rbs wbs x ∧ Lay rbs wbs y ∧
      (Reduced x.mem (pa x h) ∧ Reduced x.mem (pa x f) ∧ Reduced x.mem (pa x g)) ∧
      (Reduced y.mem (pa y h) ∧ Reduced y.mem (pa y f) ∧ Reduced y.mem (pa y g)) ∧ SameB x y) :
    RelCT isa Q (mulAddAt P h f g) fun _ _ => True := by
  refine callAt_tr C.okMx (C.ctMx fun _ _ h => h) (mul_args hS hc) (by simp only [List.map_cons, List.map_nil]; decide) ?_
  intro x y x1 y1 hp h1 h2
  obtain ⟨Lx, Ly, rx, ry, e⟩ := hQ x y hp
  refine ⟨_, _, _, _, mulAdd_pre (mont := P.montgomery) Lx hc rx.1 rx.2.1 rx.2.2 h1, mulAdd_pre (mont := P.montgomery) Ly hc ry.1 ry.2.1 ry.2.2 h2, ?_,
    (mul_cov Lx hc).1, (mul_cov Lx hc).2, (mul_cov Ly hc).1, (mul_cov Ly hc).2, e.2⟩
  have hc' := hc
  simp only [mulChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨_, c3⟩, c4⟩, c5⟩, _⟩ := hc'
  sig_pub [Contract.mxFree, accumulateContract, mulSig, X86_64.abi, VG.X86_64.argRegs]
  exact mul_pub ⟨ptr_bs hS c3, ptr_bs hS c4, ptr_bs hS c5⟩ e h1 h2

/-! ## Subtraction -/

def subChk (bs wbs : List (Reg × Nat)) (f g : Ptr) : Bool :=
  sepB bs f 1024 g 1024 && inB bs f 1024 && inB bs g 1024 && inB wbs f 1024

abbrev subArgs (f g : Ptr) : List (Reg × Arg) := [(.rdi, .ptr f), (.rsi, .ptr g)]

theorem sub_args {bs wbs : List (Reg × Nat)} (L : LayOk bs) {f g : Ptr} (hc : subChk bs wbs f g = true) :
    ∀ a ∈ subArgs f g, a.2.Ok ∧ a.1 ∈ argRegs := by
  simp only [subChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨_, c2⟩, c3⟩, _⟩ := hc
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok L c2, by decide⟩, ⟨ptr_ok L c3, by decide⟩⟩

section
variable {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay rbs wbs s) {f g : Ptr}
  (hc : subChk (rbs ++ wbs) wbs f g = true)
include L hc

theorem sub_cov : Covers ([⟨pa s g, 1024⟩] ++ [⟨pa s f, 1024⟩]) (s.rd ++ s.wr) ∧ Covers [⟨pa s f, 1024⟩] s.wr := by
  simp only [subChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨_, c2⟩, c3⟩, c4⟩ := hc
  exact ⟨Covers.append_left (L.cR c3) (L.cR c2), L.cW c4⟩

theorem sub_pre (hf : Reduced s.mem (pa s f)) (hg : Reduced s.mem (pa s g)) {s1 : State}
    (h1 : Args (subArgs f g) s s1) :
    (subContract X86_64.abi 16).pre (s1.callEntry.withRegions [⟨pa s g, 1024⟩] [⟨pa s f, 1024⟩]) := by
  simp only [subChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨c1, c2⟩, c3⟩, _⟩ := hc
  have g1 : s1.gpr .rdi = pa s f := h1.r0
  have g2 : s1.gpr .rsi = pa s g := h1.r1
  sig_pre [subContract, accSig, X86_64.abi, VG.X86_64.argRegs]
  rw [g1, g2, h1.rsp, h1.1.2]
  exact ⟨L.sp16, rfl, rfl, L.disj c1, L.ret8 c2, L.ret8 c3, L.stk16 c2, L.stk16 c3, L.nwp c2, L.nwp c3,
    L.wreduced c2 _ hf, L.wreduced c3 _ hg⟩

end

theorem subAt_ok {P : Prims} (C : CalleeOk P.sub (subContract X86_64.abi 16)) {rbs wbs : List (Reg × Nat)}
    {s : State} (L : Lay rbs wbs s) {f g : Ptr} (hc : subChk (rbs ++ wbs) wbs f g = true)
    (hf : Reduced s.mem (pa s f)) (hg : Reduced s.mem (pa s g)) :
    WP isa (subAt P f g) s fun s' => PPostB s s' [(f, 1024)] ∧ s'.gpr .r15 = s.gpr .r15 ∧
      PolyIs s'.mem (pa s f) (sub (polyAt s.mem (pa s f)) (polyAt s.mem (pa s g))) := by
  refine WP.mono (callAt_ok C.correct C.nosp C.depth (sub_args L.ok hc) (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => sub_pre L hc hf hg h1) (sub_cov L hc).1 (sub_cov L hc).2)
    fun s' ⟨hP, s1, h1, s₂, hm, _, hq⟩ => ⟨hP.b, hP.cs .r15 (by decide), ?_⟩
  simp only [subChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨_, c2⟩, c3⟩, _⟩ := hc
  sig_post [subContract, accSig, X86_64.abi, VG.X86_64.argRegs] at hq
  rw [h1.r0, h1.r1, hm, h1.rsp, h1.1.2] at hq
  simp only [Arg.val] at hq
  rw [L.wpolyAt c2, L.wpolyAt c3] at hq
  exact hq

theorem subAt_tr {P : Prims} (C : CalleeOk P.sub (subContract X86_64.abi 16)) {rbs wbs : List (Reg × Nat)}
    (hS : LayOk (rbs ++ wbs)) {f g : Ptr} (hc : subChk (rbs ++ wbs) wbs f g = true) {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay rbs wbs x ∧ Lay rbs wbs y ∧ (Reduced x.mem (pa x f) ∧ Reduced x.mem (pa x g)) ∧
      (Reduced y.mem (pa y f) ∧ Reduced y.mem (pa y g)) ∧ SameB x y) :
    RelCT isa Q (subAt P f g) fun _ _ => True := by
  refine callAt_tr C.okMx (C.ctMx fun _ _ h => h) (sub_args hS hc) (by simp only [List.map_cons, List.map_nil]; decide) ?_
  intro x y x1 y1 hp h1 h2
  obtain ⟨Lx, Ly, rx, ry, e⟩ := hQ x y hp
  refine ⟨_, _, _, _, sub_pre Lx hc rx.1 rx.2 h1, sub_pre Ly hc ry.1 ry.2 h2, ?_, (sub_cov Lx hc).1, (sub_cov Lx hc).2,
    (sub_cov Ly hc).1, (sub_cov Ly hc).2, e.2⟩
  have hc' := hc
  simp only [subChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨_, c2⟩, c3⟩, _⟩ := hc'
  sig_pub [Contract.mxFree, subContract, accSig, X86_64.abi, VG.X86_64.argRegs]
  rw [h1.r0, h1.r1, h2.r0, h2.r1, h1.rsp, h2.rsp, e.2]
  simp only [Arg.val]
  exact ⟨trivial, e.pa (ptr_bs hS c2), e.pa (ptr_bs hS c3)⟩

end VG.Proof.MlDsa.X86_64.Verify

end

end

/-!
# ML-DSA verification on x86-64: branches, sequences and the comparison

The branch on the result in `r15` (`ifOk_ok`, `ifOk_tr`), sequences of pieces
indexed by a number (`seqR_ok`, `seqR_tr`), and the comparison of `c̃′` with
`c̃` without a branch (`cmpAnd_ok`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Impl.MlKem.X86_64 (at_)
open VG.Proof.MlKem.X86_64
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## The branch on `r15` -/

theorem test15_ok (s : State) :
    WP isa (.block [.alu32 .test .r15 (.reg .r15)]) s fun s₁ => PPostB s s₁ [] ∧ s₁.gpr .r15 = s.gpr .r15 ∧
      s₁.zf = some ((s.gpr .r15).setWidth 32 == 0) :=
  WP.mono (WP.keep [.r15] (Q := fun s₁ => s₁.mem = s.mem ∧ s₁.gpr .r15 = s.gpr .r15 ∧
      s₁.zf = some (((s.gpr .r15).setWidth 32 &&& (s.gpr .r15).setWidth 32) == 0)) (by xrun) (by decide))
    fun _ ⟨⟨hm, h15, hz⟩, k⟩ => ⟨postB_of_keep k (by decide) (by rw [hm]; exact Frame.refl _ _), h15,
      by rw [hz, BitVec.and_self]⟩

theorem flag_sw (p : Prop) [Decidable p] : ((flag p).setWidth 32 == 0) = !decide p := by
  unfold flag; by_cases h : p <;> simp [h]

theorem ifOk_ok {c : Prog isa} {s : State} {Q : State → Prop} {p : Prop} [Decidable p] (h15 : s.gpr .r15 = flag p)
    (ht : ∀ s₁, PPostB s s₁ [] → s₁.gpr .r15 = s.gpr .r15 → p → WP isa c s₁ Q)
    (he : ∀ s₁, PPostB s s₁ [] → s₁.gpr .r15 = s.gpr .r15 → ¬ p → Q s₁) : WP isa (ifOk c) s Q := by
  unfold ifOk
  refine WP.seq (WP.mono (test15_ok s) fun s₁ ⟨hP, h15', hz⟩ => ?_)
  rw [h15, flag_sw] at hz
  refine WP.ite (M := isa) (decide p) (show s₁.zf.map (!·) = _ by rw [hz]; simp) (fun hb => ?_) fun hb => ?_
  · exact ht s₁ hP h15' (by simpa using hb)
  · exact WP.block_nil (he s₁ hP h15' (by simpa using hb))

theorem ifOk_tr {c : Prog isa} {P Q : State → State → Prop}
    (he : ∀ x y, P x y → (x.gpr .r15).setWidth 32 = (y.gpr .r15).setWidth 32)
    (ht : RelCT isa (fun x y => ∃ x₀ y₀, P x₀ y₀ ∧ PPostB x₀ x [] ∧ PPostB y₀ y [] ∧
      x.gpr .r15 = x₀.gpr .r15 ∧ y.gpr .r15 = y₀.gpr .r15 ∧ (x₀.gpr .r15).setWidth 32 ≠ 0) c Q)
    (hq : ∀ x y, (∃ x₀ y₀, P x₀ y₀ ∧ PPostB x₀ x [] ∧ PPostB y₀ y [] ∧
      x.gpr .r15 = x₀.gpr .r15 ∧ y.gpr .r15 = y₀.gpr .r15 ∧ (x₀.gpr .r15).setWidth 32 = 0) → Q x y) :
    RelCT isa P (ifOk c) Q := by
  unfold ifOk
  refine RelCT.seq (RelCT.postDep (block_nomem_tr fun i hi s => by
      simp only [List.mem_singleton] at hi; subst hi; rfl)
    (F := fun x x₁ => PPostB x x₁ [] ∧ x₁.gpr .r15 = x.gpr .r15 ∧ x₁.zf = some ((x.gpr .r15).setWidth 32 == 0))
    (fun x y _ => ⟨test15_ok x, test15_ok y⟩) (Q := fun x₁ y₁ => ∃ x₀ y₀, P x₀ y₀ ∧
      (PPostB x₀ x₁ [] ∧ x₁.gpr .r15 = x₀.gpr .r15 ∧ x₁.zf = some ((x₀.gpr .r15).setWidth 32 == 0)) ∧
      (PPostB y₀ y₁ [] ∧ y₁.gpr .r15 = y₀.gpr .r15 ∧ y₁.zf = some ((y₀.gpr .r15).setWidth 32 == 0)))
    fun x y _ _ hp h1 h2 => ⟨x, y, hp, h1, h2⟩) (RelCT.ite ?_ ?_ ?_)
  · rintro x₁ y₁ ⟨x₀, y₀, hp, ⟨_, _, hx⟩, ⟨_, _, hy⟩⟩
    show x₁.zf.map (!·) = y₁.zf.map (!·)
    rw [hx, hy, he x₀ y₀ hp]
  · refine RelCT.mono ht (fun x₁ y₁ ⟨⟨x₀, y₀, hp, ⟨h1, e1, hx⟩, ⟨h2, e2, _⟩⟩, hc⟩ =>
      ⟨x₀, y₀, hp, h1, h2, e1, e2, ?_⟩) fun _ _ h => h
    have hc' : x₁.zf.map (!·) = some true := hc
    rw [hx] at hc'
    simpa using hc'
  · refine RelCT.mono nil_tr (fun x₁ y₁ ⟨⟨x₀, y₀, hp, ⟨h1, e1, hx⟩, ⟨h2, e2, _⟩⟩, hc⟩ =>
      ⟨x₀, y₀, hp, h1, h2, e1, e2, ?_⟩) fun x y h => hq x y h
    have hc' : x₁.zf.map (!·) = some false := hc
    rw [hx] at hc'
    simpa using hc'

/-! ## Sequences -/

theorem seqR_ok {f : Nat → Prog isa} {I : Nat → State → Prop} :
    ∀ (n a : Nat), (∀ k, a ≤ k → k < a + n → ∀ s, I k s → WP isa (f k) s (I (k + 1))) →
      ∀ s, I a s → WP isa (seqR f a n) s (I (a + n))
  | 0, a, _, s, hs => WP.block_nil hs
  | n + 1, a, h, s, hs => by
    rw [seqR]
    refine WP.seq (WP.mono (h a (Nat.le_refl _) (by omega_using []) s hs) fun s₁ h₁ => ?_)
    rw [show a + (n + 1) = a + 1 + n by omega_using []]
    exact seqR_ok n (a + 1) (fun k hk hk' => h k (by omega_using [hk]) (by omega_using [hk'])) s₁ h₁

theorem seqR_tr {f : Nat → Prog isa} {R : Nat → State → State → Prop} :
    ∀ (n a : Nat), (∀ k, a ≤ k → k < a + n → RelCT isa (R k) (f k) (R (k + 1))) →
      RelCT isa (R a) (seqR f a n) (R (a + n))
  | 0, _, _ => nil_tr
  | n + 1, a, h => by
    rw [seqR, show a + (n + 1) = a + 1 + n by omega_using []]
    exact RelCT.seq (h a (Nat.le_refl _) (by omega_using [])) (seqR_tr n (a + 1) fun k hk hk' => h k (by omega_using [hk]) (by omega_using [hk']))


/-! ## The comparison -/

theorem sbb_val (x r : BitVec 64) :
    BitVec.setWidth 64 (BitVec.setWidth 32 r &&&
      BitVec.setWidth 32 (0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide (x.toNat < (1 : BitVec 64).toNat))))) =
    if x = 0 then BitVec.setWidth 64 (BitVec.setWidth 32 r) else 0 := by
  by_cases h : x = 0
  · subst h
    rw [ifp rfl, show decide ((0 : BitVec 64).toNat < (1 : BitVec 64).toNat) = true by decide,
      show BitVec.setWidth 32 (0#64 - BitVec.setWidth 64 (BitVec.ofBool true)) = BitVec.allOnes 32 by decide,
      BitVec.and_allOnes]
  · rw [ifn h, show decide (x.toNat < (1 : BitVec 64).toNat) = false by
      simp only [decide_eq_false_iff_not]; intro h'; exact h (BitVec.eq_of_toNat_eq (by simp at h' ⊢; omega_using [h']))]
    apply BitVec.eq_of_toNat_eq; simp

theorem cmpEnd_ok (s : State) :
    WP isa (.block (([.alu .sub .rdx (.imm 1), .alu .sbb .rax (.reg .rax)] : List Instr) ++ and15)) s fun s' =>
      (s'.gpr .r15 = (if s.gpr .rdx = 0 then BitVec.setWidth 64 ((s.gpr .r15).setWidth 32) else 0) ∧
        s'.mem = s.mem) ∧ Keep [.rdx, .rax, .r15] s s' := by
  refine WP.keep _ ?_ (Proof.MlKem.X86_64.writesOnly_of (by decide))
  unfold and15
  xrun [List.cons_append, List.nil_append]
  exact sbb_val _ _



theorem cmpBody_ok (s : State) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 1)
    (h1 : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 1) :
    WP isa cmpBody s fun s' =>
      (s'.gpr .rdx = s.gpr .rdx ||| (BitVec.setWidth 64 (s.mem (s.gpr .rsi)) ^^^ BitVec.setWidth 64 (s.mem (s.gpr .rdi))) ∧
        s'.gpr .rsi = s.gpr .rsi + 1 ∧ s'.gpr .rdi = s.gpr .rdi + 1 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
        s'.zf = some (s.gpr .rcx - 1 == 0) ∧ s'.mem = s.mem) ∧ Keep [.rax, .r8, .rdx, .rsi, .rdi, .rcx] s s' := by
  refine WP.keep _ ?_ (Proof.MlKem.X86_64.writesOnly_of (by decide))
  unfold cmpBody
  xrun [h0, h1]

theorem or_xor_zero {d : BitVec 64} {x y : Byte} :
    (d ||| (BitVec.setWidth 64 x ^^^ BitVec.setWidth 64 y) = 0) ↔ d = 0 ∧ x = y := by
  rw [show (0 : BitVec 64) = 0#64 from rfl, BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff]
  refine and_congr Iff.rfl ⟨fun h => ?_, fun h => h ▸ rfl⟩
  apply BitVec.eq_of_toNat_eq
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_setWidth] at this
  have hx := x.isLt; have hy := y.isLt
  rwa [Nat.mod_eq_of_lt (by omega_using []), Nat.mod_eq_of_lt (by omega_using [])] at this

/-- `r15 ← 0` unless the `n` bytes at `a` and `b` are equal. -/
theorem cmpAnd_ok {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay rbs wbs s) {a b : Ptr} {n : Nat} (hn : 0 < n)
    (ha : inB (rbs ++ wbs) a n = true) (hb : inB (rbs ++ wbs) b n = true) {P : Prop} [Decidable P]
    (h15 : s.gpr .r15 = flag P) :
    WP isa (cmpAnd a b n) s fun s' => PPostB s s' [] ∧
      s'.gpr .r15 = flag (P ∧ bytesAt s.mem (pa s a) n = bytesAt s.mem (pa s b) n) := by
  have hS := L.ok
  have hn' : n < 2 ^ 31 := by obtain ⟨m, hm, hl⟩ := inB_spec ha; have := (hS _ hm).1; omega
  have hok : ∀ x ∈ ([(.rsi, .ptr a), (.rdi, .ptr b), (.rcx, .imm n)] : List (Reg × Arg)),
      x.2.Ok ∧ x.1 ∈ argRegs := by
    simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    exact ⟨⟨ptr_ok hS ha, by decide⟩, ⟨ptr_ok hS hb, by decide⟩, ⟨hn', by decide⟩⟩
  have ra := L.inR ha
  have rb := L.inR hb
  unfold cmpAnd
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (glue_ok' hok (by simp only [List.map_cons, List.map_nil]; decide) s) fun s1 h1 => ?_
  refine WP.mono (WP.keep [.rdx] (Q := fun s₂ => s₂.mem = s1.mem ∧ s₂.gpr .rdx = 0) (by xrun) (Proof.MlKem.X86_64.writesOnly_of (by decide)))
    fun s2 ⟨⟨hm2, hd2⟩, k2⟩ => ?_
  have k12 : Keep argRegs s s2 := (h1.2.trans k2).mono (by simp)
  have hm12 : s2.mem = s.mem := hm2.trans h1.1.2
  have ea : s2.gpr .rsi = pa s a := by rw [k2.gpr (by decide)]; exact h1.1.1 _ (List.mem_cons_self ..)
  have eb : s2.gpr .rdi = pa s b := by
    rw [k2.gpr (by decide)]; exact h1.1.1 _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have ec : s2.gpr .rcx = BitVec.ofNat 64 n := by
    rw [k2.gpr (by decide)]
    exact h1.1.1 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  refine WP.seq (WP.mono (wp_countdown (cnt := .rcx) (N := n) (by omega_using [hn']) hn (fun k s' =>
      s'.gpr .rsi = pa s a + BitVec.ofNat 64 k ∧ s'.gpr .rdi = pa s b + BitVec.ofNat 64 k ∧ s'.mem = s.mem ∧
      (s'.gpr .rdx = 0 ↔ ∀ j < k, s.mem (pa s a + BitVec.ofNat 64 j) = s.mem (pa s b + BitVec.ofNat 64 j)) ∧
      Keep argRegs s s')
    (fun k hk s' ⟨hsi, hdi, hm, hd, kk⟩ _ => ?_) (fun _ h => h)
    ⟨by rw [ea]; simp, by rw [eb]; simp, hm12, by rw [hd2]; simp, k12⟩ ec)
    fun s3 ⟨_, _, hm3, hd3, k3⟩ => ?_)
  · refine WP.mono (cmpBody_ok s' (by rw [kk.2.1, kk.2.2, hsi]; exact inRegions_byte ra hk (by omega_using [hn']))
      (by rw [kk.2.1, kk.2.2, hdi]; exact inRegions_byte rb hk (by omega_using [hn'])))
      fun s'' ⟨⟨hd', hsi', hdi', hcx, hz, hm'⟩, k'⟩ => ⟨⟨?_, ?_, hm'.trans hm, ?_, (kk.trans k').mono (by simp)⟩, hcx, hz⟩
    · rw [hsi', hsi, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.add_assoc, ← BitVec.ofNat_add]
    · rw [hdi', hdi, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.add_assoc, ← BitVec.ofNat_add]
    · rw [hd', or_xor_zero, hd, hsi, hdi, hm]
      constructor
      · rintro ⟨h, e⟩ j hj
        rcases (by omega_using [hj] : j < k ∨ j = k) with hj | rfl
        · exact h j hj
        · exact e
      · intro h; exact ⟨fun j hj => h j (by omega_using [hj]), h k (by omega_using [])⟩
  · refine WP.mono (cmpEnd_ok s3) fun s4 ⟨⟨h15', hm4⟩, k4⟩ => ⟨?_, ?_⟩
    · exact postB_of_keep (k3.trans k4) (by decide) (by rw [hm4, hm3]; exact Frame.refl _ _)
    · have hr15 : s3.gpr .r15 = flag P := by rw [k3.gpr (by decide), h15]
      rw [h15', hr15]
      have heq : (s3.gpr .rdx = 0) ↔ bytesAt s.mem (pa s a) n = bytesAt s.mem (pa s b) n := by
        rw [hd3]
        constructor
        · intro h; simp only [bytesAt]; exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)
        · intro h j hj
          have := congrArg (fun l => l.getD j 0) h
          rwa [Proof.MlKem.bytesAt_getD _ _ hj, Proof.MlKem.bytesAt_getD _ _ hj] at this
      by_cases hd : s3.gpr .rdx = 0
      · rw [ifp hd]
        have he := heq.mp hd
        by_cases hP : P <;> simp [flag, hP, he]
      · rw [ifn hd]
        have he : ¬ bytesAt s.mem (pa s a) n = bytesAt s.mem (pa s b) n := fun e => hd (heq.mpr e)
        simp [flag, he]

end VG.Proof.MlDsa.X86_64.Verify
