module

public import VerifiedGarbage.Impl.MlDsa.X86_64.PreparedKey
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.CallArith
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.CallPack
public import VerifiedGarbage.Proof.MlKem.X86_64.Rel
public import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
public import VerifiedGarbage.Proof.MlDsa.PreparedKeyContract
public import VerifiedGarbage.Proof.MlDsa.PreparedKey.Values
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Instrs
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.PrimsOk
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Top
public import VerifiedGarbage.Proof.MlDsa.Verify.Spec
import VerifiedGarbage.Proof.MlKem.X86_64.TopBase
import VerifiedGarbage.Proof.MlKem.X86_64.Bytes
import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Control
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Same
import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Blocks
import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.BlockTr
meta import VerifiedGarbage.Impl.MlDsa.X86_64.PreparedKey
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Sha3.X86_64.Round
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.CallArith
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.CallPack
meta import VerifiedGarbage.Proof.MlKem.X86_64.Rel
meta import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
meta import VerifiedGarbage.Proof.MlDsa.PreparedKeyContract
meta import VerifiedGarbage.Proof.MlDsa.PreparedKey.Values
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Instrs
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.PrimsOk
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Top
meta import VerifiedGarbage.Proof.MlDsa.Verify.Spec
meta import VerifiedGarbage.Proof.MlKem.X86_64.TopBase
meta import VerifiedGarbage.Proof.MlKem.X86_64.Bytes
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Control
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Same
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Blocks
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.BlockTr
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.Sha3.X86_64.Round

/-!
# ML-DSA on x86-64: preparing keys

Untrusted: everything here is checked by Lean. `prepare P len m unpack`
(`Impl/MlDsa/X86_64/PreparedKey.lean`), for any decoding `unpack i` of the
polynomials of a key that writes polynomial `i` to its slot and leaks only the
pointers: it leaves the key and, after it, the NTTs of its polynomials
(`prepare_ok`), and leaks only the pointers (`prepare_ct`). The layout: `key`
(in `rbp`) and `scratch` (in `r12`, and `r13`) read, `prepared` (in `rbx`)
written.
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Verify.Prepare

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.PreparedKey
open VG.Impl.MlKem.X86_64 (at_)
open VG.Impl.MlDsa.X86_64.Verify
open VG.Proof.MlKem.X86_64
open VG.Proof.MlDsa.Arith.Representation
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable (len size : Nat)

/-- The precondition of `prepare(key = rdi, prepared = rsi, scratch = rdx)`, with a
key of `len` bytes, `prepared` of `size` bytes, and 32 bytes of stack. -/
structure PPre (σ : State) : Prop where
  sp : 32 ≤ (σ.gpr .rsp).toNat
  rd : σ.rd = [⟨σ.gpr .rdi, len⟩]
  wr : σ.wr = [⟨σ.gpr .rsi, size⟩, ⟨σ.gpr .rdx, 1024⟩]
  d1 : Region.Disjoint ⟨σ.gpr .rdi, len⟩ ⟨σ.gpr .rsi, size⟩
  d2 : Region.Disjoint ⟨σ.gpr .rdi, len⟩ ⟨σ.gpr .rdx, 1024⟩
  d3 : Region.Disjoint ⟨σ.gpr .rsi, size⟩ ⟨σ.gpr .rdx, 1024⟩
  r1 : Region.Disjoint ⟨σ.gpr .rsp, 8⟩ ⟨σ.gpr .rdi, len⟩
  r2 : Region.Disjoint ⟨σ.gpr .rsp, 8⟩ ⟨σ.gpr .rsi, size⟩
  r3 : Region.Disjoint ⟨σ.gpr .rsp, 8⟩ ⟨σ.gpr .rdx, 1024⟩
  k1 : (below (σ.gpr .rsp) 32).Disjoint ⟨σ.gpr .rdi, len⟩
  k2 : (below (σ.gpr .rsp) 32).Disjoint ⟨σ.gpr .rsi, size⟩
  k3 : (below (σ.gpr .rsp) 32).Disjoint ⟨σ.gpr .rdx, 1024⟩
  n1 : (σ.gpr .rdi).toNat + len ≤ 2 ^ 64
  n2 : (σ.gpr .rsi).toNat + size ≤ 2 ^ 64
  n3 : (σ.gpr .rdx).toNat + 1024 ≤ 2 ^ 64

/-- The public data: the pointers. -/
def PPub (σ₁ σ₂ : State) : Prop :=
  σ₁.gpr .rdi = σ₂.gpr .rdi ∧ σ₁.gpr .rsi = σ₂.gpr .rsi ∧ σ₁.gpr .rdx = σ₂.gpr .rdx ∧ σ₁.gpr .rsp = σ₂.gpr .rsp

/-- `key` and `scratch`, read. -/
abbrev pR : List (Reg × Nat) := [(.rbp, len), (.r12, 1024)]
/-- `prepared`, written. -/
abbrev pW : List (Reg × Nat) := [(.rbx, size)]

end

/-- The register saved at `scratch + 840 + 8k`. -/
abbrev savedReg (k : Nat) : Reg := savedRegs.getD k .rbx

/-- What holds throughout a run from `σ`. -/
structure PI (len : Nat) (σ s : State) : Prop where
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  rsp : s.gpr .rsp = σ.gpr .rsp
  rbx : s.gpr .rbx = σ.gpr .rsi
  rbp : s.gpr .rbp = σ.gpr .rdi
  r12 : s.gpr .r12 = σ.gpr .rdx
  r13 : s.gpr .r13 = σ.gpr .rdx
  saved : ∀ k < 6, s.mem.readW (pa s (.r12, oSV + 8 * k)) 64 = σ.gpr (savedReg k)
  ret : s.mem.readW (σ.gpr .rsp) 64 = σ.mem.readW (σ.gpr .rsp) 64
  key : bytesAt s.mem (pa s (.rbp, 0)) len = bytesAt σ.mem (σ.gpr .rdi) len

section
variable {len size : Nat} {σ : State} (hp : PPre len size σ) (hl : len < 2 ^ 31 ∧ size < 2 ^ 31)
include hp hl

theorem PI.lay {s : State} (h : PI len σ s) : Lay (pR len) (pW size) s := by
  refine ⟨fun b hb => ?_, fun b hb b' hb' hne hw => ?_, fun b hb => ?_, fun b hb => ?_, fun b hb => ?_,
    fun b hb => ?_, fun b hb => ?_, fun b hb => ?_, by rw [h.rsp]; exact hp.sp⟩
  · simp only [pR, pW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> simp only <;> omega
  · simp only [pR, pW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb hb'
    rcases hb with rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl <;>
      simp only [wRegs, List.mem_singleton, ne_eq, not_true_eq_false, reduceCtorEq, or_self] at hne hw <;>
      simp only [h.rbx, h.rbp, h.r12]
    exacts [hp.d1, hp.d3.symm, hp.d1.symm, hp.d3]
  · simp only [pR, pW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> simp only [h.rbx, h.rbp, h.r12, h.rsp]
    exacts [hp.k1, hp.k3, hp.k2]
  · simp only [pR, pW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> simp only [h.rbx, h.rbp, h.r12]
    exacts [hp.n1, hp.n3, hp.n2]
  · simp only [pR, pW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> simp only [h.rbx, h.rbp, h.r12] <;>
      exact ⟨_, by rw [h.rd, h.wr, hp.rd, hp.wr]; simp, Region.contains_self _ _⟩
  · simp only [pW, List.mem_singleton] at hb
    subst hb
    exact ⟨_, by rw [h.wr, hp.wr, h.rbx]; simp, Region.contains_self _ _⟩
  · simp only [pR, pW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> simp only [h.rbx, h.rbp, h.r12, h.rsp]
    exacts [hp.r1, hp.r3, hp.r2]
  · simp only [pR, pW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> simp only [bases, List.mem_cons, true_or, or_true]

end

/-- A piece that writes `ws` within `prepared` keeps `PI`. -/
def piChk (len size : Nat) (ws : List (Ptr × Nat)) : Bool :=
  (List.range 6).all (fun k => keepB (pR len ++ pW size) ws (.r12, oSV + 8 * k) 8) &&
    ws.all (fun w => inB (pR len ++ pW size) w.1 w.2) && keepB (pR len ++ pW size) ws (.rbp, 0) len

theorem PI.step {len size : Nat} {σ : State} (hp : PPre len size σ) (hl : len < 2 ^ 31 ∧ size < 2 ^ 31)
    {s s' : State} (h : PI len σ s) {ws : List (Ptr × Nat)} (hP : PPostB s s' ws) (hc : piChk len size ws = true) :
    PI len σ s' := by
  have L := h.lay hp hl
  simp only [piChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨hsv, hin⟩, hkey⟩ := hc
  refine ⟨hP.rd.trans h.rd, hP.wr.trans h.wr, hP.rsp.trans h.rsp, (hP.bs .rbx (by decide)).trans h.rbx,
    (hP.bs .rbp (by decide)).trans h.rbp, (hP.bs .r12 (by decide)).trans h.r12, (hP.bs .r13 (by decide)).trans h.r13,
    fun k hk => ?_, ?_, by rw [L.keepBytes hP hkey]; exact h.key⟩
  · rw [L.keepW hP (hsv k hk)]; exact h.saved k hk
  · have := L.keepRet hP hin
    rw [h.rsp] at this
    rw [this, h.ret]


/-! ## The prologue and the epilogue -/

theorem pro_eq : Impl.MlDsa.X86_64.PreparedKey.pro = [.store (at_ .rdx 840) .rbx, .store (at_ .rdx 848) .rbp, .store (at_ .rdx 856) .r12,
    .store (at_ .rdx 864) .r13, .store (at_ .rdx 872) .r14, .store (at_ .rdx 880) .r15, .mov .rbx (.reg .rsi),
    .mov .rbp (.reg .rdi), .mov .r12 (.reg .rdx), .mov .r13 (.reg .rdx)] := rfl

theorem pro_ok {len size : Nat} {σ : State} (hp : PPre len size σ) : WP isa (.block Impl.MlDsa.X86_64.PreparedKey.pro) σ (PI len σ) := by
  have hS : ⟨σ.gpr .rdx, 1024⟩ ∈ σ.wr := by rw [hp.wr]; simp
  have c : ∀ o, o + 8 ≤ 1024 → (⟨σ.gpr .rdx, 1024⟩ : Region).Contains (σ.gpr .rdx + BitVec.ofNat 64 o) 8 :=
    fun o ho => contains_offset' ho (by decide)
  have w : ∀ o, o + 8 ≤ 1024 → InRegions σ.wr (σ.gpr .rdx + BitVec.ofNat 64 o) 8 := fun o ho => ⟨_, hS, c o ho⟩
  have w0 := w 840 (by omega); have w1 := w 848 (by omega); have w2 := w 856 (by omega)
  have w3 := w 864 (by omega); have w4 := w 872 (by omega); have w5 := w 880 (by omega)
  rw [pro_eq]
  refine WP.mono (Proof.MlKem.X86_64.WP.keep [.rbx, .rbp, .r12, .r13] (Q := fun s =>
    s.mem = (((((σ.mem.writeW (σ.gpr .rdx + BitVec.ofNat 64 840) (σ.gpr .rbx)).writeW
      (σ.gpr .rdx + BitVec.ofNat 64 848) (σ.gpr .rbp)).writeW (σ.gpr .rdx + BitVec.ofNat 64 856) (σ.gpr .r12)).writeW
      (σ.gpr .rdx + BitVec.ofNat 64 864) (σ.gpr .r13)).writeW (σ.gpr .rdx + BitVec.ofNat 64 872) (σ.gpr .r14)).writeW
      (σ.gpr .rdx + BitVec.ofNat 64 880) (σ.gpr .r15) ∧
    s.gpr .rbx = σ.gpr .rsi ∧ s.gpr .rbp = σ.gpr .rdi ∧ s.gpr .r12 = σ.gpr .rdx ∧ s.gpr .r13 = σ.gpr .rdx)
    (by xrun [w0, w1, w2, w3, w4, w5]) (by decide)) fun s ⟨⟨hm, hbx, hbp, h12, h13⟩, k⟩ => ?_
  have hf : Frame [⟨σ.gpr .rdx, 1024⟩] σ.mem s.mem := by
    rw [hm]
    exact (((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 840 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 848 (by omega))).writeW (List.mem_singleton_self _) _ (c 856 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 864 (by omega))).writeW (List.mem_singleton_self _) _ (c 872 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 880 (by omega)))
  refine ⟨k.2.1, k.2.2, k.gpr (by decide), hbx, hbp, h12, h13, fun j hj => ?_, ?_, ?_⟩
  · simp only [pa, h12, hm]
    exact Proof.MlKem.X86_64.stores_read σ.mem (σ.gpr .rdx) (fun j => σ.gpr (savedReg j)) j hj
  · exact hf.readW (Region.contains_self _ _) (by simpa using hp.r3) (by decide)
  · rw [pa, hbp, BitVec.add_zero]
    exact Proof.MlKem.bytesAt_frame hf (by simpa using hp.d2) (by have := hp.n1; omega)

theorem epi_eq : Impl.MlDsa.X86_64.PreparedKey.epi = [.mov .rbx (.mem (at_ .r12 840)), .mov .rbp (.mem (at_ .r12 848)),
    .mov .r13 (.mem (at_ .r12 864)), .mov .r14 (.mem (at_ .r12 872)), .mov .r15 (.mem (at_ .r12 880)),
    .mov .r12 (.mem (at_ .r12 856))] := rfl

theorem epi_ok {len size : Nat} {σ s : State} (hp : PPre len size σ) (h : PI len σ s) :
    WP isa (.block Impl.MlDsa.X86_64.PreparedKey.epi) s fun s' => gprPreserved σ s' ∧ s'.mem = s.mem := by
  have hS : ⟨s.gpr .r12, 1024⟩ ∈ s.rd ++ s.wr := by rw [h.rd, h.wr, hp.wr, h.r12]; simp
  have i : ∀ k < 6, InRegions (s.rd ++ s.wr) (s.gpr .r12 + BitVec.ofNat 64 (840 + 8 * k)) 8 :=
    fun k hk => ⟨_, hS, contains_offset' (by omega) (by decide)⟩
  have e : ∀ k < 6, s.mem.readW (s.gpr .r12 + BitVec.ofNat 64 (840 + 8 * k)) 64 = σ.gpr (savedReg k) :=
    fun k hk => h.saved k hk
  have e0 := e 0 (by decide); have e1 := e 1 (by decide); have e2 := e 2 (by decide)
  have e3 := e 3 (by decide); have e4 := e 4 (by decide); have e5 := e 5 (by decide)
  have i0 := i 0 (by decide); have i1 := i 1 (by decide); have i2 := i 2 (by decide)
  have i3 := i 3 (by decide); have i4 := i 4 (by decide); have i5 := i 5 (by decide)
  rw [show savedReg 0 = .rbx from rfl] at e0; rw [show savedReg 1 = .rbp from rfl] at e1
  rw [show savedReg 2 = .r12 from rfl] at e2; rw [show savedReg 3 = .r13 from rfl] at e3
  rw [show savedReg 4 = .r14 from rfl] at e4; rw [show savedReg 5 = .r15 from rfl] at e5
  simp only [Nat.reduceMul, Nat.reduceAdd] at e0 e1 e2 e3 e4 e5 i0 i1 i2 i3 i4 i5
  rw [epi_eq]
  refine WP.mono (Proof.MlKem.X86_64.WP.keep [.rbx, .rbp, .r13, .r14, .r15, .r12] (Q := fun s' =>
    s'.gpr .rbx = σ.gpr .rbx ∧ s'.gpr .rbp = σ.gpr .rbp ∧ s'.gpr .r13 = σ.gpr .r13 ∧ s'.gpr .r14 = σ.gpr .r14 ∧
    s'.gpr .r15 = σ.gpr .r15 ∧ s'.gpr .r12 = σ.gpr .r12 ∧ s'.mem = s.mem)
    (by xrun [i0, i1, i2, i3, i4, i5, e0, e1, e2, e3, e4, e5]) (by decide))
    fun s' ⟨⟨hbx, hbp, h13, h14, h15, h12, hm⟩, k⟩ => ⟨⟨fun r hr => ?_, ?_⟩, hm⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hbx, hbp, by rw [k.gpr (by decide), h.rsp], h12, h13, h14, h15]
  · rw [hm]; exact h.ret

/-! ## The NTT, with its working space at `w` -/

def ipwChk (bs wbs : List (Reg × Nat)) (f w : Ptr) : Bool :=
  sepB bs f 1024 w 1024 && inB bs f 1024 && inB bs w 1024 && inB wbs f 1024 && inB wbs w 1024

abbrev ipwArgs (f w : Ptr) : List (Reg × Arg) := [(.rdi, .ptr f), (.rsi, .ptr w)]

theorem ipw_args {bs wbs : List (Reg × Nat)} (L : LayOk bs) {f w : Ptr} (hc : ipwChk bs wbs f w = true) :
    ∀ a ∈ ipwArgs f w, a.2.Ok ∧ a.1 ∈ Verify.argRegs := by
  simp only [ipwChk, Bool.and_eq_true] at hc
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok L hc.1.1.1.2, by decide⟩, ⟨ptr_ok L hc.1.1.2, by decide⟩⟩

section
variable {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay rbs wbs s) {f w : Ptr}
  (hc : ipwChk (rbs ++ wbs) wbs f w = true)
include L hc

theorem ipw_cov : Covers ([] ++ [⟨pa s f, 1024⟩, ⟨pa s w, 1024⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨pa s f, 1024⟩, ⟨pa s w, 1024⟩] s.wr := by
  simp only [ipwChk, Bool.and_eq_true] at hc
  exact ⟨Covers.right (Covers.cons (L.cW hc.1.2) (L.cW hc.2)), Covers.cons (L.cW hc.1.2) (L.cW hc.2)⟩

theorem ipw_pre {t : Poly → Poly} (hr : Reduced s.mem (pa s f)) {s1 : State} (h1 : Args (ipwArgs f w) s s1) :
    (inPlaceContract X86_64.abi (t : Poly → Poly) 16).pre
      (s1.callEntry.withRegions [] [⟨pa s f, 1024⟩, ⟨pa s w, 1024⟩]) := by
  simp only [ipwChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨c1, c2⟩, c3⟩, _⟩, _⟩ := hc
  have g1 : s1.gpr .rdi = pa s f := h1.r0
  have g2 : s1.gpr .rsi = pa s w := h1.r1
  sig_pre [inPlaceContract, inPlaceSig, X86_64.abi, VG.X86_64.argRegs]
  rw [g1, g2, h1.rsp, h1.1.2]
  exact ⟨L.sp16, rfl, L.disj c1, L.ret8 c2, L.ret8 c3, L.stk16 c2, L.stk16 c3, L.nwp c2, L.nwp c3,
    L.wreduced c2 _ hr⟩

end

theorem ipwAt_ok {t : Poly → Poly} {n : String} {c : Prog isa} (C : CalleeOk c (inPlaceContract X86_64.abi t 16))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay rbs wbs s) {f w : Ptr} (hc : ipwChk (rbs ++ wbs) wbs f w = true)
    (hr : Reduced s.mem (pa s f)) :
    WP isa (callAt n c (ipwArgs f w)) s fun s' => PPostB s s' [(f, 1024), (w, 1024)] ∧
      PolyIs s'.mem (pa s f) (t (polyAt s.mem (pa s f))) := by
  refine WP.mono (callAt_ok C.correct C.nosp C.depth (ipw_args L.ok hc)
    (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => ipw_pre L hc hr h1) (ipw_cov L hc).1 (ipw_cov L hc).2)
    fun s' ⟨hP, s1, h1, s₂, hm, _, hq⟩ => ⟨hP.b, ?_⟩
  have g1 : s1.gpr .rdi = pa s f := h1.r0
  have c2 : inB (rbs ++ wbs) f 1024 = true := by
    simp only [ipwChk, Bool.and_eq_true] at hc; exact hc.1.1.1.2
  sig_post [inPlaceContract, inPlaceSig, X86_64.abi, VG.X86_64.argRegs] at hq
  rw [g1, hm, h1.rsp, h1.1.2, L.wpolyAt c2] at hq
  exact hq

theorem ipwAt_tr {t : Poly → Poly} {n : String} {c : Prog isa} (C : CalleeOk c (inPlaceContract X86_64.abi t 16))
    {rbs wbs : List (Reg × Nat)} (hS : LayOk (rbs ++ wbs)) {f w : Ptr} (hc : ipwChk (rbs ++ wbs) wbs f w = true)
    {P : State → State → Prop}
    (hP : ∀ x y, P x y → Lay rbs wbs x ∧ Lay rbs wbs y ∧ Reduced x.mem (pa x f) ∧ Reduced y.mem (pa y f) ∧ SameB x y) :
    RelCT isa P (callAt n c (ipwArgs f w)) fun _ _ => True := by
  refine callAt_tr C.correct C.ct (ipw_args hS hc) (by simp only [List.map_cons, List.map_nil]; decide) ?_
  · intro x y x1 y1 hp h1 h2
    obtain ⟨Lx, Ly, rx, ry, e⟩ := hP x y hp
    refine ⟨_, _, _, _, ipw_pre Lx hc rx h1, ipw_pre Ly hc ry h2, ?_, (ipw_cov Lx hc).1, (ipw_cov Lx hc).2,
      (ipw_cov Ly hc).1, (ipw_cov Ly hc).2, e.2⟩
    simp only [ipwChk, Bool.and_eq_true] at hc
    have hb : f.1 ∈ bases := ptr_bs hS hc.1.1.1.2
    have hw : w.1 ∈ bases := ptr_bs hS hc.1.1.2
    sig_pub [inPlaceContract, inPlaceSig, X86_64.abi, VG.X86_64.argRegs]
    rw [h1.r0, h2.r0, h1.r1, h2.r1, h1.rsp, h2.rsp]
    exact ⟨by rw [e.2], by simp only [Arg.val]; rw [e.pa hb], by simp only [Arg.val]; rw [e.pa hw]⟩


/-! ## The polynomials, then the copy -/

/-- The key of a run from `σ`. -/
abbrev key (len : Nat) (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rdi) len

/-- The writes of the decoding of polynomial `i`, and of its NTT. -/
abbrev uWs (len i : Nat) : List (Ptr × Nat) := [(slot len i, 1024)]
abbrev nWs (len i : Nat) : List (Ptr × Nat) := [(slot len i, 1024), ((.rbx, 0), 1024)]
abbrev cWs (len : Nat) : List (Ptr × Nat) := [((.rbx, 0), len)]

/-- What the proof needs of the numbers `len`, `size` and `m`, which the
kernel evaluates for each instance. -/
def prepChk (len size m : Nat) : Bool :=
  decide (len < 2 ^ 31) && decide (size < 2 ^ 31) && decide (0 < len) && decide (len % 8 = 0) &&
  (List.range m).all (fun i =>
    piChk len size (uWs len i) && piChk len size (nWs len i) &&
    ipwChk (pR len ++ pW size) (pW size) (slot len i) (.rbx, 0) &&
    (List.range i).all fun j => keepB (pR len ++ pW size) (uWs len i) (slot len j) 1024 &&
      keepB (pR len ++ pW size) (nWs len i) (slot len j) 1024) &&
  inB (pR len ++ pW size) (.rbp, 0) len && inB (pW size) (.rbx, 0) len &&
  sepB (pR len ++ pW size) (.rbp, 0) len (.rbx, 0) len && piChk len size (cWs len) &&
  (List.range m).all (fun j => keepB (pR len ++ pW size) (cWs len) (slot len j) 1024)

/-- After the first `i` polynomials. -/
def LI (len : Nat) (val : List Byte → Nat → Poly) (σ : State) (i : Nat) (s : State) : Prop :=
  PI len σ s ∧ ∀ j < i, PolyIs s.mem (pa s (slot len j)) (ntt (val (key len σ) j))

/-- After the first `i` polynomials and the decoding of polynomial `i`. -/
def LU (len : Nat) (val : List Byte → Nat → Poly) (σ : State) (i : Nat) (s : State) : Prop :=
  PI len σ s ∧ (∀ j < i, PolyIs s.mem (pa s (slot len j)) (ntt (val (key len σ) j))) ∧
    PolyIs s.mem (pa s (slot len i)) (val (key len σ) i)

section
variable {P : Prims} (C : CalleeOk P.ntt (inPlaceContract X86_64.abi ntt 16)) {len size m : Nat}
  {U : Nat → Prog isa} {val : List Byte → Nat → Poly}
  (hU : ∀ i < m, ∀ s, Lay (pR len) (pW size) s → WP isa (U i) s fun s' => PPostB s s' (uWs len i) ∧
    PolyIs s'.mem (pa s (slot len i)) (val (bytesAt s.mem (pa s (.rbp, 0)) len) i))
  {σ : State} (hp : PPre len size σ) (hc : prepChk len size m = true)

theorem prepChk_spec (hc : prepChk len size m = true) :
    (len < 2 ^ 31 ∧ size < 2 ^ 31 ∧ 0 < len ∧ len % 8 = 0) ∧
    (∀ i < m, piChk len size (uWs len i) = true ∧ piChk len size (nWs len i) = true ∧
      ipwChk (pR len ++ pW size) (pW size) (slot len i) (.rbx, 0) = true ∧
      ∀ j < i, keepB (pR len ++ pW size) (uWs len i) (slot len j) 1024 = true ∧
        keepB (pR len ++ pW size) (nWs len i) (slot len j) 1024 = true) ∧
    inB (pR len ++ pW size) (.rbp, 0) len = true ∧ inB (pW size) (.rbx, 0) len = true ∧
    sepB (pR len ++ pW size) (.rbp, 0) len (.rbx, 0) len = true ∧ piChk len size (cWs len) = true ∧
    ∀ j < m, keepB (pR len ++ pW size) (cWs len) (slot len j) 1024 = true := by
  simp only [prepChk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := hc
  exact ⟨⟨h1, h2, h3, h4⟩, fun i hi => ⟨(h5 i hi).1.1.1, (h5 i hi).1.1.2, (h5 i hi).1.2,
    fun j hj => (h5 i hi).2 j hj⟩, h6, h7, h8, h9, h10⟩

include C hU hp hc

omit C in
theorem unpack_ok {i : Nat} (hi : i < m) {s : State} (h : LI len val σ i s) :
    WP isa (U i) s (LU len val σ i) := by
  obtain ⟨⟨hl1, hl2, -, -⟩, hk, -⟩ := prepChk_spec hc
  have hl : len < 2 ^ 31 ∧ size < 2 ^ 31 := ⟨hl1, hl2⟩
  obtain ⟨cu, -, -, ck⟩ := hk i hi
  have L := h.1.lay hp hl
  refine WP.mono (hU i hi s L) fun s1 ⟨hP1, hq1⟩ => ⟨h.1.step hp hl hP1 cu,
    fun j hj => L.keepPoly hP1 (ck j hj).1 (h.2 j hj), ?_⟩
  rw [hP1.pa (p := slot len i) (show Reg.rbx ∈ bases by decide)]
  rw [h.1.key] at hq1
  exact hq1

omit hU in
theorem ntt_ok {i : Nat} (hi : i < m) {s : State} (h : LU len val σ i s) :
    WP isa (Impl.MlDsa.X86_64.PreparedKey.nttAt P (slot len i)) s (LI len val σ (i + 1)) := by
  obtain ⟨⟨hl1, hl2, -, -⟩, hk, -⟩ := prepChk_spec hc
  have hl : len < 2 ^ 31 ∧ size < 2 ^ 31 := ⟨hl1, hl2⟩
  obtain ⟨-, cn, ci, ck⟩ := hk i hi
  have L := h.1.lay hp hl
  refine WP.mono (ipwAt_ok C L ci h.2.2.1) fun s2 ⟨hP2, hq2⟩ => ⟨h.1.step hp hl hP2 cn, fun j hj => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
  · exact L.keepPoly hP2 (ck j hj).2 (h.2.1 j hj)
  · rw [hP2.pa (p := slot len j) (show Reg.rbx ∈ bases by decide)]
    rw [h.2.2.2] at hq2
    exact hq2

theorem poly_ok {i : Nat} (hi : i < m) {s : State} (h : LI len val σ i s) :
    WP isa (.seq (U i) (Impl.MlDsa.X86_64.PreparedKey.nttAt P (slot len i))) s (LI len val σ (i + 1)) :=
  WP.seq (WP.mono (unpack_ok hU hp hc hi h) fun _ h1 => ntt_ok C hp hc hi h1)

theorem polys_ok {s : State} (h : LI len val σ 0 s) :
    WP isa (seqR (fun i => .seq (U i) (Impl.MlDsa.X86_64.PreparedKey.nttAt P (slot len i))) 0 m) s (LI len val σ m) := by
  simpa only [Nat.zero_add] using seqR_ok (I := LI len val σ) m 0
    (fun i _ hi s h => poly_ok C hU hp hc (by omega) h) s h

omit C hU in
theorem copy_ok' {s : State} (h : LI len val σ m s) :
    WP isa (Impl.MlDsa.X86_64.Sign.copy (.rbx, 0) (.rbp, 0) len) s fun s' => LI len val σ m s' ∧
      bytesAt s'.mem (pa s (.rbx, 0)) len = key len σ := by
  obtain ⟨⟨hl1, hl2, h0, h8⟩, -, cr, cw, cs, cp, ck⟩ := prepChk_spec hc
  have hl : len < 2 ^ 31 ∧ size < 2 ^ 31 := ⟨hl1, hl2⟩
  have L := h.1.lay hp hl
  refine WP.mono (VG.Proof.MlDsa.X86_64.Sign.copy_ok (.rbx, 0) (.rbp, 0) len ⟨h0, h8⟩ hl1 (by decide) (by decide)
    (by decide) s (L.inR cr) (L.inW cw) (L.disj cs)) fun s' ⟨hb, hfr, k⟩ => ?_
  have hP : PPostB s s' (cWs len) := postB_of_keep k (by decide) (by simpa using hfr)
  exact ⟨⟨h.1.step hp hl hP cp, fun j hj => L.keepPoly hP (ck j hj) (h.2 j hj)⟩, by rw [hb, h.1.key]⟩

/-- `prepare`: the key, and after it the NTTs of its polynomials. -/
theorem prepare_ok :
    WP isa (prepare P len m U) σ fun s' => gprPreserved σ s' ∧ bytesAt s'.mem (σ.gpr .rsi) len = key len σ ∧
      ∀ j < m, PolyIs s'.mem (σ.gpr .rsi + BitVec.ofNat 64 (len + 1024 * j)) (ntt (val (key len σ) j)) := by
  unfold prepare
  refine WP.seq (WP.mono (pro_ok hp) fun s0 h0 => ?_)
  refine WP.seq (WP.mono (polys_ok C hU hp hc ⟨h0, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (copy_ok' hp hc h1) fun s2 ⟨h2, hb⟩ => ?_)
  refine WP.mono (epi_ok hp h2.1) fun s3 ⟨hg, hm⟩ => ⟨hg, ?_, fun j hj => ?_⟩
  · rw [hm, ← hb, show pa s1 (.rbx, 0) = σ.gpr .rsi by simp [pa, h1.1.rbx]]
  · have := h2.2 j hj
    rw [pa, h2.1.rbx] at this
    rw [hm]; exact this

end


/-! ## Constant time -/

/-- Two runs, each from a state satisfying `PPre`, with the same pointers. -/
abbrev RP (len size : Nat) (I : State → State → Prop) : State → State → Prop := Rel2 (PPre len size) PPub I

theorem PI.sameB {len : Nat} {σ₁ σ₂ x y : State} (pub : PPub σ₁ σ₂) (h₁ : PI len σ₁ x) (h₂ : PI len σ₂ y) :
    SameB x y := by
  refine ⟨fun r hr => ?_, by rw [h₁.rsp, h₂.rsp, pub.2.2.2]⟩
  simp only [bases, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h₁.rbx, h₂.rbx, pub.2.1]
  · rw [h₁.rbp, h₂.rbp, pub.1]
  · rw [h₁.r12, h₂.r12, pub.2.2.1]
  · rw [h₁.r13, h₂.r13, pub.2.2.1]

theorem pro_tr {len size : Nat} : RelCT isa (RP len size fun σ s => s = σ) (.block Impl.MlDsa.X86_64.PreparedKey.pro)
    fun _ _ => True :=
  taintRel [.rsi, .rdi, .rdx] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ r hr => by
    subst h₁ h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [pub.2.1, pub.1, pub.2.2.1]) (by taint_decide)

theorem epi_tr {len size : Nat} {I : State → State → Prop} (hI : ∀ σ s, I σ s → PI len σ s) :
    RelCT isa (RP len size I) (.block Impl.MlDsa.X86_64.PreparedKey.epi) fun _ _ => True :=
  taintRel [.r12] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [(hI _ _ h₁).r12, (hI _ _ h₂).r12, pub.2.2.1]) (by taint_decide)

theorem layOk {len size : Nat} (hl : len < 2 ^ 31 ∧ size < 2 ^ 31) : LayOk (pR len ++ pW size) := by
  intro b hb
  simp only [pR, pW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl <;> exact ⟨by simp only; omega, by simp [bases]⟩

section
variable {P : Prims} (C : CalleeOk P.ntt (inPlaceContract X86_64.abi ntt 16)) {len size m : Nat}
  {U : Nat → Prog isa} {val : List Byte → Nat → Poly}
  (hU : ∀ i < m, ∀ s, Lay (pR len) (pW size) s → WP isa (U i) s fun s' => PPostB s s' (uWs len i) ∧
    PolyIs s'.mem (pa s (slot len i)) (val (bytesAt s.mem (pa s (.rbp, 0)) len) i))
  (hUt : ∀ i < m, ∀ Q : State → State → Prop,
    (∀ x y, Q x y → Lay (pR len) (pW size) x ∧ Lay (pR len) (pW size) y ∧ SameB x y) →
    RelCT isa Q (U i) fun _ _ => True)
  (hc : prepChk len size m = true)
include C hU hUt hc

theorem poly_tr {i : Nat} (hi : i < m) :
    RelCT isa (RP len size fun σ s => LI len val σ i s) (.seq (U i) (Impl.MlDsa.X86_64.PreparedKey.nttAt P (slot len i)))
      (RP len size fun σ s => LI len val σ (i + 1) s) := by
  obtain ⟨⟨hl1, hl2, -, -⟩, hk, -⟩ := prepChk_spec hc
  have hl : len < 2 ^ 31 ∧ size < 2 ^ 31 := ⟨hl1, hl2⟩
  obtain ⟨-, -, ci, -⟩ := hk i hi
  refine RelCT.seq (relInv (I' := fun σ s => LU len val σ i s) (fun σ s hp h => unpack_ok hU hp hc hi h)
    (hUt i hi _ fun x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ =>
      ⟨h₁.1.lay p₁ hl, h₂.1.lay p₂ hl, h₁.1.sameB pub h₂.1⟩))
    (relInv (fun σ s hp h => ntt_ok C hp hc hi h)
      (ipwAt_tr C (layOk hl) ci fun x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ =>
        ⟨h₁.1.lay p₁ hl, h₂.1.lay p₂ hl, h₁.2.2.1, h₂.2.2.1, h₁.1.sameB pub h₂.1⟩))

theorem prepare_ct : ConstantTime isa (PPre len size) PPub (prepare P len m U) := by
  obtain ⟨⟨hl1, -, h0, h8⟩, -⟩ := prepChk_spec hc
  unfold prepare
  refine relStart (RelCT.seq (relInv (I' := fun σ s => LI len val σ 0 s) (fun σ s hp hs => by
      subst hs; exact WP.mono (pro_ok hp) fun s h => ⟨h, fun _ h => absurd h (Nat.not_lt_zero _)⟩) pro_tr)
    (RelCT.seq (seqR_tr (R := fun i => RP len size fun σ s => LI len val σ i s) m 0 fun k _ hk => poly_tr C hU hUt hc (by omega))
    (RelCT.seq (relInv (I' := fun σ s => LI len val σ m s) (fun σ s hp h => WP.mono (copy_ok' hp hc (by rw [Nat.zero_add] at h; exact h)) fun _ h => h.1)
      (Sign.copy_tr ⟨h0, h8⟩ hl1 (by decide) (by decide) (by decide) fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ =>
        ⟨by rw [h₁.1.rbx, h₂.1.rbx, pub.2.1], by rw [h₁.1.rbp, h₂.1.rbp, pub.1]⟩))
      (epi_tr fun _ _ h => h.1))))

end


/-! ## The two functions -/

/-- `t₁[i] · 2ᵈ` of the public key `pk`. -/
abbrev pubVal (pk : List Byte) (i : Nat) : Poly :=
  (VG.Proof.MlDsa.Verify.vT1 pk i).map fun c => ofInt (c * 2 ^ d : Nat)

/-- Polynomial `i` of `s₁ ‖ s₂ ‖ t₀` of the private key `sk`, in `R_q`. -/
abbrev secVal (p : Params) (sk : List Byte) (i : Nat) : Poly :=
  toRq (bitUnpack ((sk.drop (secretPiece p i).1).take (secretPiece p i).2.1) (secretPiece p i).2.2.1
    (secretPiece p i).2.2.2)

/-- What the proof of `preparePublic` needs of the parameter set. -/
def pubChk (p : Params) : Bool :=
  prepChk p.pkLen (preparedPublicKeyBytes p) p.k &&
    (List.range p.k).all fun i => t1Chk (pR p.pkLen ++ pW (preparedPublicKeyBytes p)) (pW (preparedPublicKeyBytes p))
      (.rbp, 32 + 320 * i) (slot p.pkLen i) && decide (32 + 320 * i + 320 ≤ p.pkLen)

/-- What the proof of `prepareSecret` needs of the parameter set. -/
def secChk (p : Params) : Bool :=
  prepChk p.skLen (preparedSecretKeyBytes p) (p.ℓ + 2 * p.k) &&
    (List.range (p.ℓ + 2 * p.k)).all fun i =>
      decide (((secretPiece p i).2.2.1, (secretPiece p i).2.2.2) ∈ bitPackParams) &&
      decide ((secretPiece p i).2.1 = 32 * bitlen ((secretPiece p i).2.2.1 + (secretPiece p i).2.2.2)) &&
      buChk (pR p.skLen ++ pW (preparedSecretKeyBytes p)) (pW (preparedSecretKeyBytes p)) (.rbp, (secretPiece p i).1)
        (secretPiece p i).2.1 (slot p.skLen i) &&
      decide ((secretPiece p i).1 + (secretPiece p i).2.1 ≤ p.skLen)

theorem pubChk_all : ∀ p ∈ params, pubChk p = true := by decide +kernel

theorem secChk_all : ∀ p ∈ params, secChk p = true := by decide +kernel

theorem key_slice {s : State} {len off l : Nat} (h : off + l ≤ len) :
    bytesAt s.mem (pa s (.rbp, off)) l = ((bytesAt s.mem (pa s (.rbp, 0)) len).drop off).take l := by
  rw [pa, pa, BitVec.add_zero, Proof.MlKem.bytesAt_slice _ _ h]

section
variable {P : Prims} (C : PrimsOk P) {p : Params} (hp : p ∈ params)
include C hp

theorem pub_unpack : ∀ i < p.k, ∀ s, Lay (pR p.pkLen) (pW (preparedPublicKeyBytes p)) s →
    WP isa (publicUnpack P p i) s fun s' => PPostB s s' (uWs p.pkLen i) ∧
      PolyIs s'.mem (pa s (slot p.pkLen i)) (pubVal (bytesAt s.mem (pa s (.rbp, 0)) p.pkLen) i) := by
  intro i hi s L
  have hc := pubChk_all p hp
  simp only [pubChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨c1, c2⟩ := hc.2 i hi
  refine WP.mono (unpackT1At_ok C.unpackT1 L c1) fun s' ⟨hP, _, hq⟩ => ⟨hP, ?_⟩
  rw [key_slice c2] at hq
  exact hq

theorem pub_unpack_tr : ∀ i < p.k, ∀ Q : State → State → Prop,
    (∀ x y, Q x y → Lay (pR p.pkLen) (pW (preparedPublicKeyBytes p)) x ∧
      Lay (pR p.pkLen) (pW (preparedPublicKeyBytes p)) y ∧ SameB x y) →
    RelCT isa Q (publicUnpack P p i) fun _ _ => True := by
  intro i hi Q hQ
  have hc := pubChk_all p hp
  simp only [pubChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  have hl := (prepChk_spec hc.1).1
  exact unpackT1At_tr C.unpackT1 (layOk ⟨hl.1, hl.2.1⟩) (hc.2 i hi).1 hQ

theorem sec_unpack : ∀ i < p.ℓ + 2 * p.k, ∀ s, Lay (pR p.skLen) (pW (preparedSecretKeyBytes p)) s →
    WP isa (secretUnpack P p i) s fun s' => PPostB s s' (uWs p.skLen i) ∧
      PolyIs s'.mem (pa s (slot p.skLen i)) (secVal p (bytesAt s.mem (pa s (.rbp, 0)) p.skLen) i) := by
  intro i hi s L
  have hc := secChk_all p hp
  simp only [secChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨c1, c2⟩, c3⟩, c4⟩ := hc.2 i hi
  refine WP.mono (bitUnpackAt_ok C.bitUnpack L c1 c2 c3) fun s' ⟨hP, _, hq⟩ => ⟨hP, ?_⟩
  rw [key_slice c4] at hq
  exact hq

theorem sec_unpack_tr : ∀ i < p.ℓ + 2 * p.k, ∀ Q : State → State → Prop,
    (∀ x y, Q x y → Lay (pR p.skLen) (pW (preparedSecretKeyBytes p)) x ∧
      Lay (pR p.skLen) (pW (preparedSecretKeyBytes p)) y ∧ SameB x y) →
    RelCT isa Q (secretUnpack P p i) fun _ _ => True := by
  intro i hi Q hQ
  have hc := secChk_all p hp
  simp only [secChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  have hl := (prepChk_spec hc.1).1
  obtain ⟨⟨⟨c1, c2⟩, c3⟩, _⟩ := hc.2 i hi
  exact bitUnpackAt_tr C.bitUnpack (layOk ⟨hl.1, hl.2.1⟩) c1 c2 c3 hQ

end


theorem secret_value (p : Params) (key : List Byte) {i : Nat} (hi : i < p.ℓ + 2 * p.k) :
    ntt (secVal p key i) = (preparedSecretPolys p key)[i]! := by
  have hlen : secretLen p = VG.Proof.MlDsa.Sign.lenS p := rfl
  by_cases h1 : i < p.ℓ
  · rw [PreparedKey.secret_s1 p key h1]
    simp only [secVal, secretPiece, ite_eq_left (show i < p.ℓ + p.k by omega), hlen]
    rfl
  · by_cases h2 : i < p.ℓ + p.k
    · have hj : i - p.ℓ < p.k := by omega
      have he : p.ℓ + (i - p.ℓ) = i := by omega
      rw [← he, PreparedKey.secret_s2 p key hj]
      simp only [secVal, secretPiece, ite_eq_left (show p.ℓ + (i - p.ℓ) < p.ℓ + p.k by omega), hlen]
      unfold VG.Proof.MlDsa.Sign.s2F
      rw [Nat.mul_add]
      congr 5 <;> omega
    · have hj : i - (p.ℓ + p.k) < p.k := by omega
      have he : p.ℓ + p.k + (i - (p.ℓ + p.k)) = i := by omega
      rw [← he, PreparedKey.secret_t0 p key hj]
      simp only [secVal, secretPiece, ite_eq_right (show ¬ p.ℓ + p.k + (i - (p.ℓ + p.k)) < p.ℓ + p.k by omega), hlen]
      unfold VG.Proof.MlDsa.Sign.t0F
      have hoff : 128 + VG.Proof.MlDsa.Sign.lenS p * (p.ℓ + p.k) +
          416 * (p.ℓ + p.k + (i - (p.ℓ + p.k)) - p.ℓ - p.k) =
          128 + VG.Proof.MlDsa.Sign.lenS p * p.ℓ + VG.Proof.MlDsa.Sign.lenS p * p.k +
            32 * d * (i - (p.ℓ + p.k)) := by
        rw [Nat.mul_add]
        simp only [d]
        omega
      rw [hoff]
      rfl

/-! ## The contracts -/

/-- The contract the proof of `preparePublic` is written against. -/
def pubK (p : Params) : Contract isa where
  pre := PPre p.pkLen (preparedPublicKeyBytes p)
  post σ s := bytesAt s.mem (σ.gpr .rsi) p.pkLen = bytesAt σ.mem (σ.gpr .rdi) p.pkLen ∧
    PreparedPublicKey p s.mem (σ.gpr .rsi)
  pub := PPub

/-- The contract the proof of `prepareSecret` is written against. -/
def secK (p : Params) : Contract isa where
  pre := PPre p.skLen (preparedSecretKeyBytes p)
  post σ s := bytesAt s.mem (σ.gpr .rsi) p.skLen = bytesAt σ.mem (σ.gpr .rdi) p.skLen ∧
    PreparedSecretKey p s.mem (σ.gpr .rsi)
  pub := PPub

theorem n_mul (i : Nat) : 4 * n * i = 1024 * i := by rw [show 4 * n = 1024 from rfl]

/-! ## Properties of every instruction -/

section
variable {P : Prims} {len m : Nat} {U U0 : Nat → Prog isa}

theorem prepare_q {q : Instr → Bool} (hn : P.ntt.allInstrs q = true) (hU : ∀ k, SameQ q (U k) (U0 k)) :
    SameQ q (prepare P len m U) (prepare P0 len m U0) :=
  SameQ.seq rfl ((SameQ.seqR (fun k => (hU k).seq (SameQ.call hn _)) _ _).seq rfl)

theorem prepare_c (hn : ctlOk P.ntt = true) (hU : ∀ k, SameC (U k) (U0 k)) :
    SameC (prepare P len m U) (prepare P0 len m U0) :=
  SameC.seq rfl ((SameC.seqR (fun k => (hU k).seq (SameC.call hn _)) _ _).seq rfl)

end

theorem pub0_sp : ∀ p ∈ params, (preparePublic P0 p).allInstrs (fun i => !isa.writesSp i) = true := by
  decide +kernel
theorem sec0_sp : ∀ p ∈ params, (prepareSecret P0 p).allInstrs (fun i => !isa.writesSp i) = true := by
  decide +kernel
theorem pub0_ctlC : ∀ p ∈ params, ctlC (preparePublic P0 p) = true := by decide +kernel
theorem sec0_ctlC : ∀ p ∈ params, ctlC (prepareSecret P0 p) = true := by decide +kernel

section
variable {P : Prims} (C : PrimsOk P) {p : Params} (hp : p ∈ params)
include C hp

theorem preparePublic_spSafe : (preparePublic P p).all (fun i => !isa.writesSp i) = true :=
  Code.all_of_allInstrs ((prepare_q (Code.allInstrs_of_all C.ntt.spSafe)
    (fun _ => SameQ.call (Code.allInstrs_of_all C.unpackT1.spSafe) _)).trans (pub0_sp p hp))

theorem prepareSecret_spSafe : (prepareSecret P p).all (fun i => !isa.writesSp i) = true :=
  Code.all_of_allInstrs ((prepare_q (Code.allInstrs_of_all C.ntt.spSafe)
    (fun _ => SameQ.call (Code.allInstrs_of_all C.bitUnpack.spSafe) _)).trans (sec0_sp p hp))

theorem preparePublic_ctl : ctlOk (preparePublic P p) = true :=
  ctlOk_of_ctlC ((prepare_c C.ntt.ctl (fun _ => SameC.call C.unpackT1.ctl _)).trans (pub0_ctlC p hp))

theorem prepareSecret_ctl : ctlOk (prepareSecret P p) = true :=
  ctlOk_of_ctlC ((prepare_c C.ntt.ctl (fun _ => SameC.call C.bitUnpack.ctl _)).trans (sec0_ctlC p hp))

/-! ## Correctness and constant time -/

theorem preparePublic_correct (σ : State) (hpre : (pubK p).pre σ) :
    ∃ t s', Exec isa (preparePublic P p) σ t s' ∧ abiPreserved σ s' ∧ (pubK p).post σ s' := by
  have hc := pubChk_all p hp
  simp only [pubChk, Bool.and_eq_true] at hc
  obtain ⟨t, s', he, hg, hb, hpol⟩ := prepare_ok (val := pubVal) C.ntt (pub_unpack C hp) hpre hc.1
  refine ⟨t, s', he, abiPreserved_of_ctl (preparePublic_ctl C hp) he hg, hb, fun i hi => ?_⟩
  rw [polyStored_iff, hb, n_mul, PreparedKey.public_poly p _ hi]
  exact hpol i hi

theorem prepareSecret_correct (σ : State) (hpre : (secK p).pre σ) :
    ∃ t s', Exec isa (prepareSecret P p) σ t s' ∧ abiPreserved σ s' ∧ (secK p).post σ s' := by
  have hc := secChk_all p hp
  simp only [secChk, Bool.and_eq_true] at hc
  obtain ⟨t, s', he, hg, hb, hpol⟩ := prepare_ok (val := secVal p) C.ntt (sec_unpack C hp) hpre hc.1
  refine ⟨t, s', he, abiPreserved_of_ctl (prepareSecret_ctl C hp) he hg, hb, fun i hi => ?_⟩
  rw [polyStored_iff, hb, n_mul, ← secret_value p _ hi]
  exact hpol i hi

theorem preparePublic_ct : ConstantTime isa (pubK p).pre (pubK p).pub (preparePublic P p) := by
  have hc := pubChk_all p hp
  simp only [pubChk, Bool.and_eq_true] at hc
  exact prepare_ct (val := pubVal) C.ntt (pub_unpack C hp) (pub_unpack_tr C hp) hc.1

theorem prepareSecret_ct : ConstantTime isa (secK p).pre (secK p).pub (prepareSecret P p) := by
  have hc := secChk_all p hp
  simp only [secChk, Bool.and_eq_true] at hc
  exact prepare_ct (val := secVal p) C.ntt (sec_unpack C hp) (sec_unpack_tr C hp) hc.1

end


/-! ## The shared contracts -/

/-- A state satisfying the preconditions of the contracts. -/
def prepSat (len size : Nat) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x4000 | .rdx => 0x20000 | .rsp => 0x80000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, len⟩]
  wr := [⟨0x4000, size⟩, ⟨0x20000, 1024⟩]

theorem pubK_implies {p : Params} (hp : p ∈ params) :
    (pubK p).Implies (preparePublicKeyContract p X86_64.abi 32) where
  pre s h := by
    sig_pre [preparePublicKeyContract, preparePublicKeySig, X86_64.abi, VG.X86_64.argRegs] at h
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩ := h
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩
  post s s' _ h := by
    sig_post [preparePublicKeyContract, preparePublicKeySig, X86_64.abi, VG.X86_64.argRegs]
    exact h
  pub s₁ s₂ _ _ h := by
    sig_pub [preparePublicKeyContract, preparePublicKeySig, X86_64.abi, VG.X86_64.argRegs] at h
    obtain ⟨hsp, hdi, hsi, hdx⟩ := h
    exact ⟨hdi, hsi, hdx, hsp⟩
  sat := by
    simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · sig_implies_sat [preparePublicKeyContract, preparePublicKeySig, X86_64.abi, VG.X86_64.argRegs]
        [prepSat] using prepSat mlDsa44.pkLen (preparedPublicKeyBytes mlDsa44)
    · sig_implies_sat [preparePublicKeyContract, preparePublicKeySig, X86_64.abi, VG.X86_64.argRegs]
        [prepSat] using prepSat mlDsa65.pkLen (preparedPublicKeyBytes mlDsa65)
    · sig_implies_sat [preparePublicKeyContract, preparePublicKeySig, X86_64.abi, VG.X86_64.argRegs]
        [prepSat] using prepSat mlDsa87.pkLen (preparedPublicKeyBytes mlDsa87)

theorem secK_implies {p : Params} (hp : p ∈ params) :
    (secK p).Implies (prepareSecretKeyContract p X86_64.abi 32) where
  pre s h := by
    sig_pre [prepareSecretKeyContract, prepareSecretKeySig, X86_64.abi, VG.X86_64.argRegs] at h
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩ := h
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩
  post s s' _ h := by
    sig_post [prepareSecretKeyContract, prepareSecretKeySig, X86_64.abi, VG.X86_64.argRegs]
    exact h
  pub s₁ s₂ _ _ h := by
    sig_pub [prepareSecretKeyContract, prepareSecretKeySig, X86_64.abi, VG.X86_64.argRegs] at h
    obtain ⟨hsp, hdi, hsi, hdx⟩ := h
    exact ⟨hdi, hsi, hdx, hsp⟩
  sat := by
    simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · sig_implies_sat [prepareSecretKeyContract, prepareSecretKeySig, X86_64.abi, VG.X86_64.argRegs]
        [prepSat] using prepSat mlDsa44.skLen (preparedSecretKeyBytes mlDsa44)
    · sig_implies_sat [prepareSecretKeyContract, prepareSecretKeySig, X86_64.abi, VG.X86_64.argRegs]
        [prepSat] using prepSat mlDsa65.skLen (preparedSecretKeyBytes mlDsa65)
    · sig_implies_sat [prepareSecretKeyContract, prepareSecretKeySig, X86_64.abi, VG.X86_64.argRegs]
        [prepSat] using prepSat mlDsa87.skLen (preparedSecretKeyBytes mlDsa87)

theorem preparePublic_verified {P : Prims} (C : PrimsOk P) {p : Params} (hp : p ∈ params) :
    Verified X86_64.target (preparePublic P p) (preparePublicKeyContract p X86_64.abi 32) :=
  Verified.of_correct (preparePublic_correct C hp) (preparePublic_ct C hp) (pubK_implies hp)

theorem prepareSecret_verified {P : Prims} (C : PrimsOk P) {p : Params} (hp : p ∈ params) :
    Verified X86_64.target (prepareSecret P p) (prepareSecretKeyContract p X86_64.abi 32) :=
  Verified.of_correct (prepareSecret_correct C hp) (prepareSecret_ct C hp) (secK_implies hp)

end VG.Proof.MlDsa.X86_64.Verify.Prepare
