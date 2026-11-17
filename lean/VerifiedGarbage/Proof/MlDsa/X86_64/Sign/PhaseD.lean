module

public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Top
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseA
import VerifiedGarbage.Proof.MlKem.X86_64.SampleLoop
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Blocks
import VerifiedGarbage.Proof.MlDsa.PreparedKeyContract
import VerifiedGarbage.Proof.MlDsa.PreparedKey.Values
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Prims

/-! ### `MlDsa.X86_64.Sign.PrimsD`, which this module and modules that import it used -/

section

/-! ### `MlDsa.X86_64.Sign.PrimsC`, which this module and modules that import it used -/

section

/-!
# ML-DSA signing on x86-64: calls of rounding, norms, hints and packing

As `Prims.lean`, for `vg_mldsa_high_bits`, `vg_mldsa_low_bits`,
`vg_mldsa_norm_lt`, `vg_mldsa_make_hint`, `vg_mldsa_simple_bit_pack`,
`vg_mldsa_bit_pack`, `vg_mldsa_bit_unpack` and `vg_mldsa_hint_bit_pack`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable {D : Nat} {rbs wbs : List (Reg × Nat)}

/-- What a call with a polynomial `f` read and a buffer `out` of `l` bytes
written needs of the layout. -/
def rwChk (bs wbs : List (Reg × Nat)) (f : Ptr) (lf : Nat) (out : Ptr) (l : Nat) : Bool :=
  inB wbs out l && inB bs f lf && inB bs out l && sepB bs f lf out l && decide (f.1 ∈ bases) &&
    decide (f.2 < 2 ^ 31) && decide (out.1 ∈ bases) && decide (out.2 < 2 ^ 31)

theorem rwChk_spec {bs wbs : List (Reg × Nat)} {f out : Ptr} {lf l : Nat} (hc : rwChk bs wbs f lf out l = true) :
    inB wbs out l = true ∧ inB bs f lf = true ∧ inB bs out l = true ∧ sepB bs f lf out l = true ∧
      f.1 ∈ bases ∧ f.2 < 2 ^ 31 ∧ out.1 ∈ bases ∧ out.2 < 2 ^ 31 := by
  simp only [rwChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := hc
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-! ## `HighBits` and `LowBits` -/

theorem gamma2_lt {γ : Nat} (h : γ ∈ gamma2s) : γ < 2 ^ 32 := by
  simp only [gamma2s, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> decide

theorem bitsArgs_ok {bs : List (Reg × Nat)} {r out : Ptr} {γ : Nat} (hγ : γ ∈ gamma2s) (hc : rwChk bs wbs r 1024 out 1024 = true) :
    [Arg.ptr r, .imm γ, .ptr out].all Arg.ok = true := by
  obtain ⟨_, _, _, _, b1, o1, b2, o2⟩ := rwChk_spec hc
  simp only [List.all_cons, List.all_nil, Arg.ok, b1, o1, b2, o2, decide_true, Bool.and_true,
    decide_eq_true (gamma2_lt hγ)]

/-- The contract of `vg_mldsa_high_bits` or `vg_mldsa_low_bits`: `bitsSig`'s,
with the postcondition `Q`. -/
abbrev bitsC (Q : Nat → Poly → Mem → Addr → Prop) (S : Nat) : Contract isa :=
  bitsSig.contract X86_64.abi
    (pre := fun r gamma2 _out m => gamma2.toNat ∈ gamma2s ∧ Reduced m r)
    (post := fun r gamma2 out m m' _ => Q gamma2.toNat (polyAt m r) m' out)
    (writeArgs := true)
    (stack := S)

theorem bitsPre {Q : Nat → Poly → Mem → Addr → Prop} {S : Nat} (hS : S + 8 ≤ D) {s s1 : State}
    (A : At D rbs wbs s s1) {r out : Ptr} {γ : Nat} (hγ : γ ∈ gamma2s)
    (hc : rwChk (rbs ++ wbs) wbs r 1024 out 1024 = true) (hA : ArgsIn [.ptr r, .imm γ, .ptr out] s s1)
    (hr : Reduced s.mem (pa s r)) :
    (bitsC Q S).pre (s1.callEntry.withRegions [pR (pa s r)] [pR (pa s out)]) := by
  obtain ⟨_, i1, i2, d12, _⟩ := rwChk_spec hc
  obtain ⟨e1, e2, e3⟩ := argsIn3 hA
  have hD : 8 ≤ D := by omega_using [hS]
  have hwf := ce_wfS (ws := [64, 32, 64]) (by decide) hS (A.rsp ▸ A.L.sp) [pR (pa s r)] [pR (pa s out)]
  sig_pre [bitsSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [e1, e2, e3, Arg.val, sw32_ofNat (gamma2_lt hγ)]
  refine ⟨hwf, trivial, trivial, A.L.disj d12, A.ret i1 hD, ?_, A.L.nwp i1, A.L.nwp i2, hγ, A.red' i1 hD hr⟩
  refine Sig.conj_cons.mpr ⟨A.ret i2 hD, conj_stk [pR (pa s r), pR (pa s out)] ?_⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨A.stk hS i1, A.stk hS i2⟩

theorem bitsAt_ok {Q : Nat → Poly → Mem → Addr → Prop} {n : String} {c : Prog isa}
    (C : Callee (fun S => bitsC Q S) D c) {s : State} (L : Lay D rbs wbs s) {r out : Ptr} {γ : Nat}
    (hγ : γ ∈ gamma2s) (hc : rwChk (rbs ++ wbs) wbs r 1024 out 1024 = true) (hr : Reduced s.mem (pa s r)) :
    WP isa (callP n c [.ptr r, .imm γ, .ptr out]) s fun s' => PPostB D s s' [(out, 1024)] ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ Q γ (polyAt s.mem (pa s r)) s'.mem (pa s out) := by
  obtain ⟨w1, i1, i2, _, _⟩ := rwChk_spec hc
  have hD : 8 ≤ D := by have := C.hS; omega_using [this]
  refine WP.mono (callP_ok C.ver.1 C.nosp C.depth L.dsm (bitsArgs_ok hγ hc)
    (fun s1 hA hm k => bitsPre C.hS (At.of L hm k) hγ hc hA hr)
    (Covers.append_left (L.cR i1) (Covers.right (L.cW w1))) (L.cW w1))
    fun s' ⟨hpost, hcs, s1, hA, hm, k, s₂, hm₂, _, hq⟩ => ⟨hpost, hcs, ?_⟩
  have A := At.of L hm k
  obtain ⟨e1, e2, e3⟩ := argsIn3 hA
  sig_post [bitsSig, X86_64.abi, VG.X86_64.argRegs] at hq
  simp only [e1, e2, e3, Arg.val, hm₂, A.poly' i1 hD, sw32_ofNat (gamma2_lt hγ)] at hq
  exact hq

theorem bitsAt_tr {Q : Nat → Poly → Mem → Addr → Prop} {n : String} {c : Prog isa}
    (C : Callee (fun S => bitsC Q S) D c) {r out : Ptr} {γ : Nat} (hγ : γ ∈ gamma2s)
    (hc : rwChk (rbs ++ wbs) wbs r 1024 out 1024 = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧ Reduced x.mem (pa x r) ∧ Reduced y.mem (pa y r))
      (callP n c [.ptr r, .imm γ, .ptr out]) fun _ _ => True := by
  obtain ⟨w1, i1, i2, _, _⟩ := rwChk_spec hc
  refine callP_tr C.okMx (C.ctMx fun _ _ h => h) (bitsArgs_ok hγ hc)
    fun x y x1 y1 ⟨R, rx, ry⟩ ⟨⟨hAx, hmx⟩, kx⟩ ⟨⟨hAy, hmy⟩, ky⟩ =>
      ⟨_, _, _, _, bitsPre (Q := Q) C.hS (At.of R.lx hmx kx) hγ hc hAx rx, bitsPre (Q := Q) C.hS (At.of R.ly hmy ky) hγ hc hAy ry, ?_,
        by rw [kx.2.1, kx.2.2]; exact Covers.append_left (R.lx.cR i1) (Covers.right (R.lx.cW w1)),
        by rw [kx.2.2]; exact R.lx.cW w1,
        by rw [ky.2.1, ky.2.2]; exact Covers.append_left (R.ly.cR i1) (Covers.right (R.ly.cW w1)),
        by rw [ky.2.2]; exact R.ly.cW w1,
        by rw [(At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp]⟩
  obtain ⟨hx1, hx2, hx3⟩ := argsIn3 hAx
  obtain ⟨hy1, hy2, hy3⟩ := argsIn3 hAy
  sig_pub [Contract.mxFree, bitsSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hx1, hx2, hx3, hy1, hy2, hy3, Arg.val, R.pa i1, R.pa i2,
    (At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp, and_self]

theorem highBitsAt_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {r out : Ptr} {γ : Nat}
    (hγ : γ ∈ gamma2s) (hc : rwChk (rbs ++ wbs) wbs r 1024 out 1024 = true) (hr : Reduced s.mem (pa s r)) :
    WP isa (highBitsAt P r γ out) s fun s' => PPostB D s s' [(out, 1024)] ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      NatPolyIs s'.mem (pa s out) ((polyAt s.mem (pa s r)).map fun c => (highBits γ c).toNat) :=
  bitsAt_ok (Q := fun γ f m out => NatPolyIs m out (f.map fun c => (highBits γ c).toNat)) hP.highBits L hγ hc hr

theorem highBitsAt_tr {P : Prims} (hP : PrimsOk P D) {r out : Ptr} {γ : Nat} (hγ : γ ∈ gamma2s)
    (hc : rwChk (rbs ++ wbs) wbs r 1024 out 1024 = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧ Reduced x.mem (pa x r) ∧ Reduced y.mem (pa y r))
      (highBitsAt P r γ out) fun _ _ => True :=
  bitsAt_tr (Q := fun γ f m out => NatPolyIs m out (f.map fun c => (highBits γ c).toNat)) hP.highBits hγ hc

theorem lowBitsAt_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {r out : Ptr} {γ : Nat}
    (hγ : γ ∈ gamma2s) (hc : rwChk (rbs ++ wbs) wbs r 1024 out 1024 = true) (hr : Reduced s.mem (pa s r)) :
    WP isa (lowBitsAt P r γ out) s fun s' => PPostB D s s' [(out, 1024)] ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      PolyIs s'.mem (pa s out) ((polyAt s.mem (pa s r)).map fun c => ofInt (lowBits γ c)) :=
  bitsAt_ok (Q := fun γ f m out => PolyIs m out (f.map fun c => ofInt (lowBits γ c))) hP.lowBits L hγ hc hr

theorem lowBitsAt_tr {P : Prims} (hP : PrimsOk P D) {r out : Ptr} {γ : Nat} (hγ : γ ∈ gamma2s)
    (hc : rwChk (rbs ++ wbs) wbs r 1024 out 1024 = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧ Reduced x.mem (pa x r) ∧ Reduced y.mem (pa y r))
      (lowBitsAt P r γ out) fun _ _ => True :=
  bitsAt_tr (Q := fun γ f m out => PolyIs m out (f.map fun c => ofInt (lowBits γ c))) hP.lowBits hγ hc

/-! ## Norms -/

/-- What a call of `vg_mldsa_norm_lt` on `f` needs of the layout. -/
def normChk (bs : List (Reg × Nat)) (f : Ptr) : Bool :=
  inB bs f 1024 && decide (f.1 ∈ bases) && decide (f.2 < 2 ^ 31)

theorem normPre {S : Nat} (hS : S + 8 ≤ D) {s s1 : State} (A : At D rbs wbs s s1) {f : Ptr} {B : Nat}
    (hc : normChk (rbs ++ wbs) f = true) (hA : ArgsIn [.ptr f, .imm B] s s1)
    (hr : Reduced s.mem (pa s f)) :
    (normLtContract X86_64.abi S).pre (s1.callEntry.withRegions [pR (pa s f)] []) := by
  simp only [normChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨i1, _⟩, _⟩ := hc
  obtain ⟨e1, e2⟩ := argsIn2 hA
  have hD : 8 ≤ D := by omega_using [hS]
  have hwf := ce_wfS (ws := [64, 32]) (by decide) hS (A.rsp ▸ A.L.sp) [pR (pa s f)] []
  sig_pre [normLtContract, normLtSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [e1, Arg.val]
  refine ⟨hwf, trivial, ?_, A.L.nwp i1, A.red' i1 hD hr⟩
  refine Sig.conj_cons.mpr ⟨A.ret i1 hD, conj_stk [pR (pa s f)] ?_⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
  exact A.stk hS i1

theorem normArgs_ok {bs : List (Reg × Nat)} {f : Ptr} {B : Nat} (hB : B < 2 ^ 32) (hc : normChk bs f = true) :
    [Arg.ptr f, .imm B].all Arg.ok = true := by
  simp only [normChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  simp only [List.all_cons, List.all_nil, Arg.ok, hc.1.2, hc.2, decide_true, Bool.and_true, decide_eq_true hB]

theorem normCall_ok {nm : String} {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {f : Ptr} {B : Nat}
    (hB : B < 2 ^ 32) (hc : normChk (rbs ++ wbs) f = true) (hr : Reduced s.mem (pa s f)) :
    WP isa (callP nm P.normLt [.ptr f, .imm B]) s fun s' => PPostB D s s' [] ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      (s'.gpr .rax).setWidth 32 = if normRq [polyAt s.mem (pa s f)] < B then 1 else 0 := by
  have i1 : inB (rbs ++ wbs) f 1024 = true := by
    simp only [normChk, Bool.and_eq_true] at hc; exact hc.1.1
  have hD : 8 ≤ D := by have := hP.normLt.hS; omega_using [this]
  refine WP.mono (callP_ok hP.normLt.ver.1 hP.normLt.nosp hP.normLt.depth L.dsm (normArgs_ok hB hc)
    (fun s1 hA hm k => normPre hP.normLt.hS (At.of L hm k) hc hA hr)
    (Covers.append_left (L.cR i1) Covers.nil) Covers.nil)
    fun s' ⟨hpost, hcs, s1, hA, hm, k, s₂, hm₂, hg₂, hq⟩ => ⟨hpost, hcs, ?_⟩
  have A := At.of L hm k
  obtain ⟨e1, e2⟩ := argsIn2 hA
  have er : s₂.gpr .rax = s'.gpr .rax := hg₂ .rax (by decide)
  sig_post [normLtContract, normLtSig, X86_64.abi, VG.X86_64.argRegs] at hq
  simp only [e1, e2, Arg.val, er, A.poly' i1 hD, sw32_ofNat hB] at hq
  exact hq

theorem normCall_tr {nm : String} {P : Prims} (hP : PrimsOk P D) {f : Ptr} {B : Nat} (hB : B < 2 ^ 32)
    (hc : normChk (rbs ++ wbs) f = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧ Reduced x.mem (pa x f) ∧ Reduced y.mem (pa y f))
      (callP nm P.normLt [.ptr f, .imm B]) fun _ _ => True := by
  have i1 : inB (rbs ++ wbs) f 1024 = true := by
    simp only [normChk, Bool.and_eq_true] at hc; exact hc.1.1
  refine callP_tr hP.normLt.okMx (hP.normLt.ctMx fun _ _ h => h) (normArgs_ok hB hc)
    fun x y x1 y1 ⟨R, rx, ry⟩ ⟨⟨hAx, hmx⟩, kx⟩ ⟨⟨hAy, hmy⟩, ky⟩ =>
      ⟨_, _, _, _, normPre hP.normLt.hS (At.of R.lx hmx kx) hc hAx rx,
        normPre hP.normLt.hS (At.of R.ly hmy ky) hc hAy ry, ?_,
        by rw [kx.2.1, kx.2.2]; exact Covers.append_left (R.lx.cR i1) Covers.nil, Covers.nil,
        by rw [ky.2.1, ky.2.2]; exact Covers.append_left (R.ly.cR i1) Covers.nil, Covers.nil,
        by rw [(At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp]⟩
  obtain ⟨hx1, hx2⟩ := argsIn2 hAx
  obtain ⟨hy1, hy2⟩ := argsIn2 hAy
  sig_pub [Contract.mxFree, normLtContract, normLtSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hx1, hx2, hy1, hy2, Arg.val, R.pa i1, (At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp,
    and_self]

/-! ## `MakeHint` -/

/-- What a call of `vg_mldsa_make_hint` on `z`, `r` to `h` needs of the layout. -/
def hintChk (bs wbs : List (Reg × Nat)) (z r h : Ptr) : Bool :=
  inB wbs h 1024 && inB bs z 1024 && inB bs r 1024 && inB bs h 1024 && sepB bs z 1024 h 1024 &&
    sepB bs r 1024 h 1024 && decide (z.1 ∈ bases) && decide (z.2 < 2 ^ 31) && decide (r.1 ∈ bases) &&
    decide (r.2 < 2 ^ 31) && decide (h.1 ∈ bases) && decide (h.2 < 2 ^ 31)

theorem hintChk_spec {bs wbs : List (Reg × Nat)} {z r h : Ptr} (hc : hintChk bs wbs z r h = true) :
    inB wbs h 1024 = true ∧ inB bs z 1024 = true ∧ inB bs r 1024 = true ∧ inB bs h 1024 = true ∧
      sepB bs z 1024 h 1024 = true ∧ sepB bs r 1024 h 1024 = true ∧ z.1 ∈ bases ∧ z.2 < 2 ^ 31 ∧
      r.1 ∈ bases ∧ r.2 < 2 ^ 31 ∧ h.1 ∈ bases ∧ h.2 < 2 ^ 31 := by
  simp only [hintChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := hc
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

theorem hintArgs_ok {bs : List (Reg × Nat)} {z r h : Ptr} {γ : Nat} (hγ : γ ∈ gamma2s) (hc : hintChk bs wbs z r h = true) :
    [Arg.ptr z, .ptr r, .imm γ, .ptr h].all Arg.ok = true := by
  obtain ⟨_, _, _, _, _, _, b1, o1, b2, o2, b3, o3⟩ := hintChk_spec hc
  simp only [List.all_cons, List.all_nil, Arg.ok, b1, o1, b2, o2, b3, o3, decide_true, Bool.and_true,
    decide_eq_true (gamma2_lt hγ)]

theorem hintPre {S : Nat} (hS : S + 8 ≤ D) {s s1 : State} (A : At D rbs wbs s s1) {z r h : Ptr} {γ : Nat}
    (hγ : γ ∈ gamma2s) (hc : hintChk (rbs ++ wbs) wbs z r h = true)
    (hA : ArgsIn [.ptr z, .ptr r, .imm γ, .ptr h] s s1) (rz : Reduced s.mem (pa s z))
    (rr : Reduced s.mem (pa s r)) :
    (makeHintContract X86_64.abi S).pre (s1.callEntry.withRegions [pR (pa s z), pR (pa s r)] [pR (pa s h)]) := by
  obtain ⟨_, i1, i2, i3, d13, d23, _⟩ := hintChk_spec hc
  obtain ⟨e1, e2, e3, e4⟩ := argsIn4 hA
  have hD : 8 ≤ D := by omega_using [hS]
  have hwf := ce_wfS (ws := [64, 64, 32, 64]) (by decide) hS (A.rsp ▸ A.L.sp) [pR (pa s z), pR (pa s r)]
    [pR (pa s h)]
  sig_pre [makeHintContract, makeHintSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [e1, e2, e3, e4, Arg.val, sw32_ofNat (gamma2_lt hγ)]
  refine ⟨hwf, trivial, trivial, A.L.disj d13, A.L.disj d23, A.ret i1 hD, A.ret i2 hD, ?_, A.L.nwp i1, A.L.nwp i2,
    A.L.nwp i3, hγ, A.red' i1 hD rz, A.red' i2 hD rr⟩
  refine Sig.conj_cons.mpr ⟨A.ret i3 hD, conj_stk [pR (pa s z), pR (pa s r), pR (pa s h)] ?_⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨A.stk hS i1, A.stk hS i2, A.stk hS i3⟩

theorem hintCall_ok {nm : String} {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {z r h : Ptr} {γ : Nat}
    (hγ : γ ∈ gamma2s) (hc : hintChk (rbs ++ wbs) wbs z r h = true) (rz : Reduced s.mem (pa s z))
    (rr : Reduced s.mem (pa s r)) :
    WP isa (callP nm P.makeHint [.ptr z, .ptr r, .imm γ, .ptr h]) s fun s' =>
      PPostB D s s' [(h, 1024)] ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      HintIs s'.mem (pa s h) 1 [Vector.zipWith (makeHint γ) (polyAt s.mem (pa s z)) (polyAt s.mem (pa s r))] ∧
      ((s'.gpr .rax).setWidth 32).toNat =
        hintOnes [Vector.zipWith (makeHint γ) (polyAt s.mem (pa s z)) (polyAt s.mem (pa s r))] := by
  obtain ⟨w1, i1, i2, i3, _⟩ := hintChk_spec hc
  have hD : 8 ≤ D := by have := hP.makeHint.hS; omega_using [this]
  refine WP.mono (callP_ok hP.makeHint.ver.1 hP.makeHint.nosp hP.makeHint.depth L.dsm (hintArgs_ok hγ hc)
    (fun s1 hA hm k => hintPre hP.makeHint.hS (At.of L hm k) hγ hc hA rz rr)
    (Covers.append_left (Covers.cons (L.cR i1) (L.cR i2)) (Covers.right (L.cW w1))) (L.cW w1))
    fun s' ⟨hpost, hcs, s1, hA, hm, k, s₂, hm₂, hg₂, hq⟩ => ⟨hpost, hcs, ?_⟩
  have A := At.of L hm k
  obtain ⟨e1, e2, e3, e4⟩ := argsIn4 hA
  have er : s₂.gpr .rax = s'.gpr .rax := hg₂ .rax (by decide)
  sig_post [makeHintContract, makeHintSig, X86_64.abi, VG.X86_64.argRegs] at hq
  simp only [e1, e2, e3, e4, Arg.val, hm₂, er, A.poly' i1 hD, A.poly' i2 hD, sw32_ofNat (gamma2_lt hγ)] at hq
  exact hq

theorem hintCall_tr {nm : String} {P : Prims} (hP : PrimsOk P D) {z r h : Ptr} {γ : Nat} (hγ : γ ∈ gamma2s)
    (hc : hintChk (rbs ++ wbs) wbs z r h = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧ (Reduced x.mem (pa x z) ∧ Reduced x.mem (pa x r)) ∧
      (Reduced y.mem (pa y z) ∧ Reduced y.mem (pa y r)))
      (callP nm P.makeHint [.ptr z, .ptr r, .imm γ, .ptr h]) fun _ _ => True := by
  obtain ⟨w1, i1, i2, i3, _⟩ := hintChk_spec hc
  refine callP_tr hP.makeHint.okMx (hP.makeHint.ctMx fun _ _ h => h) (hintArgs_ok hγ hc)
    fun x y x1 y1 ⟨R, ⟨rzx, rrx⟩, ⟨rzy, rry⟩⟩ ⟨⟨hAx, hmx⟩, kx⟩ ⟨⟨hAy, hmy⟩, ky⟩ =>
      ⟨_, _, _, _, hintPre hP.makeHint.hS (At.of R.lx hmx kx) hγ hc hAx rzx rrx,
        hintPre hP.makeHint.hS (At.of R.ly hmy ky) hγ hc hAy rzy rry, ?_,
        by rw [kx.2.1, kx.2.2]; exact Covers.append_left (Covers.cons (R.lx.cR i1) (R.lx.cR i2)) (Covers.right (R.lx.cW w1)),
        by rw [kx.2.2]; exact R.lx.cW w1,
        by rw [ky.2.1, ky.2.2]; exact Covers.append_left (Covers.cons (R.ly.cR i1) (R.ly.cR i2)) (Covers.right (R.ly.cW w1)),
        by rw [ky.2.2]; exact R.ly.cW w1,
        by rw [(At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp]⟩
  obtain ⟨hx1, hx2, hx3, hx4⟩ := argsIn4 hAx
  obtain ⟨hy1, hy2, hy3, hy4⟩ := argsIn4 hAy
  sig_pub [Contract.mxFree, makeHintContract, makeHintSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hx1, hx2, hx3, hx4, hy1, hy2, hy3, hy4, Arg.val, R.pa i1, R.pa i2, R.pa i3,
    (At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp, and_self]

end

end VG.Proof.MlDsa.X86_64.Sign

end

end

/-!
# ML-DSA signing on x86-64: calls of the packing primitives

As `Prims.lean`, for `vg_mldsa_simple_bit_pack`, `vg_mldsa_bit_pack`,
`vg_mldsa_bit_unpack` and `vg_mldsa_hint_bit_pack` (which may leak the hint:
two runs leak the same when their hints agree, `hbpAt_tr`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable {D : Nat} {rbs wbs : List (Reg × Nat)}

/-! ## `SimpleBitPack` -/

theorem sbpArgs_ok {bs : List (Reg × Nat)} {f out : Ptr} {b len : Nat} (hb : b < 2 ^ 32) (hl : len < 2 ^ 32)
    (hc : rwChk bs wbs f 1024 out len = true) : [Arg.ptr f, .imm b, .ptr out, .imm len].all Arg.ok = true := by
  obtain ⟨_, _, _, _, b1, o1, b2, o2⟩ := rwChk_spec hc
  simp only [List.all_cons, List.all_nil, Arg.ok, b1, o1, b2, o2, decide_true, Bool.and_true,
    decide_eq_true hb, decide_eq_true hl]

theorem sbpPre {S : Nat} (hS : S + 8 ≤ D) {s s1 : State} (A : At D rbs wbs s s1) {f out : Ptr} {b len : Nat}
    (hb : b ∈ simpleBitPackBounds) (hl : len = 32 * bitlen b) (hc : rwChk (rbs ++ wbs) wbs f 1024 out len = true)
    (hA : ArgsIn [.ptr f, .imm b, .ptr out, .imm len] s s1)
    (hle : ∀ i < 256, (coeffAt s.mem (pa s f) i).toNat ≤ b) :
    (simpleBitPackContract X86_64.abi S).pre (s1.callEntry.withRegions [pR (pa s f)] [⟨pa s out, len⟩]) := by
  obtain ⟨_, i1, i2, d12, _⟩ := rwChk_spec hc
  obtain ⟨e1, e2, e3, e4⟩ := argsIn4 hA
  have hD : 8 ≤ D := by omega_arith
  have hb' : b < 2 ^ 32 ∧ len < 2 ^ 32 := by
    simp only [simpleBitPackBounds, t1Max, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> subst hl <;> decide
  have hwf := ce_wfS (ws := [64, 32, 64, 64]) (by decide) hS (A.rsp ▸ A.L.sp) [pR (pa s f)] [⟨pa s out, len⟩]
  sig_pre [simpleBitPackContract, simpleBitPackSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [e1, e2, e3, e4, Arg.val, sw32_ofNat hb'.1, toNat64 hb'.2]
  refine ⟨hwf, trivial, trivial, A.L.disj d12, A.ret i1 hD, ?_, A.L.nwp i1, A.L.nwp i2, hb, hl,
    fun i hi => by rw [A.coeff' i1 hD hi]; exact hle i hi⟩
  refine Sig.conj_cons.mpr ⟨A.ret i2 hD, conj_stk [pR (pa s f), ⟨pa s out, len⟩] ?_⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨A.stk hS i1, A.stk hS i2⟩

theorem sbpAt_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {f out : Ptr} {b len : Nat}
    (hb : b ∈ simpleBitPackBounds) (hl : len = 32 * bitlen b) (hc : rwChk (rbs ++ wbs) wbs f 1024 out len = true)
    (hle : ∀ i < 256, (coeffAt s.mem (pa s f) i).toNat ≤ b) :
    WP isa (simpleBitPackAt P f b out len) s fun s' => PPostB D s s' [(out, len)] ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      bytesAt s'.mem (pa s out) len = simpleBitPack (natPolyAt s.mem (pa s f)) b := by
  obtain ⟨w1, i1, i2, _, _⟩ := rwChk_spec hc
  have hD : 8 ≤ D := by have := hP.simpleBitPack.hS; omega_arith
  have hb' : b < 2 ^ 32 ∧ len < 2 ^ 32 := by
    simp only [simpleBitPackBounds, t1Max, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> subst hl <;> decide
  refine WP.mono (callP_ok hP.simpleBitPack.ver.1 hP.simpleBitPack.nosp hP.simpleBitPack.depth L.dsm
    (sbpArgs_ok hb'.1 hb'.2 hc) (fun s1 hA hm k => sbpPre hP.simpleBitPack.hS (At.of L hm k) hb hl hc hA hle)
    (Covers.append_left (L.cR i1) (Covers.right (L.cW w1))) (L.cW w1))
    fun s' ⟨hpost, hcs, s1, hA, hm, k, s₂, hm₂, _, hq⟩ => ⟨hpost, hcs, ?_⟩
  have A := At.of L hm k
  obtain ⟨e1, e2, e3, e4⟩ := argsIn4 hA
  sig_post [simpleBitPackContract, simpleBitPackSig, X86_64.abi, VG.X86_64.argRegs] at hq
  simp only [e1, e2, e3, e4, Arg.val, hm₂, A.natPoly' i1 hD, sw32_ofNat hb'.1, toNat64 hb'.2] at hq
  exact hq

theorem sbpAt_tr {P : Prims} (hP : PrimsOk P D) {f out : Ptr} {b len : Nat}
    (hb : b ∈ simpleBitPackBounds) (hl : len = 32 * bitlen b) (hc : rwChk (rbs ++ wbs) wbs f 1024 out len = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧ (∀ i < 256, (coeffAt x.mem (pa x f) i).toNat ≤ b) ∧
      (∀ i < 256, (coeffAt y.mem (pa y f) i).toNat ≤ b)) (simpleBitPackAt P f b out len) fun _ _ => True := by
  obtain ⟨w1, i1, i2, _, _⟩ := rwChk_spec hc
  have hb' : b < 2 ^ 32 ∧ len < 2 ^ 32 := by
    simp only [simpleBitPackBounds, t1Max, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> subst hl <;> decide
  refine callP_tr hP.simpleBitPack.okMx (hP.simpleBitPack.ctMx fun _ _ h => h) (sbpArgs_ok hb'.1 hb'.2 hc)
    fun x y x1 y1 ⟨R, rx, ry⟩ ⟨⟨hAx, hmx⟩, kx⟩ ⟨⟨hAy, hmy⟩, ky⟩ =>
      ⟨_, _, _, _, sbpPre hP.simpleBitPack.hS (At.of R.lx hmx kx) hb hl hc hAx rx,
        sbpPre hP.simpleBitPack.hS (At.of R.ly hmy ky) hb hl hc hAy ry, ?_,
        by rw [kx.2.1, kx.2.2]; exact Covers.append_left (R.lx.cR i1) (Covers.right (R.lx.cW w1)),
        by rw [kx.2.2]; exact R.lx.cW w1,
        by rw [ky.2.1, ky.2.2]; exact Covers.append_left (R.ly.cR i1) (Covers.right (R.ly.cW w1)),
        by rw [ky.2.2]; exact R.ly.cW w1,
        by rw [(At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp]⟩
  obtain ⟨hx1, hx2, hx3, hx4⟩ := argsIn4 hAx
  obtain ⟨hy1, hy2, hy3, hy4⟩ := argsIn4 hAy
  sig_pub [Contract.mxFree, simpleBitPackContract, simpleBitPackSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hx1, hx2, hx3, hx4, hy1, hy2, hy3, hy4, Arg.val, R.pa i1, R.pa i2,
    (At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp, and_self]

/-! ## `BitPack` -/

theorem bitPackParams_lt {a b : Nat} (h : (a, b) ∈ bitPackParams) :
    a < 2 ^ 32 ∧ b < 2 ^ 32 ∧ 32 * bitlen (a + b) < 2 ^ 32 := by
  simp only [bitPackParams, d, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem bpArgs_ok {bs : List (Reg × Nat)} {f out : Ptr} {a b len : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (hl : len < 2 ^ 32)
    (hc : rwChk bs wbs f 1024 out len = true) : [Arg.ptr f, .imm a, .imm b, .ptr out, .imm len].all Arg.ok = true := by
  obtain ⟨_, _, _, _, b1, o1, b2, o2⟩ := rwChk_spec hc
  simp only [List.all_cons, List.all_nil, Arg.ok, b1, o1, b2, o2, decide_true, Bool.and_true,
    decide_eq_true ha, decide_eq_true hb, decide_eq_true hl]

/-- The coefficients of a polynomial of `R` in `[-a, b]`. -/
def InRange (m : Mem) (p : Addr) (a b : Nat) : Prop :=
  ∀ i < 256, -(a : Int) ≤ modPm (coeffAt m p i).toNat q ∧ modPm (coeffAt m p i).toNat q ≤ b

theorem bpPre {S : Nat} (hS : S + 8 ≤ D) {s s1 : State} (A : At D rbs wbs s s1) {f out : Ptr} {a b len : Nat}
    (hp : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b)) (hc : rwChk (rbs ++ wbs) wbs f 1024 out len = true)
    (hA : ArgsIn [.ptr f, .imm a, .imm b, .ptr out, .imm len] s s1) (hr : Reduced s.mem (pa s f))
    (hrg : InRange s.mem (pa s f) a b) :
    (bitPackContract X86_64.abi S).pre (s1.callEntry.withRegions [pR (pa s f)] [⟨pa s out, len⟩]) := by
  obtain ⟨_, i1, i2, d12, _⟩ := rwChk_spec hc
  obtain ⟨e1, e2, e3, e4, e5⟩ := argsIn5 hA
  have hD : 8 ≤ D := by omega_arith
  obtain ⟨ha', hb', hl'⟩ := bitPackParams_lt hp
  rw [← hl] at hl'
  have hwf := ce_wfS (ws := [64, 32, 32, 64, 64]) (by decide) hS (A.rsp ▸ A.L.sp) [pR (pa s f)] [⟨pa s out, len⟩]
  sig_pre [bitPackContract, bitPackSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [e1, e2, e3, e4, e5, Arg.val, sw32_ofNat ha', sw32_ofNat hb', toNat64 hl']
  refine ⟨hwf, trivial, trivial, A.L.disj d12, A.ret i1 hD, ?_, A.L.nwp i1, A.L.nwp i2, hp, hl, A.red' i1 hD hr,
    fun i hi => by rw [A.coeff' i1 hD hi]; exact hrg i hi⟩
  refine Sig.conj_cons.mpr ⟨A.ret i2 hD, conj_stk [pR (pa s f), ⟨pa s out, len⟩] ?_⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨A.stk hS i1, A.stk hS i2⟩

theorem bpAt_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {f out : Ptr} {a b len : Nat}
    (hp : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b)) (hc : rwChk (rbs ++ wbs) wbs f 1024 out len = true)
    (hr : Reduced s.mem (pa s f)) (hrg : InRange s.mem (pa s f) a b) :
    WP isa (bitPackAt P f a b out len) s fun s' => PPostB D s s' [(out, len)] ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      bytesAt s'.mem (pa s out) len = bitPack ((polyAt s.mem (pa s f)).map fun c => modPm c.val q) a b := by
  obtain ⟨w1, i1, i2, _, _⟩ := rwChk_spec hc
  have hD : 8 ≤ D := by have := hP.bitPack.hS; omega_arith
  obtain ⟨ha', hb', hl'⟩ := bitPackParams_lt hp
  rw [← hl] at hl'
  refine WP.mono (callP_ok hP.bitPack.ver.1 hP.bitPack.nosp hP.bitPack.depth L.dsm (bpArgs_ok ha' hb' hl' hc)
    (fun s1 hA hm k => bpPre hP.bitPack.hS (At.of L hm k) hp hl hc hA hr hrg)
    (Covers.append_left (L.cR i1) (Covers.right (L.cW w1))) (L.cW w1))
    fun s' ⟨hpost, hcs, s1, hA, hm, k, s₂, hm₂, _, hq⟩ => ⟨hpost, hcs, ?_⟩
  have A := At.of L hm k
  obtain ⟨e1, e2, e3, e4, e5⟩ := argsIn5 hA
  sig_post [bitPackContract, bitPackSig, X86_64.abi, VG.X86_64.argRegs] at hq
  simp only [e1, e2, e3, e4, e5, Arg.val, hm₂, A.poly' i1 hD, sw32_ofNat ha', sw32_ofNat hb', toNat64 hl'] at hq
  exact hq

theorem bpAt_tr {P : Prims} (hP : PrimsOk P D) {f out : Ptr} {a b len : Nat}
    (hp : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b)) (hc : rwChk (rbs ++ wbs) wbs f 1024 out len = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧ (Reduced x.mem (pa x f) ∧ InRange x.mem (pa x f) a b) ∧
      (Reduced y.mem (pa y f) ∧ InRange y.mem (pa y f) a b)) (bitPackAt P f a b out len) fun _ _ => True := by
  obtain ⟨w1, i1, i2, _, _⟩ := rwChk_spec hc
  obtain ⟨ha', hb', hl'⟩ := bitPackParams_lt hp
  rw [← hl] at hl'
  refine callP_tr hP.bitPack.okMx (hP.bitPack.ctMx fun _ _ h => h) (bpArgs_ok ha' hb' hl' hc)
    fun x y x1 y1 ⟨R, ⟨rx, gx⟩, ⟨ry, gy⟩⟩ ⟨⟨hAx, hmx⟩, kx⟩ ⟨⟨hAy, hmy⟩, ky⟩ =>
      ⟨_, _, _, _, bpPre hP.bitPack.hS (At.of R.lx hmx kx) hp hl hc hAx rx gx,
        bpPre hP.bitPack.hS (At.of R.ly hmy ky) hp hl hc hAy ry gy, ?_,
        by rw [kx.2.1, kx.2.2]; exact Covers.append_left (R.lx.cR i1) (Covers.right (R.lx.cW w1)),
        by rw [kx.2.2]; exact R.lx.cW w1,
        by rw [ky.2.1, ky.2.2]; exact Covers.append_left (R.ly.cR i1) (Covers.right (R.ly.cW w1)),
        by rw [ky.2.2]; exact R.ly.cW w1,
        by rw [(At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp]⟩
  obtain ⟨hx1, hx2, hx3, hx4, hx5⟩ := argsIn5 hAx
  obtain ⟨hy1, hy2, hy3, hy4, hy5⟩ := argsIn5 hAy
  sig_pub [Contract.mxFree, bitPackContract, bitPackSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hx1, hx2, hx3, hx4, hx5, hy1, hy2, hy3, hy4, hy5, Arg.val, R.pa i1, R.pa i2,
    (At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp, and_self]

/-! ## `BitUnpack` -/

theorem bupArgs_ok {bs : List (Reg × Nat)} {v f : Ptr} {a b len : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (hl : len < 2 ^ 32)
    (hc : rwChk bs wbs v len f 1024 = true) : [Arg.ptr v, .imm len, .imm a, .imm b, .ptr f].all Arg.ok = true := by
  obtain ⟨_, _, _, _, b1, o1, b2, o2⟩ := rwChk_spec hc
  simp only [List.all_cons, List.all_nil, Arg.ok, b1, o1, b2, o2, decide_true, Bool.and_true,
    decide_eq_true ha, decide_eq_true hb, decide_eq_true hl]

theorem bupPre {S : Nat} (hS : S + 8 ≤ D) {s s1 : State} (A : At D rbs wbs s s1) {v f : Ptr} {a b len : Nat}
    (hp : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b)) (hc : rwChk (rbs ++ wbs) wbs v len f 1024 = true)
    (hA : ArgsIn [.ptr v, .imm len, .imm a, .imm b, .ptr f] s s1) :
    (bitUnpackContract X86_64.abi S).pre (s1.callEntry.withRegions [⟨pa s v, len⟩] [pR (pa s f)]) := by
  obtain ⟨_, i1, i2, d12, _⟩ := rwChk_spec hc
  obtain ⟨e1, e2, e3, e4, e5⟩ := argsIn5 hA
  have hD : 8 ≤ D := by omega_arith
  obtain ⟨ha', hb', hl'⟩ := bitPackParams_lt hp
  rw [← hl] at hl'
  have hwf := ce_wfS (ws := [64, 64, 32, 32, 64]) (by decide) hS (A.rsp ▸ A.L.sp) [⟨pa s v, len⟩] [pR (pa s f)]
  sig_pre [bitUnpackContract, bitUnpackSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [e1, e2, e3, e4, e5, Arg.val, sw32_ofNat ha', sw32_ofNat hb', toNat64 hl']
  refine ⟨hwf, trivial, trivial, A.L.disj d12, A.ret i1 hD, ?_, A.L.nwp i1, A.L.nwp i2, hp, hl⟩
  refine Sig.conj_cons.mpr ⟨A.ret i2 hD, conj_stk [⟨pa s v, len⟩, pR (pa s f)] ?_⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨A.stk hS i1, A.stk hS i2⟩

theorem bupAt_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {v f : Ptr} {a b len : Nat}
    (hp : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b)) (hc : rwChk (rbs ++ wbs) wbs v len f 1024 = true) :
    WP isa (bitUnpackAt P v len a b f) s fun s' => PPostB D s s' [(f, 1024)] ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      PolyIs s'.mem (pa s f) (toRq (bitUnpack (bytesAt s.mem (pa s v) len) a b)) := by
  obtain ⟨w1, i1, i2, _, _⟩ := rwChk_spec hc
  have hD : 8 ≤ D := by have := hP.bitUnpack.hS; omega_arith
  obtain ⟨ha', hb', hl'⟩ := bitPackParams_lt hp
  rw [← hl] at hl'
  refine WP.mono (callP_ok hP.bitUnpack.ver.1 hP.bitUnpack.nosp hP.bitUnpack.depth L.dsm (bupArgs_ok ha' hb' hl' hc)
    (fun s1 hA hm k => bupPre hP.bitUnpack.hS (At.of L hm k) hp hl hc hA)
    (Covers.append_left (L.cR i1) (Covers.right (L.cW w1))) (L.cW w1))
    fun s' ⟨hpost, hcs, s1, hA, hm, k, s₂, hm₂, _, hq⟩ => ⟨hpost, hcs, ?_⟩
  have A := At.of L hm k
  obtain ⟨e1, e2, e3, e4, e5⟩ := argsIn5 hA
  sig_post [bitUnpackContract, bitUnpackSig, X86_64.abi, VG.X86_64.argRegs] at hq
  simp only [e1, e2, e3, e4, e5, Arg.val, hm₂, A.bytes' i1 hD, sw32_ofNat ha', sw32_ofNat hb', toNat64 hl'] at hq
  exact hq

theorem bupAt_tr {P : Prims} (hP : PrimsOk P D) {v f : Ptr} {a b len : Nat}
    (hp : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b)) (hc : rwChk (rbs ++ wbs) wbs v len f 1024 = true) :
    RelCT isa (LRel D rbs wbs) (bitUnpackAt P v len a b f) fun _ _ => True := by
  obtain ⟨w1, i1, i2, _, _⟩ := rwChk_spec hc
  obtain ⟨ha', hb', hl'⟩ := bitPackParams_lt hp
  rw [← hl] at hl'
  refine callP_tr hP.bitUnpack.okMx (hP.bitUnpack.ctMx fun _ _ h => h) (bupArgs_ok ha' hb' hl' hc)
    fun x y x1 y1 R ⟨⟨hAx, hmx⟩, kx⟩ ⟨⟨hAy, hmy⟩, ky⟩ =>
      ⟨_, _, _, _, bupPre hP.bitUnpack.hS (At.of R.lx hmx kx) hp hl hc hAx,
        bupPre hP.bitUnpack.hS (At.of R.ly hmy ky) hp hl hc hAy, ?_,
        by rw [kx.2.1, kx.2.2]; exact Covers.append_left (R.lx.cR i1) (Covers.right (R.lx.cW w1)),
        by rw [kx.2.2]; exact R.lx.cW w1,
        by rw [ky.2.1, ky.2.2]; exact Covers.append_left (R.ly.cR i1) (Covers.right (R.ly.cW w1)),
        by rw [ky.2.2]; exact R.ly.cW w1,
        by rw [(At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp]⟩
  obtain ⟨hx1, hx2, hx3, hx4, hx5⟩ := argsIn5 hAx
  obtain ⟨hy1, hy2, hy3, hy4, hy5⟩ := argsIn5 hAy
  sig_pub [Contract.mxFree, bitUnpackContract, bitUnpackSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hx1, hx2, hx3, hx4, hx5, hy1, hy2, hy3, hy4, hy5, Arg.val, R.pa i1, R.pa i2,
    (At.of R.lx hmx kx).rsp, (At.of R.ly hmy ky).rsp, R.rsp, and_self]

/-! ## `HintBitPack` -/

theorem hbpArgs_ok {bs : List (Reg × Nat)} {h y : Ptr} {hlen ω len : Nat} (h1 : hlen < 2 ^ 32) (h2 : ω < 2 ^ 32) (h3 : len < 2 ^ 32)
    (hc : rwChk bs wbs h (hlen * 4) y len = true) :
    [Arg.ptr h, .imm hlen, .imm ω, .ptr y, .imm len].all Arg.ok = true := by
  obtain ⟨_, _, _, _, b1, o1, b2, o2⟩ := rwChk_spec hc
  simp only [List.all_cons, List.all_nil, Arg.ok, b1, o1, b2, o2, decide_true, Bool.and_true,
    decide_eq_true h1, decide_eq_true h2, decide_eq_true h3]

theorem hintParams_lt {ω k : Nat} (h : (ω, k) ∈ hintParams) : ω < 2 ^ 32 ∧ ω + k < 2 ^ 32 ∧ 256 * k < 2 ^ 32 := by
  simp only [hintParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem hbpPre {S : Nat} (hS : S + 8 ≤ D) {s s1 : State} (A : At D rbs wbs s s1) {h y : Ptr} {ω k : Nat}
    (hp : (ω, k) ∈ hintParams) (hc : rwChk (rbs ++ wbs) wbs h (256 * k * 4) y (ω + k) = true)
    (hA : ArgsIn [.ptr h, .imm (256 * k), .imm ω, .ptr y, .imm (ω + k)] s s1)
    (hones : hintOnes (hintAt s.mem (pa s h) k) ≤ ω) :
    (hintBitPackContract X86_64.abi S).pre
      (s1.callEntry.withRegions [⟨pa s h, 256 * k * 4⟩] [⟨pa s y, ω + k⟩]) := by
  obtain ⟨_, i1, i2, d12, _⟩ := rwChk_spec hc
  obtain ⟨e1, e2, e3, e4, e5⟩ := argsIn5 hA
  have hD : 8 ≤ D := by omega_arith
  obtain ⟨h1, h2, h3⟩ := hintParams_lt hp
  have hwf := ce_wfS (ws := [64, 64, 32, 64, 64]) (by decide) hS (A.rsp ▸ A.L.sp) [⟨pa s h, 256 * k * 4⟩]
    [⟨pa s y, ω + k⟩]
  have ek : ω + k - ω = k := by omega_arith
  have i1' : inB (rbs ++ wbs) h (1024 * k) = true := by rw [show 1024 * k = 256 * k * 4 by omega_arith]; exact i1
  sig_pre [hintBitPackContract, hintBitPackSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [e1, e2, e3, e4, e5, Arg.val, sw32_ofNat h1, toNat64 h2, toNat64 h3, ek]
  refine ⟨hwf, trivial, trivial, A.L.disj d12, A.ret i1 hD, ?_, A.L.nwp i1, A.L.nwp i2, hp, by omega_arith, trivial,
    by rw [A.hint i1' hD]; exact hones⟩
  refine Sig.conj_cons.mpr ⟨A.ret i2 hD, conj_stk [⟨pa s h, 256 * k * 4⟩, ⟨pa s y, ω + k⟩] ?_⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨A.stk hS i1, A.stk hS i2⟩

theorem hbpAt_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {h y : Ptr} {ω k : Nat}
    (hp : (ω, k) ∈ hintParams) (hc : rwChk (rbs ++ wbs) wbs h (256 * k * 4) y (ω + k) = true)
    (hones : hintOnes (hintAt s.mem (pa s h) k) ≤ ω) :
    WP isa (hintBitPackAt P h (256 * k) ω y (ω + k)) s fun s' => PPostB D s s' [(y, ω + k)] ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      bytesAt s'.mem (pa s y) (ω + k) = hintBitPack ω k (hintAt s.mem (pa s h) k) := by
  obtain ⟨w1, i1, i2, _, _⟩ := rwChk_spec hc
  have hD : 8 ≤ D := by have := hP.hintBitPack.hS; omega_arith
  obtain ⟨h1, h2, h3⟩ := hintParams_lt hp
  have ek : ω + k - ω = k := by omega_arith
  have i1' : inB (rbs ++ wbs) h (1024 * k) = true := by rw [show 1024 * k = 256 * k * 4 by omega_arith]; exact i1
  refine WP.mono (callP_ok hP.hintBitPack.ver.1 hP.hintBitPack.nosp hP.hintBitPack.depth L.dsm
    (hbpArgs_ok h3 h1 h2 hc) (fun s1 hA hm k => hbpPre hP.hintBitPack.hS (At.of L hm k) hp hc hA hones)
    (Covers.append_left (L.cR i1) (Covers.right (L.cW w1))) (L.cW w1))
    fun s' ⟨hpost, hcs, s1, hA, hm, k', s₂, hm₂, _, hq⟩ => ⟨hpost, hcs, ?_⟩
  have A := At.of L hm k'
  obtain ⟨e1, e2, e3, e4, e5⟩ := argsIn5 hA
  sig_post [hintBitPackContract, hintBitPackSig, X86_64.abi, VG.X86_64.argRegs] at hq
  simp only [e1, e3, e4, e5, Arg.val, hm₂, sw32_ofNat h1, toNat64 h2, ek, A.hint i1' hD] at hq
  exact hq

/-- Two runs leak the same when their hints (as the `u32`s at `h`) agree. -/
theorem hbpAt_tr {P : Prims} (hP : PrimsOk P D) {h y : Ptr} {ω k : Nat} (hp : (ω, k) ∈ hintParams)
    (hc : rwChk (rbs ++ wbs) wbs h (256 * k * 4) y (ω + k) = true) :
    RelCT isa (fun x z => LRel D rbs wbs x z ∧ hintOnes (hintAt x.mem (pa x h) k) ≤ ω ∧
      hintOnes (hintAt z.mem (pa z h) k) ≤ ω ∧
      (List.range (256 * k)).map (fun i => (coeffAt x.mem (pa x h) i).toNat) =
        (List.range (256 * k)).map (fun i => (coeffAt z.mem (pa z h) i).toNat))
      (hintBitPackAt P h (256 * k) ω y (ω + k)) fun _ _ => True := by
  obtain ⟨w1, i1, i2, _, _⟩ := rwChk_spec hc
  have hD : 8 ≤ D := by have := hP.hintBitPack.hS; omega_arith
  obtain ⟨h1, h2, h3⟩ := hintParams_lt hp
  refine callP_tr hP.hintBitPack.okMx (hP.hintBitPack.ctMx fun _ _ h => h) (hbpArgs_ok h3 h1 h2 hc)
    fun x z x1 z1 ⟨R, ox, oz, hl⟩ ⟨⟨hAx, hmx⟩, kx⟩ ⟨⟨hAz, hmz⟩, kz⟩ =>
      ⟨_, _, _, _, hbpPre hP.hintBitPack.hS (At.of R.lx hmx kx) hp hc hAx ox,
        hbpPre hP.hintBitPack.hS (At.of R.ly hmz kz) hp hc hAz oz, ?_,
        by rw [kx.2.1, kx.2.2]; exact Covers.append_left (R.lx.cR i1) (Covers.right (R.lx.cW w1)),
        by rw [kx.2.2]; exact R.lx.cW w1,
        by rw [kz.2.1, kz.2.2]; exact Covers.append_left (R.ly.cR i1) (Covers.right (R.ly.cW w1)),
        by rw [kz.2.2]; exact R.ly.cW w1,
        by rw [(At.of R.lx hmx kx).rsp, (At.of R.ly hmz kz).rsp, R.rsp]⟩
  obtain ⟨hx1, hx2, hx3, hx4, hx5⟩ := argsIn5 hAx
  obtain ⟨hz1, hz2, hz3, hz4, hz5⟩ := argsIn5 hAz
  have Ax := At.of R.lx hmx kx
  have Az := At.of R.ly hmz kz
  sig_pub [Contract.mxFree, hintBitPackContract, hintBitPackSig, X86_64.abi, VG.X86_64.argRegs]
  simp only [hx1, hx2, hx3, hx4, hx5, hz1, hz2, hz3, hz4, hz5, Arg.val, toNat64 h3, Ax.coeffs (len := 256 * k) i1 hD,
    Az.coeffs (len := 256 * k) i1 hD, hl]
  simp only [Ax.rsp, Az.rsp, R.rsp, R.pa i1, R.pa i2, and_self]

end

end VG.Proof.MlDsa.X86_64.Sign

end

end

/-!
# ML-DSA signing on x86-64: the private key and `ρ″`

Once `Â` is sampled (`IM`), `ŝ₁[r]`, `ŝ₂[i]` and `t̂₀[i]`, each the `NTT` of
the `BitUnpack` of its piece of `sk` (`dec_ok`), in their slots (`ID`), and
`ρ″ = H(K ‖ rnd ‖ μ, 64)` at `MS` (`decode_ok`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable (p : Params)

/-- The slots of `ŝ₁`, `ŝ₂` and `t̂₀`. -/
abbrev s1Base : Nat := 5 + 2 * p.k + 2 * p.ℓ
abbrev s2Base : Nat := 5 + 2 * p.k + 3 * p.ℓ
abbrev t0Base : Nat := 5 + 3 * p.k + 3 * p.ℓ

/-- `ŝ₁[r]`, `ŝ₂[i]` and `t̂₀[i]` of the function entered in `σ`. -/
abbrev S1v (σ : State) (r : Nat) : Poly := s1F p (skOf p σ) r
abbrev S2v (σ : State) (i : Nat) : Poly := s2F p (skOf p σ) i
abbrev T0v (σ : State) (i : Nat) : Poly := t0F p (skOf p σ) i

/-- `ρ″ = H(K ‖ rnd ‖ μ, 64)`. -/
abbrev rppOf (σ : State) : List Byte := H (((skOf p σ).drop 32).take 32 ++ rndOf σ ++ muOf σ) 64

end

/-! ## `Â` -/

/-- `Â` sampled within `maxBounds`, in its slots. -/
structure IM (p : Params) (D : Nat) (σ s : State) : Prop where
  st : St p D σ s
  ok : ∀ e < p.k * p.ℓ, (rejNTTPoly maxBounds.rejNTT (seedE p σ e)).isSome
  A : Fam s (aBase p) (p.k * p.ℓ) (aVal p σ)

def imChk (p : Params) (ws : List (Ptr × Nat)) : Bool := stChk p ws && famChk (sgB p) ws (aBase p) (p.k * p.ℓ)

theorem IM.step {p : Params} {D : Nat} {σ s s' : State} (h : IM p D σ s) {ws : List (Ptr × Nat)}
    (hP : PPostB D s s' ws) (hc : imChk p ws = true) : IM p D σ s' := by
  simp only [imChk, Bool.and_eq_true] at hc
  exact ⟨h.st.step hP hc.1, h.ok, Fam.keep h.st.lay hP hc.2 h.A⟩

/-! ## The private key -/

/-- `Â`, the first `a` polynomials of `ŝ₁`, `b` of `ŝ₂` and `c` of `t̂₀`. -/
structure ID (p : Params) (D : Nat) (σ : State) (a b c : Nat) (s : State) : Prop where
  im : IM p D σ s
  s1 : Fam s (s1Base p) a (S1v p σ)
  s2 : Fam s (s2Base p) b (S2v p σ)
  t0 : Fam s (t0Base p) c (T0v p σ)

def idChk (p : Params) (ws : List (Ptr × Nat)) (a b c : Nat) : Bool :=
  imChk p ws && famChk (sgB p) ws (s1Base p) a && famChk (sgB p) ws (s2Base p) b && famChk (sgB p) ws (t0Base p) c

theorem ID.step {p : Params} {D : Nat} {σ s s' : State} {a b c : Nat} (h : ID p D σ a b c s)
    {ws : List (Ptr × Nat)} (hP : PPostB D s s' ws) (hc : idChk p ws a b c = true) : ID p D σ a b c s' := by
  simp only [idChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
  have L := h.im.st.lay
  exact ⟨h.im.step hP h1, Fam.keep L hP h2 h.s1, Fam.keep L hP h3 h.s2, Fam.keep L hP h4 h.t0⟩

theorem pS_bases (j : Nat) : (pS j).1 ∈ bases := List.mem_cons_self ..

theorem sc_bases (o : Nat) : (sc o).1 ∈ bases := List.mem_cons_self ..

theorem pa_add (s : State) (r : Reg) (a b : Nat) : pa s (r, a) + BitVec.ofNat 64 b = pa s (r, a + b) :=
  VG.Proof.MlKem.X86_64.off_add _ _ _

theorem sk_slice {p : Params} {D : Nat} {σ s : State} (h : St p D σ s) {o len : Nat} (hk : o + len ≤ p.skLen) :
    bytesAt s.mem (pa s (.rbp, o)) len = ((skOf p σ).drop o).take len := by
  rw [← h.sk, VG.Proof.MlKem.bytesAt_slice _ _ hk, pa_add, Nat.zero_add]

/-- What decoding a polynomial of `len` bytes at `src` to slot `j` needs of the layout. -/
def decChk (p : Params) (a b c : Nat) (src : Ptr) (len j : Nat) : Bool :=
  rwChk (sgB p) (sgW p) src len (pS j) 1024 && ipChk (sgB p) (sgW p) (pS j) &&
    idChk p [(pS j, 1024)] a b c && idChk p [(pS j, 1024), (sc oPS, 1024)] a b c

theorem dec_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {σ : State} {a b c : Nat} {src : Ptr}
    {len x y j : Nat} (hp : (x, y) ∈ bitPackParams) (hl : len = 32 * bitlen (x + y))
    (hc : decChk p a b c src len j = true) {s : State} (h : ID p D σ a b c s) :
    WP isa (.seq (bitUnpackAt P src len x y (pS j)) (nttAt P (pS j))) s fun s' =>
      ID p D σ a b c s' ∧ Pl s' j (ntt (toRq (bitUnpack (bytesAt s.mem (pa s src) len) x y))) := by
  simp only [decChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
  refine WP.seq (WP.mono (bupAt_ok hP h.im.st.lay hp hl h1) fun s1 ⟨hP1, _, hq1⟩ => ?_)
  have I1 := h.step hP1 h3
  refine WP.mono (ipAt_ok (t := ntt) hP.ntt I1.im.st.lay h2 (by rw [hP1.pa (pS_bases j)]; exact hq1.1))
    fun s2 ⟨hP2, _, hq2⟩ => ⟨I1.step hP2 h4, ?_⟩
  show PolyIs s2.mem (pa s2 (pS j)) _
  rw [hP2.pa (pS_bases j), hP1.pa (pS_bases j), ← hq1.2]
  rw [hP1.pa (pS_bases j)] at hq2
  exact hq2

/-- What `decode` needs of the layout. -/
def dChk (p : Params) : Bool :=
  (List.range p.ℓ).all (fun r => decChk p r 0 0 (.rbp, skS1 p r) (sLen p) (s1Base p + r) &&
      decide (skS1 p r + sLen p ≤ p.skLen)) &&
    (List.range p.k).all (fun i => decChk p p.ℓ i 0 (.rbp, skS2 p i) (sLen p) (s2Base p + i) &&
      decide (skS2 p i + sLen p ≤ p.skLen)) &&
    (List.range p.k).all (fun i => decChk p p.ℓ p.k i (.rbp, skT0 p i) 416 (t0Base p + i) &&
      decide (skT0 p i + 416 ≤ p.skLen)) &&
    shakeChk (sgB p) (sgW p) [((.rbp, 32), 32), ((.r13, 0), 32), ((.r12, 0), 64)] (sc oMS) 64 &&
    idChk p [(sc 0, 200), (sc 200, 640), (sc oMS, 64)] p.ℓ p.k p.k && inB (sgB p) (sc oMS) 64 &&
    decide ((p.η, p.η) ∈ bitPackParams) && decide (64 ≤ p.skLen)

theorem dChk_ok {p : Params} (h : Ok3 p) : dChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide +kernel

/-- Decoded: `Â`, `ŝ₁`, `ŝ₂`, `t̂₀`, and `ρ″` at `MS`. -/
structure IK (p : Params) (D : Nat) (σ s : State) : Prop where
  d : ID p D σ p.ℓ p.k p.k s
  rpp : bytesAt s.mem (pa s (sc oMS)) 64 = rppOf p σ

theorem dChk_spec {p : Params} (hc : dChk p = true) :
    (∀ r < p.ℓ, decChk p r 0 0 (.rbp, skS1 p r) (sLen p) (s1Base p + r) = true ∧ skS1 p r + sLen p ≤ p.skLen) ∧
    (∀ i < p.k, decChk p p.ℓ i 0 (.rbp, skS2 p i) (sLen p) (s2Base p + i) = true ∧ skS2 p i + sLen p ≤ p.skLen) ∧
    (∀ i < p.k, decChk p p.ℓ p.k i (.rbp, skT0 p i) 416 (t0Base p + i) = true ∧ skT0 p i + 416 ≤ p.skLen) ∧
    shakeChk (sgB p) (sgW p) [((.rbp, 32), 32), ((.r13, 0), 32), ((.r12, 0), 64)] (sc oMS) 64 = true ∧
    idChk p [(sc 0, 200), (sc 200, 640), (sc oMS, 64)] p.ℓ p.k p.k = true ∧ inB (sgB p) (sc oMS) 64 = true ∧
    (p.η, p.η) ∈ bitPackParams ∧ 64 ≤ p.skLen := by
  simp only [dChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, hη⟩, hsk⟩ := hc
  exact ⟨h1, h2, h3, h4, h5, h6, hη, hsk⟩

theorem sLen_eq (p : Params) : sLen p = 32 * bitlen (p.η + p.η) := by rw [← Nat.two_mul]

section
variable {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (hc : dChk p = true) {σ : State}
include hP hc

theorem decS1_ok {r : Nat} (hr : r < p.ℓ) {s : State} (hs : ID p D σ r 0 0 s) :
    WP isa (decS1 P p r) s (ID p D σ (r + 1) 0 0) := by
  obtain ⟨c, ck⟩ := (dChk_spec hc).1 r hr
  refine WP.mono (dec_ok hP (dChk_spec hc).2.2.2.2.2.2.1 (sLen_eq p) c hs) fun s' ⟨I', hq⟩ =>
    ⟨I'.im, Fam.snoc I'.s1 ?_, I'.s2, I'.t0⟩
  rw [sk_slice hs.im.st ck] at hq
  exact hq

theorem decS2_ok {i : Nat} (hi : i < p.k) {s : State} (hs : ID p D σ p.ℓ i 0 s) :
    WP isa (decS2 P p i) s (ID p D σ p.ℓ (i + 1) 0) := by
  obtain ⟨c, ck⟩ := (dChk_spec hc).2.1 i hi
  refine WP.mono (dec_ok hP (dChk_spec hc).2.2.2.2.2.2.1 (sLen_eq p) c hs) fun s' ⟨I', hq⟩ =>
    ⟨I'.im, I'.s1, Fam.snoc I'.s2 ?_, I'.t0⟩
  rw [sk_slice hs.im.st ck] at hq
  exact hq

theorem decT0_ok {i : Nat} (hi : i < p.k) {s : State} (hs : ID p D σ p.ℓ p.k i s) :
    WP isa (decT0 P p i) s (ID p D σ p.ℓ p.k (i + 1)) := by
  obtain ⟨c, ck⟩ := (dChk_spec hc).2.2.1 i hi
  refine WP.mono (dec_ok hP (by decide) (by decide) c hs) fun s' ⟨I', hq⟩ => ⟨I'.im, I'.s1, I'.s2,
    Fam.snoc I'.t0 ?_⟩
  have e : skT0 p i = 128 + lenS p * p.ℓ + lenS p * p.k + 32 * 13 * i := by
    unfold skT0 lenS sLen; rw [Nat.mul_add]; omega_using []
  rw [sk_slice hs.im.st ck, e] at hq
  exact hq

theorem rpp_ok {s : State} (hs : ID p D σ p.ℓ p.k p.k s) : WP isa rpp s (IK p D σ) := by
  unfold rpp
  obtain ⟨_, _, _, h4, h5, _, _, hsk⟩ := dChk_spec hc
  refine WP.mono (shake_ok (sgB_bases p) hP.hD h4 hs.im.st.lay) fun s4 ⟨hP4, _, hb⟩ =>
    ⟨hs.step hP4 h5, ?_⟩
  rw [hP4.pa (by decide), hb]
  simp only [pieces, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [sk_slice hs.im.st (o := 32) (len := 32) (by omega_using [hsk]), hs.im.st.rnd, hs.im.st.mu, ← List.append_assoc]

theorem decode_ok {s : State} (h : IM p D σ s) : WP isa (decode P p) s (IK p D σ) := by
  unfold decode
  refine WP.seq (WP.mono (seqR_ok (I := fun r => ID p D σ r 0 0) p.ℓ 0
    (fun r _ hr s hs => decS1_ok hP hc (by omega_using [hr]) hs) s
    ⟨h, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s1 hs1 => ?_)
  rw [Nat.zero_add] at hs1
  refine WP.seq (WP.mono (seqR_ok (I := fun i => ID p D σ p.ℓ i 0) p.k 0
    (fun i _ hi s hs => decS2_ok hP hc (by omega_using [hi]) hs) s1
    ⟨hs1.im, hs1.s1, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩)
    fun s2 hs2 => ?_)
  rw [Nat.zero_add] at hs2
  refine WP.seq (WP.mono (seqR_ok (I := fun i => ID p D σ p.ℓ p.k i) p.k 0
    (fun i _ hi s hs => decT0_ok hP hc (by omega_using [hi]) hs) s2
    ⟨hs2.im, hs2.s1, hs2.s2, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s3 hs3 => ?_)
  rw [Nat.zero_add] at hs3
  exact rpp_ok hP hc hs3

end

/-! ## A prepared key -/

/-- The buffers read, with the whole prepared key at `rbp`. -/
abbrev sgRP (p : Params) : List (Reg × Nat) := [(.rbp, preparedSecretKeyBytes p), (.r12, 64), (.r13, 32)]

/-- The length of the polynomials of a prepared key. -/
abbrev polysLen (p : Params) : Nat := 1024 * (p.ℓ + 2 * p.k)

/-- What copying the polynomials of a prepared key needs of the layout. -/
def pkChk (p : Params) : Bool :=
  copyChk (sgRP p ++ sgW p) (sgW p) (s1P p 0) (.rbp, p.skLen) (polysLen p) &&
    imChk p [(s1P p 0, polysLen p)] && imChk p [] && inB (sgB p) (sc oFL) 8 && decide (preparedSecretKeyBytes p < 2 ^ 32) &&
    decide (scrLen p < 2 ^ 32 ∧ p.sigLen < 2 ^ 32) && decide (p.skLen + polysLen p = preparedSecretKeyBytes p)

theorem pkChk_ok {p : Params} (h : Ok3 p) : pkChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide +kernel

/-- Polynomial `i` of the prepared key of the function entered in `σ`. -/
abbrev prepV (p : Params) (σ : State) (i : Nat) : Poly := (preparedSecretPolys p (skOf p σ))[i]!

theorem prep_fam {p : Params} {D : Nat} {σ s s' : State} (hpre : (signK p D).pre σ) (hf : σ.gpr .r9 ≠ 0)
    (hc : pkChk p = true) (h : IM p D σ s) (hP : PPostB D s s' [(s1P p 0, polysLen p)])
    (hb : bytesAt s'.mem (pa s (s1P p 0)) (polysLen p) = bytesAt s.mem (pa s (.rbp, p.skLen)) (polysLen p))
    {i : Nat} (hi : i < p.ℓ + 2 * p.k) : Pl s' (s1Base p + i) (prepV p σ i) := by
  simp only [pkChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, hlen⟩ := hc
  have hpre' := hpre
  obtain ⟨-, hwr, d1, d2, -, -, -, -, -, -, -, -, -, -, k1, -, -, -, -, n1, -, -, -, -, -, hprep⟩ := hpre'
  have hL : skL p σ = preparedSecretKeyBytes p := by simp only [skL, hf, ite_false]
  rw [hL] at d1 d2 k1 n1
  have e2 : s.gpr .rbp = σ.gpr .rdi := h.st.top.regs (.rbp, .rdi) (by decide)
  -- The polynomial in the prepared key, unchanged since entry.
  have hl : p.skLen + 1024 * (p.ℓ + 2 * p.k) = preparedSecretKeyBytes p := hlen
  have hA : σ.gpr .rdi + BitVec.ofNat 64 p.skLen + BitVec.ofNat 64 (1024 * i) =
      σ.gpr .rdi + BitVec.ofNat 64 (p.skLen + 1024 * i) := VG.Proof.MlKem.X86_64.off_add _ _ _
  have hsub : Region.Sub ⟨σ.gpr .rdi + BitVec.ofNat 64 (p.skLen + 1024 * i), 1024⟩
      ⟨σ.gpr .rdi, preparedSecretKeyBytes p⟩ := Offset.sub_base _ (by omega_using [hi, hl])
  have hσ : bytesAt s.mem (σ.gpr .rdi + BitVec.ofNat 64 (p.skLen + 1024 * i)) 1024 =
      bytesAt σ.mem (σ.gpr .rdi + BitVec.ofNat 64 (p.skLen + 1024 * i)) 1024 := by
    refine VG.Proof.MlKem.bytesAt_frame h.st.fr (fun r hr => ?_) (by decide)
    rw [hwr] at hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [d1.sub_left hsub, d2.sub_left hsub, (k1.sub_right hsub).symm]
  have hpoly : PolyIs σ.mem (σ.gpr .rdi + BitVec.ofNat 64 (p.skLen + 1024 * i)) (prepV p σ i) :=
    (polyStored_iff).mp (hprep hf i hi)
  show PolyIs s'.mem (pa s' (pS (s1Base p + i))) _
  rw [hP.pa (pS_bases _)]
  refine PreparedKey.polyIs_of_copy ?_ hpoly
  have hd : pa s (pS (s1Base p + i)) = pa s (s1P p 0) + BitVec.ofNat 64 (1024 * i) := by
    rw [pa_add]
    exact congrArg (fun o => pa s (.rbx, o)) (by simp only [oP, s1Base]; omega_using [])
  have hi' : 1024 * i + 1024 ≤ polysLen p := by simp only [polysLen]; omega_using [hi]
  rw [hd, ← VG.Proof.MlKem.bytesAt_slice _ _ hi', hb, VG.Proof.MlKem.bytesAt_slice _ _ hi', ← hσ, ← hA]
  simp only [pa, e2]

theorem prepV_s1 (p : Params) (σ : State) {r : Nat} (hr : r < p.ℓ) : prepV p σ r = S1v p σ r :=
  PreparedKey.secret_s1 p _ hr

theorem prepV_s2 (p : Params) (σ : State) {i : Nat} (hi : i < p.k) : prepV p σ (p.ℓ + i) = S2v p σ i :=
  PreparedKey.secret_s2 p _ hi

theorem prepV_t0 (p : Params) (σ : State) {i : Nat} (hi : i < p.k) : prepV p σ (p.ℓ + p.k + i) = T0v p σ i :=
  PreparedKey.secret_t0 p _ hi

theorem copyKey_ok {p : Params} {D : Nat} {σ s : State} (hpre : (signK p D).pre σ) (hf : σ.gpr .r9 ≠ 0)
    (hD : D < 2 ^ 32) (hc : pkChk p = true) (h : IM p D σ s) :
    WP isa (copyKey p) s (ID p D σ p.ℓ p.k p.k) := by
  have hc' := hc
  simp only [pkChk, Bool.and_eq_true, decide_eq_true_eq] at hc'
  obtain ⟨⟨⟨⟨⟨⟨hcp, him⟩, -⟩, -⟩, hpl⟩, hsz⟩, -⟩ := hc'
  have hL : preparedSecretKeyBytes p ≤ skL p σ := by simp only [skL, hf, ite_false]; exact Nat.le_refl _
  have L' : Lay D (sgRP p) (sgW p) s := sgLayL hpre hL hD ⟨hsz.1, hpl, hsz.2⟩ h.st.top
  unfold copyKey
  refine WP.mono (copy_okB L' hcp) fun s' ⟨hP, _, hb⟩ => ?_
  have I := h.step hP him
  refine ⟨I, fun r hr => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [← prepV_s1 p σ hr]; exact prep_fam hpre hf hc h hP hb (by omega_using [hr])
  · rw [← prepV_s2 p σ hi, show s2Base p + i = s1Base p + (p.ℓ + i) by simp only [s1Base, s2Base]; omega_using []]
    exact prep_fam hpre hf hc h hP hb (by omega_using [hi])
  · rw [← prepV_t0 p σ hi, show t0Base p + i = s1Base p + (p.ℓ + p.k + i) by simp only [s1Base, t0Base]; omega_using []]
    exact prep_fam hpre hf hc h hP hb (by omega_using [hi])

/-- The flag at `FL` is the entry's `r9`. -/
theorem testFlag_ok {D : Nat} {σ s : State} (ht : Top σ s) (hin : InRegions (s.rd ++ s.wr) (pa s (sc oFL)) 8) :
    WP isa (.block testFlag) s fun s' => PPostB D s s' [] ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.zf = some (σ.gpr .r9 == 0) := by
  have e := ht.flag
  simp only [pa] at hin e
  unfold testFlag
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rax] (Q := fun s' => s'.mem = s.mem ∧
      s'.zf = some (s.mem.readW (s.gpr .rbx + BitVec.ofNat 64 oFL) 64 &&&
        s.mem.readW (s.gpr .rbx + BitVec.ofNat 64 oFL) 64 == 0)) (by xrun [hin]) (by decide))
    fun s' ⟨⟨hm, hz⟩, k⟩ => ⟨⟨k.2.1, k.2.2, fun r hr => k.gpr (by
        simp only [bases, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide), k.gpr (by decide),
        by rw [hm]; exact Frame.refl _ _⟩,
      fun r hr => k.gpr (by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide), hm, by rw [hz, e, BitVec.and_self]⟩

theorem decodeOrCopy_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (hc : dChk p = true)
    (hk : pkChk p = true) {σ s : State} (hpre : (signK p D).pre σ) (h : IM p D σ s) :
    WP isa (decodeOrCopy P p) s (IK p D σ) := by
  have hk' := hk
  simp only [pkChk, Bool.and_eq_true] at hk'
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, him⟩, hin⟩, -⟩, -⟩, -⟩ := hk'
  unfold decodeOrCopy
  refine WP.seq (WP.mono (testFlag_ok (D := D) h.st.top (h.st.lay.iR hin)) fun s1 ⟨hP1, _, _, hz⟩ => ?_)
  have h1 := h.step hP1 him
  refine WP.ite (M := isa) (!(σ.gpr .r9 == 0)) (show s1.zf.map (!·) = _ by rw [hz]; rfl) (fun hb => ?_) fun hb => ?_
  · have hf : σ.gpr .r9 ≠ 0 := by simpa using hb
    exact WP.seq (WP.mono (copyKey_ok hpre hf hP.hD' hk h1) fun s2 h2 => rpp_ok hP hc h2)
  · exact decode_ok hP hc h1

end VG.Proof.MlDsa.X86_64.Sign
