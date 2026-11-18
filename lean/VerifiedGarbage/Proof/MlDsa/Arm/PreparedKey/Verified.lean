module

public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Inst
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlDsa.Arm.Pack.Unpack
import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Rel
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.SignCT
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Arm.Inline
public import VerifiedGarbage.Proof.Argon2.Arm.Push
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseD
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Blocks
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Top
public import VerifiedGarbage.Impl.MlDsa.Arm.PreparedKey
public import VerifiedGarbage.Proof.MlDsa.PreparedKey.Values
public import VerifiedGarbage.Proof.MlDsa.PreparedKeyContract
meta import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Rel
meta import VerifiedGarbage.Proof.MlDsa.Arm.Sign.SignCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.Arm.Frame
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.Arm.Inline
meta import VerifiedGarbage.Proof.Argon2.Arm.Push
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseD
meta import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Blocks
meta import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Top
meta import VerifiedGarbage.Impl.MlDsa.Arm.PreparedKey
meta import VerifiedGarbage.Proof.MlDsa.PreparedKey.Values
meta import VerifiedGarbage.Proof.MlDsa.PreparedKeyContract

/-! ### `MlDsa.Arm.PreparedKey.CT`, which only this module used -/

section

/-! ### `MlDsa.Arm.PreparedKey.Entry`, which this module and modules that import it used -/

section

/-! ### `MlDsa.Arm.PreparedKey.Body`, which this module and modules that import it used -/

section

/-!
# ML-DSA on ARMv7, preparing keys: the body

In the layout of the key (`r4`, read) and of `prepared` and `scratch`
(`r8` and `r7`, written): the copy of the key to `prepared`, then each
polynomial unpacked to its place after it and transformed there
(`publicPoly_ok`, `secretPoly_ok`), so that after the loop `prepared` holds
the prepared key (`public_body`, `secret_body`), as on AArch64. The call of
`vg_mldsa_unpack_t1` is proven as the signing function's calls are
(`t1At_ok`, in `Sign/PrimsC.lean`'s style).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable {D : Nat} {rbs wbs : List (Reg × Nat)}

theorem t1Args_ok {v f : Ptr} (b1 : v.1 ∈ bases) (b2 : f.1 ∈ bases) : [Arg.ptr v, .ptr f].all Arg.ok = true := by
  simp [Arg.ok, b1, b2]

theorem t1Pre {S : Nat} {s E : State} (En : Ent D rbs wbs s S E) {v f : Ptr}
    (hc : rwChk (rbs ++ wbs) wbs v 320 f 1024 = true)
    (g0 : E.gpr .r0 = s.gpr v.1 + BitVec.ofNat 32 v.2) (g1 : E.gpr .r1 = s.gpr f.1 + BitVec.ofNat 32 f.2)
    (hrd : E.rd = [⟨pa s v, 320⟩]) (hwr : E.wr = [pR (pa s f)]) :
    (unpackT1Contract Arm.abi S).pre E := by
  obtain ⟨_, i1, i2, d12, _⟩ := rwChk_spec hc
  sig_pre [unpackT1Contract, unpackT1Sig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [g0, g1, En.L.w i1 (by decide), En.L.w i2 (by decide)]
  exact ⟨wf0 En.wf, hrd, hwr, En.L.disj d12, En.conj (bs := [(v, 320), (f, 1024)]) (by simp [i1, i2]),
    En.L.fit i1 (by decide), En.L.fit i2 (by decide)⟩

theorem t1At_ok {n : String} {c : Prog isa} (C : Callee (fun S => unpackT1Contract Arm.abi S) 0 D c)
    {s : State} (L : Lay D rbs wbs s) {v f : Ptr} (hc : rwChk (rbs ++ wbs) wbs v 320 f 1024 = true) :
    WP isa (callR n c [.ptr v, .ptr f]) s fun s' => PPostB D s s' [(f, 1024)] ∧ CS s s' ∧
      PolyIs s'.mem (pa s f) ((simpleBitUnpack (bytesAt s.mem (pa s v) 320) t1Max).map
        fun c => ofInt (c * 2 ^ d : Nat)) := by
  obtain ⟨w1, i1, i2, _, b1, b2⟩ := rwChk_spec hc
  refine WP.mono (callR_ok C.ver.1 (by have := C.su; have := C.hS; omega_arith) (t1Args_ok b1 b2) L.sp
    (rd := [⟨pa s v, 320⟩]) (wr := [pR (pa s f)])
    (fun s1 hA k => t1Pre (ent_R L k (by have := C.hS; omega_using [this]) _ _) hc
      (by rw [vR _ _ _ nl0]; exact (argsIn2 hA).1) (by rw [vR _ _ _ nl1]; exact (argsIn2 hA).2) rfl rfl)
    (Covers.append_left (L.cR i1) (Covers.right (L.cW w1))) (L.cW w1))
    fun s' ⟨hpost, hcs, s1, hA, k, hq⟩ => ⟨hpost, hcs, ?_⟩
  obtain ⟨e1, e2⟩ := argsIn2 hA
  sig_post [unpackT1Contract, unpackT1Sig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hq
  simp only [e1, e2, Arg.val, k.mem, L.w i1 (by decide), L.w i2 (by decide)] at hq
  exact hq

theorem t1At_tr {n : String} {c : Prog isa} (C : Callee (fun S => unpackT1Contract Arm.abi S) 0 D c)
    {v f : Ptr} (hc : rwChk (rbs ++ wbs) wbs v 320 f 1024 = true) :
    RelCT isa (LRel D rbs wbs) (callR n c [.ptr v, .ptr f]) fun _ _ => True := by
  obtain ⟨w1, i1, i2, _, b1, b2⟩ := rwChk_spec hc
  have hS : C.S ≤ D := by have := C.hS; omega_using [this]
  refine callR_tr C.ver.1 C.ver.2.1 (t1Args_ok b1 b2) fun x y x1 y1 R ⟨hAx, kx⟩ ⟨hAy, ky⟩ =>
    ⟨_, _, _, _, t1Pre (ent_R R.lx kx hS [⟨pa x v, 320⟩] [pR (pa x f)]) hc
      (by rw [vR _ _ _ nl0]; exact (argsIn2 hAx).1) (by rw [vR _ _ _ nl1]; exact (argsIn2 hAx).2) rfl rfl,
      t1Pre (ent_R R.ly ky hS [⟨pa y v, 320⟩] [pR (pa y f)]) hc
      (by rw [vR _ _ _ nl0]; exact (argsIn2 hAy).1) (by rw [vR _ _ _ nl1]; exact (argsIn2 hAy).2) rfl rfl, ?_,
      by rw [kx.rd, kx.wr]; exact Covers.append_left (R.lx.cR i1) (Covers.right (R.lx.cW w1)),
      by rw [kx.wr]; exact R.lx.cW w1,
      by rw [ky.rd, ky.wr]; exact Covers.append_left (R.ly.cR i1) (Covers.right (R.ly.cW w1)),
      by rw [ky.wr]; exact R.ly.cW w1⟩
  obtain ⟨hx1, hx2⟩ := argsIn2 hAx
  obtain ⟨hy1, hy2⟩ := argsIn2 hAy
  sig_pub [unpackT1Contract, unpackT1Sig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [kx.sp, ky.sp, hx1, hx2, hy1, hy2, Arg.val, R.eq i1, R.eq i2, R.sp, and_self]

end

end VG.Proof.MlDsa.Arm.Sign


namespace VG.Proof.MlDsa.Arm.PreparedKey

open VG VG.Arm VG.Spec.MlDsa
open VG.Impl.MlDsa.Arm.PreparedKey
open VG.Impl.MlDsa.Arm.Sign (Prims Ptr Arg callR callS copy seqR)
open VG.Proof.MlDsa.Arm.Sign
open VG.Spec.Sha3 (bytesAt)

/-! ## The layout -/

/-- The key. -/
abbrev input (bytes : Nat) : List (Reg × Nat) := [(.r4, bytes)]
/-- `prepared` and `scratch`. -/
abbrev output (bytes count : Nat) : List (Reg × Nat) := [(.r8, bytes + 1024 * count), (.r7, 1024)]

section
variable (bytes count : Nat)

theorem in4 (o len : Nat) : inB (input bytes ++ output bytes count) (.r4, o) len = decide (o + len ≤ bytes) := rfl
theorem in8 (o len : Nat) :
    inB (input bytes ++ output bytes count) (.r8, o) len = decide (o + len ≤ bytes + 1024 * count) := rfl
theorem in7 (o len : Nat) : inB (input bytes ++ output bytes count) (.r7, o) len = decide (o + len ≤ 1024) := rfl
theorem out8 (o len : Nat) : inB (output bytes count) (.r8, o) len = decide (o + len ≤ bytes + 1024 * count) := rfl
theorem out7 (o len : Nat) : inB (output bytes count) (.r7, o) len = decide (o + len ≤ 1024) := rfl

theorem sep4_8 (o len o' len' : Nat) :
    sepB (input bytes ++ output bytes count) (.r4, o) len (.r8, o') len' =
      (decide (o + len ≤ bytes) && decide (o' + len' ≤ bytes + 1024 * count)) := by
  unfold sepB; rw [in4, in8]; cases decide (o + len ≤ bytes) <;> cases decide (o' + len' ≤ bytes + 1024 * count) <;> rfl

theorem sep4_7 (o len o' len' : Nat) :
    sepB (input bytes ++ output bytes count) (.r4, o) len (.r7, o') len' =
      (decide (o + len ≤ bytes) && decide (o' + len' ≤ 1024)) := by
  unfold sepB; rw [in4, in7]; cases decide (o + len ≤ bytes) <;> cases decide (o' + len' ≤ 1024) <;> rfl

theorem sep8_7 (o len o' len' : Nat) :
    sepB (input bytes ++ output bytes count) (.r8, o) len (.r7, o') len' =
      (decide (o + len ≤ bytes + 1024 * count) && decide (o' + len' ≤ 1024)) := by
  unfold sepB; rw [in8, in7]; cases decide (o + len ≤ bytes + 1024 * count) <;> cases decide (o' + len' ≤ 1024) <;> rfl

theorem sep8_8 (o len o' len' : Nat) :
    sepB (input bytes ++ output bytes count) (.r8, o) len (.r8, o') len' =
      (decide (o + len ≤ bytes + 1024 * count) && decide (o' + len' ≤ bytes + 1024 * count) &&
        (decide (o + len ≤ o') || decide (o' + len' ≤ o))) := by
  unfold sepB; rw [in8, in8]; simp

end

/-! ## Checks -/

theorem ip_check (bytes count : Nat) {o : Nat} (h : o + 1024 ≤ bytes + 1024 * count) :
    ipChkW (input bytes ++ output bytes count) (output bytes count) (.r8, o) (.r7, 0) = true := by
  simp only [ipChkW, sep8_7, in8, in7, out8, out7, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨h, by decide⟩, h⟩, by decide⟩, ⟨h, by decide⟩⟩, by decide⟩, by decide⟩

theorem rw_check (bytes count : Nat) {src len o : Nat} (h1 : src + len ≤ bytes) (h2 : o + 1024 ≤ bytes + 1024 * count) :
    rwChk (input bytes ++ output bytes count) (output bytes count) (.r4, src) len (.r8, o) 1024 = true := by
  simp only [rwChk, sep4_8, in4, in8, out8, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨h2, h1⟩, h2⟩, h1, h2⟩, by decide⟩, by decide⟩

theorem copy_check (bytes count : Nat) (h : 0 < bytes) :
    copyChk (input bytes ++ output bytes count) (output bytes count) (.r8, 0) (.r4, 0) bytes = true := by
  simp only [copyChk, sep4_8, in4, out8, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨by omega_using [], by omega_using []⟩, by omega_using [], by omega_using []⟩, h⟩, by decide⟩, by decide⟩

theorem keep_source (bytes count : Nat) {i : Nat} (hi : i < count) :
    keepB (input bytes ++ output bytes count) [((.r8, bytes + 1024 * i), 1024), ((.r7, 0), 1024)] (.r4, 0) bytes =
      true := by
  simp only [keepB, List.all_cons, List.all_nil, Bool.and_true, sep4_8, sep4_7, in4, Bool.and_eq_true,
    decide_eq_true_eq, bases, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_true, or_false,
    true_and]
  omega_using [hi]

theorem keep_prefix (bytes count : Nat) {i : Nat} (hi : i < count) :
    keepB (input bytes ++ output bytes count) [((.r8, bytes + 1024 * i), 1024), ((.r7, 0), 1024)] (.r8, 0) bytes =
      true := by
  simp only [keepB, List.all_cons, List.all_nil, Bool.and_true, sep8_8, sep8_7, in8, Bool.and_eq_true,
    Bool.or_eq_true, decide_eq_true_eq, bases, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_true, or_false,
    true_and]
  omega_using [hi]

theorem keep_prior (bytes count : Nat) {i j : Nat} (hi : i < count) (hj : j < i) :
    keepB (input bytes ++ output bytes count) [((.r8, bytes + 1024 * i), 1024), ((.r7, 0), 1024)]
      (.r8, bytes + 1024 * j) 1024 = true := by
  simp only [keepB, List.all_cons, List.all_nil, Bool.and_true, sep8_8, sep8_7, in8, Bool.and_eq_true,
    Bool.or_eq_true, decide_eq_true_eq, bases, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_true, or_false,
    true_and]
  omega_using [hi, hj]

theorem keep_copy (bytes count : Nat) :
    keepB (input bytes ++ output bytes count) [((.r8, 0), bytes)] (.r4, 0) bytes = true := by
  simp only [keepB, List.all_cons, List.all_nil, Bool.and_true, sep4_8, in4, Bool.and_eq_true, decide_eq_true_eq, bases, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_true, or_false,
    true_and]
  omega_using []

/-! ## The polynomials -/

/-- Each preparation slice decodes the specified secret polynomial. -/
theorem secret_value (p : Params) (key : List Byte) {i : Nat} (hi : i < p.ℓ + 2 * p.k) :
    let (src, len, a, b) := secretPiece p i
    ntt (toRq (bitUnpack ((key.drop src).take len) a b)) = (preparedSecretPolys p key)[i]! := by
  have hlen : secretLen p = VG.Proof.MlDsa.Sign.lenS p := rfl
  by_cases h1 : i < p.ℓ
  · rw [PreparedKey.secret_s1 p key h1]
    simp only [secretPiece, ite_eq_left (show i < p.ℓ + p.k by omega_using [h1]), hlen]
    rfl
  · by_cases h2 : i < p.ℓ + p.k
    · have hj : i - p.ℓ < p.k := by omega_using [h1, h2]
      have he : p.ℓ + (i - p.ℓ) = i := by omega_using [h1]
      rw [← he, PreparedKey.secret_s2 p key hj]
      simp only [secretPiece, ite_eq_left (show p.ℓ + (i - p.ℓ) < p.ℓ + p.k by omega_using [h1, h2]), hlen]
      unfold VG.Proof.MlDsa.Sign.s2F
      rw [Nat.mul_add]
      congr 5 <;> omega_using []
    · have hj : i - (p.ℓ + p.k) < p.k := by omega_using [hi, h1]
      have he : p.ℓ + p.k + (i - (p.ℓ + p.k)) = i := by omega_using [h2]
      rw [← he, PreparedKey.secret_t0 p key hj]
      simp only [secretPiece, ite_eq_right (show ¬ p.ℓ + p.k + (i - (p.ℓ + p.k)) < p.ℓ + p.k by omega_using []), hlen]
      unfold VG.Proof.MlDsa.Sign.t0F
      have hoff : 128 + VG.Proof.MlDsa.Sign.lenS p * (p.ℓ + p.k) +
          416 * (p.ℓ + p.k + (i - (p.ℓ + p.k)) - p.ℓ - p.k) =
          128 + VG.Proof.MlDsa.Sign.lenS p * p.ℓ + VG.Proof.MlDsa.Sign.lenS p * p.k +
            32 * d * (i - (p.ℓ + p.k)) := by
        rw [Nat.mul_add]
        simp only [d]
        omega_using []
      rw [hoff]
      rfl

theorem bases_io (bytes count : Nat) : ∀ b ∈ input bytes ++ output bytes count, b.1 ∈ bases := by
  intro b hb
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl <;> dsimp only <;> decide

theorem w_bases (o : Nat) : ∀ w ∈ ([((.r8, o), 1024), ((.r7, 0), 1024)] : List (Ptr × Nat)), w.1.1 ∈ bases := by
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl <;> dsimp only <;> decide

section
variable {P : Prims} {D : Nat} (hP : PrimsOk P D)
  (C1 : Callee (fun S => unpackT1Contract Arm.abi S) 0 D Impl.MlDsa.Arm.Pack.unpackT1)
  {bytes count : Nat}

include hP in
/-- `NTT` of a polynomial of `prepared`, after a call that wrote it. -/
theorem transform_after {s u : State} (L : Lay D (input bytes) (output bytes count) s) {o : Nat}
    (hu : PPostB D s u [((.r8, o), 1024)]) (hcs : CS s u) {f : Poly} (hf : PolyIs u.mem (pa s (.r8, o)) f)
    (hi : ipChkW (input bytes ++ output bytes count) (output bytes count) (.r8, o) (.r7, 0) = true) :
    WP isa (transform P o) u fun t => PPostB D s t [((.r8, o), 1024), ((.r7, 0), 1024)] ∧ CS s t ∧
      PolyIs t.mem (pa s (.r8, o)) (ntt f) := by
  have hpa : pa u (.r8, o) = pa s (.r8, o) := hu.pa (show Reg.r8 ∈ bases by decide)
  rw [← hpa] at hf
  refine WP.mono (ipAtW_ok (t := ntt) hP.ntt (L.post hu (bases_io _ _)) hi hf.1) fun t ⟨ht, hct, htp⟩ => ?_
  refine ⟨hu.trans ht (w_bases o) (by simp) (by simp), hcs.trans hct, ?_⟩
  rw [hf.2, hpa] at htp; exact htp

include hP C1 in
theorem publicPoly_ok {s : State} (L : Lay D (input bytes) (output bytes count) s) {p : Params} {i : Nat}
    (hc : rwChk (input bytes ++ output bytes count) (output bytes count) (.r4, 32 + 320 * i) 320
      (.r8, p.pkLen + 1024 * i) 1024 = true)
    (hi : ipChkW (input bytes ++ output bytes count) (output bytes count) (.r8, p.pkLen + 1024 * i) (.r7, 0) = true) :
    WP isa (publicPoly P p i) s fun t =>
      PPostB D s t [((.r8, p.pkLen + 1024 * i), 1024), ((.r7, 0), 1024)] ∧ CS s t ∧
      PolyIs t.mem (pa s (.r8, p.pkLen + 1024 * i))
        (ntt ((simpleBitUnpack (bytesAt s.mem (pa s (.r4, 32 + 320 * i)) 320) t1Max).map
          fun c => ofInt (c * 2 ^ d : Nat))) := by
  unfold publicPoly
  exact WP.seq (WP.mono (t1At_ok C1 L hc) fun u ⟨hu, hcs, hp⟩ => transform_after hP L hu hcs hp hi)

include hP in
theorem secretPoly_ok {s : State} (L : Lay D (input bytes) (output bytes count) s) {p : Params} {i : Nat}
    {src len a b : Nat} (he : secretPiece p i = (src, len, a, b))
    (hab : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b))
    (hc : rwChk (input bytes ++ output bytes count) (output bytes count) (.r4, src) len
      (.r8, p.skLen + 1024 * i) 1024 = true)
    (hi : ipChkW (input bytes ++ output bytes count) (output bytes count) (.r8, p.skLen + 1024 * i) (.r7, 0) = true) :
    WP isa (secretPoly P p i) s fun t =>
      PPostB D s t [((.r8, p.skLen + 1024 * i), 1024), ((.r7, 0), 1024)] ∧ CS s t ∧
      PolyIs t.mem (pa s (.r8, p.skLen + 1024 * i)) (ntt (toRq (bitUnpack (bytesAt s.mem (pa s (.r4, src)) len) a b))) := by
  unfold secretPoly
  rw [he]
  exact WP.seq (WP.mono (bupAt_ok hP L hab hl hc) fun u ⟨hu, hcs, hp⟩ => transform_after hP L hu hcs hp hi)

end

/-! ## The loops -/

/-- One of the parameter sets of Table 1. -/
abbrev Ok3 (p : Params) : Prop := p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87

theorem pk_eq {p : Params} (hp : Ok3 p) : p.pkLen = 32 + 320 * p.k := by rcases hp with rfl | rfl | rfl <;> rfl

theorem public_checks {p : Params} (hp : Ok3 p) {i : Nat} (hi : i < p.k) :
    rwChk (input p.pkLen ++ output p.pkLen p.k) (output p.pkLen p.k) (.r4, 32 + 320 * i) 320
      (.r8, p.pkLen + 1024 * i) 1024 = true ∧
    ipChkW (input p.pkLen ++ output p.pkLen p.k) (output p.pkLen p.k) (.r8, p.pkLen + 1024 * i) (.r7, 0) = true := by
  have := pk_eq hp
  exact ⟨rw_check _ _ (by omega_using [hi, this]) (by omega_using [hi]), ip_check _ _ (by omega_using [hi])⟩

theorem secret_checks {p : Params} (hp : Ok3 p) {i : Nat} (hi : i < p.ℓ + 2 * p.k) :
    let (src, len, a, b) := secretPiece p i
    rwChk (input p.skLen ++ output p.skLen (p.ℓ + 2 * p.k)) (output p.skLen (p.ℓ + 2 * p.k)) (.r4, src) len
      (.r8, p.skLen + 1024 * i) 1024 = true ∧ (a, b) ∈ bitPackParams ∧ len = 32 * bitlen (a + b) := by
  have hs44 : secretLen mlDsa44 = 96 := by decide
  have hs65 : secretLen mlDsa65 = 128 := by decide
  have hs87 : secretLen mlDsa87 = 96 := by decide
  have hk44 : mlDsa44.skLen = 2560 := by decide
  have hk65 : mlDsa65.skLen = 4032 := by decide
  have hk87 : mlDsa87.skLen = 4896 := by decide
  rcases hp with rfl | rfl | rfl <;>
    dsimp only [secretPiece] <;> split <;>
    simp only [hs44, hs65, hs87, hk44, hk65, hk87, mlDsa44, mlDsa65, mlDsa87] at * <;>
    exact ⟨rw_check _ _ (by omega_using [hi]) (by omega_using [hi]), by decide, by decide⟩

/-- The regions the preparation writes. -/
def writes (bytes count : Nat) : List (Ptr × Nat) :=
  [((.r8, 0), bytes), ((.r7, 0), 1024)] ++ (List.range count).map fun i => ((.r8, bytes + 1024 * i), 1024)

/-- After the polynomials before `done`: `prepared` begins with the key `key`
and holds the polynomials `f i` after it. -/
structure Inv (D bytes count : Nat) (f : Nat → Poly) (σ : State) (key : List Byte) (done : Nat) (s : State) : Prop where
  lay : Lay D (input bytes) (output bytes count) s
  post : PPostB D σ s (writes bytes count)
  cs : CS σ s
  source : bytesAt s.mem (pa s (.r4, 0)) bytes = key
  encoded : bytesAt s.mem (pa s (.r8, 0)) bytes = key
  polys : ∀ i < done, PolyIs s.mem (pa s (.r8, bytes + 1024 * i)) (f i)

theorem inv_step {D bytes count : Nat} {f : Nat → Poly} {σ s : State} {key : List Byte} {i : Nat} (hi : i < count)
    (h : Inv D bytes count f σ key i s) {c : Prog isa}
    (hc : WP isa c s fun t => PPostB D s t [((.r8, bytes + 1024 * i), 1024), ((.r7, 0), 1024)] ∧ CS s t ∧
      PolyIs t.mem (pa s (.r8, bytes + 1024 * i)) (f i)) :
    WP isa c s (Inv D bytes count f σ key (i + 1)) := by
  refine WP.mono hc fun t ⟨ht, hct, hpoly⟩ => ?_
  refine ⟨h.lay.post ht (bases_io _ _), ?_, h.cs.trans hct, ?_, ?_, ?_⟩
  · refine h.post.trans ht (w_bases _) (fun _ hw => hw) ?_
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact List.mem_append_right _ (List.mem_map_of_mem (List.mem_range.mpr hi))
    · simp [writes]
  · rw [h.lay.keepBytes ht (keep_source bytes count hi)]
    exact h.source
  · rw [h.lay.keepBytes ht (keep_prefix bytes count hi)]
    exact h.encoded
  · intro j hj
    by_cases he : j = i
    · subst j
      rw [ht.pa (p := (.r8, bytes + 1024 * i)) (show Reg.r8 ∈ bases by decide)]
      exact hpoly
    · exact h.lay.keepPoly ht (keep_prior bytes count hi (by omega_using [hj, he])) (h.polys j (by omega_using [hj, he]))

/-- The copy of the key to `prepared`. -/
theorem copy_inv {D bytes count : Nat} (f : Nat → Poly) (hb : 0 < bytes) (s : State)
    (L : Lay D (input bytes) (output bytes count) s) :
    WP isa (copy (.r8, 0) (.r4, 0) bytes) s (Inv D bytes count f s (bytesAt s.mem (pa s (.r4, 0)) bytes) 0) := by
  refine WP.mono (copy_okB L (copy_check bytes count hb)) fun u ⟨hu, hcs, hc⟩ => ?_
  refine ⟨L.post hu (bases_io _ _), PostB.trans hu (PostB.refl D u []) (fun r hr => ?_) (fun _ h => absurd h
    List.not_mem_nil), hcs, L.keepBytes hu (keep_copy bytes count), ?_, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hr
    subst hr
    simp [writes]
  · rw [hu.pa (p := (.r8, 0)) (show Reg.r8 ∈ bases by decide)]; exact hc

section
variable {P : Prims} {D : Nat} (hP : PrimsOk P D)
  (C1 : Callee (fun S => unpackT1Contract Arm.abi S) 0 D Impl.MlDsa.Arm.Pack.unpackT1)

include hP C1 in
theorem public_body {p : Params} (hp : Ok3 p) (s : State) (L : Lay D (input p.pkLen) (output p.pkLen p.k) s) :
    WP isa (.seq (copy (.r8, 0) (.r4, 0) p.pkLen) (seqR (publicPoly P p) 0 p.k)) s fun t =>
      Inv D p.pkLen p.k (Verify.t1Hat (bytesAt s.mem (pa s (.r4, 0)) p.pkLen)) s
        (bytesAt s.mem (pa s (.r4, 0)) p.pkLen) p.k t ∧
      PreparedPublicKey p t.mem (pa t (.r8, 0)) := by
  have hpk := pk_eq hp
  refine WP.seq (WP.mono (copy_inv (Verify.t1Hat (bytesAt s.mem (pa s (.r4, 0)) p.pkLen)) (by omega_using [hpk]) s L)
    fun u hu => ?_)
  refine WP.mono (seqR_ok (I := fun i => Inv D p.pkLen p.k (Verify.t1Hat (bytesAt s.mem (pa s (.r4, 0)) p.pkLen)) s
    (bytesAt s.mem (pa s (.r4, 0)) p.pkLen) i) p.k 0 (fun i _ hi u h => ?_) u hu)
    fun t ht => ?_
  · obtain ⟨hc, hi'⟩ := public_checks hp (i := i) (by omega_using [hi])
    refine inv_step (by omega_using [hi]) h (WP.mono (publicPoly_ok hP C1 h.lay hc hi') fun t ⟨ht, hct, hpoly⟩ =>
      ⟨ht, hct, ?_⟩)
    have hslice : bytesAt u.mem (pa u (.r4, 32 + 320 * i)) 320 =
        ((bytesAt s.mem (pa s (.r4, 0)) p.pkLen).drop (32 + 320 * i)).take 320 := by
      rw [← h.source, MlKem.bytesAt_slice _ _ (by omega_using [hpk, hi])]
      simp only [pa, BitVec.add_zero]
    rw [hslice] at hpoly
    exact hpoly
  · rw [Nat.zero_add] at ht
    refine ⟨ht, preparedPublicKey_iff.2 fun i hi => ?_⟩
    rw [ht.encoded, PreparedKey.public_poly p _ hi]
    simpa only [pa, BitVec.add_zero, n] using ht.polys i hi

include hP in
theorem secret_body {p : Params} (hp : Ok3 p) (s : State)
    (L : Lay D (input p.skLen) (output p.skLen (p.ℓ + 2 * p.k)) s) :
    WP isa (.seq (copy (.r8, 0) (.r4, 0) p.skLen) (seqR (secretPoly P p) 0 (p.ℓ + 2 * p.k))) s fun t =>
      Inv D p.skLen (p.ℓ + 2 * p.k) (fun i => (preparedSecretPolys p (bytesAt s.mem (pa s (.r4, 0)) p.skLen))[i]!) s
        (bytesAt s.mem (pa s (.r4, 0)) p.skLen) (p.ℓ + 2 * p.k) t ∧
      PreparedSecretKey p t.mem (pa t (.r8, 0)) := by
  have hsk : 0 < p.skLen := by rcases hp with rfl | rfl | rfl <;> decide
  refine WP.seq (WP.mono (copy_inv (count := p.ℓ + 2 * p.k)
    (fun i => (preparedSecretPolys p (bytesAt s.mem (pa s (.r4, 0)) p.skLen))[i]!) hsk s L) fun u hu => ?_)
  refine WP.mono (seqR_ok (I := fun i => Inv D p.skLen (p.ℓ + 2 * p.k)
    (fun i => (preparedSecretPolys p (bytesAt s.mem (pa s (.r4, 0)) p.skLen))[i]!) s
    (bytesAt s.mem (pa s (.r4, 0)) p.skLen) i) (p.ℓ + 2 * p.k) 0
    (fun i _ hi u h => ?_) u hu) fun t ht => ?_
  · have hi' : i < p.ℓ + 2 * p.k := by omega_using [hi]
    obtain ⟨src, len, a, b, he⟩ : ∃ src len a b, secretPiece p i = (src, len, a, b) := by
      rcases secretPiece p i with ⟨src, len, a, b⟩
      exact ⟨src, len, a, b, rfl⟩
    have hchecks := secret_checks hp hi'
    rw [he] at hchecks
    obtain ⟨hc, hab, hl⟩ := hchecks
    have hip := ip_check p.skLen (p.ℓ + 2 * p.k) (o := p.skLen + 1024 * i) (by omega_using [hi])
    refine inv_step hi' h (WP.mono (secretPoly_ok hP h.lay he hab hl hc hip) fun t ⟨ht, hct, hpoly⟩ =>
      ⟨ht, hct, ?_⟩)
    have hbound : src + len ≤ p.skLen := by
      have := (rwChk_spec hc).2.1
      rwa [in4, decide_eq_true_eq] at this
    have hslice : bytesAt u.mem (pa u (.r4, src)) len =
        ((bytesAt s.mem (pa s (.r4, 0)) p.skLen).drop src).take len := by
      rw [← h.source, MlKem.bytesAt_slice _ _ hbound]
      simp only [pa, BitVec.add_zero]
    have hv := secret_value p (bytesAt s.mem (pa s (.r4, 0)) p.skLen) hi'
    rw [he] at hv
    rwa [hslice, hv] at hpoly
  · rw [Nat.zero_add] at ht
    refine ⟨ht, preparedSecretKey_iff.2 fun i hi => ?_⟩
    rw [ht.encoded]
    simpa only [pa, BitVec.add_zero, n] using ht.polys i hi

end

end VG.Proof.MlDsa.Arm.PreparedKey

end

end

/-!
# ML-DSA on ARMv7, preparing keys: the entry

The precondition of the contracts, spelled out (`EntryPre`); the frame
saving `r4`, `r7`, `r8` and `lr`, and the moves of the arguments, after which
the buffers are a layout (`entry_lay`); and the loads and the pop that
restore the registers saved, so that a body that prepares the key prepares
it in `prepared` and keeps the registers the ABI preserves (`entry_correct`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.PreparedKey

open VG VG.Arm VG.Spec.MlDsa
open VG.Impl.MlDsa.Arm.PreparedKey
open VG.Impl.MlDsa.Arm.Sign (Prims Ptr)
open VG.Proof.MlDsa.Arm.Sign
open VG.Spec.Sha3 (bytesAt)

/-- The stack of the calls of the body. -/
abbrev callStack : Nat := 28

/-- The stack of the preparations: their frame (16 bytes) and that of the calls,
44 bytes, to the next frame size of the model (which a function that returns
without secret residue wipes: `Arm.Scrub.scrubRegF`). -/
abbrev prepStack : Nat := 48

/-- The precondition of `preparePublicKeyContract` and `prepareSecretKeyContract`,
for a key of `bytes` bytes and `count` polynomials. -/
structure EntryPre (bytes count : Nat) (s : State) : Prop where
  stk : prepStack ≤ s.sp.toNat
  rd : s.rd = [⟨State.addr (s.gpr .r0), bytes⟩]
  wr : s.wr = [⟨State.addr (s.gpr .r1), bytes + 1024 * count⟩, ⟨State.addr (s.gpr .r2), 1024⟩]
  io : Region.Disjoint ⟨State.addr (s.gpr .r0), bytes⟩ ⟨State.addr (s.gpr .r1), bytes + 1024 * count⟩
  it : Region.Disjoint ⟨State.addr (s.gpr .r0), bytes⟩ ⟨State.addr (s.gpr .r2), 1024⟩
  ot : Region.Disjoint ⟨State.addr (s.gpr .r1), bytes + 1024 * count⟩ ⟨State.addr (s.gpr .r2), 1024⟩
  si : (Argon2.Arm.stkR s.sp prepStack).Disjoint ⟨State.addr (s.gpr .r0), bytes⟩
  so : (Argon2.Arm.stkR s.sp prepStack).Disjoint ⟨State.addr (s.gpr .r1), bytes + 1024 * count⟩
  st : (Argon2.Arm.stkR s.sp prepStack).Disjoint ⟨State.addr (s.gpr .r2), 1024⟩
  ni : (s.gpr .r0).toNat + bytes ≤ 2 ^ 32
  no : (s.gpr .r1).toNat + (bytes + 1024 * count) ≤ 2 ^ 32
  nt : (s.gpr .r2).toNat + 1024 ≤ 2 ^ 32

theorem publicBytes_eq (p : Params) : preparedPublicKeyBytes p = p.pkLen + 1024 * p.k := by
  unfold preparedPublicKeyBytes n; omega_using []

theorem secretBytes_eq (p : Params) : preparedSecretKeyBytes p = p.skLen + 1024 * (p.ℓ + 2 * p.k) := by
  unfold preparedSecretKeyBytes n; omega_using []

theorem public_pre {p : Params} {s : State} (h : (preparePublicKeyContract p Arm.abi prepStack).pre s) :
    EntryPre p.pkLen p.k s := by
  sig_pre [preparePublicKeyContract, preparePublicKeySig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  rw [publicBytes_eq] at h
  obtain ⟨h0, -, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

theorem secret_pre {p : Params} {s : State} (h : (prepareSecretKeyContract p Arm.abi prepStack).pre s) :
    EntryPre p.skLen (p.ℓ + 2 * p.k) s := by
  sig_pre [prepareSecretKeyContract, prepareSecretKeySig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  rw [secretBytes_eq] at h
  obtain ⟨h0, -, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

/-! ## The moves of the arguments -/

/-- The registers saved. -/
abbrev saved : List Reg := [.r4, .r7, .r8, .lr]

theorem movs_ok (s : State) :
    WP isa (.block [.mov .r4 (.reg .r0), .mov .r8 (.reg .r1), .mov .r7 (.reg .r2)]) s fun u =>
      u.gpr .r4 = s.gpr .r0 ∧ u.gpr .r8 = s.gpr .r1 ∧ u.gpr .r7 = s.gpr .r2 ∧
      (∀ r, r ≠ .r4 → r ≠ .r8 → r ≠ .r7 → u.gpr r = s.gpr r) ∧ u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧
      u.sp = s.sp := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, Op2.eval,
    Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg,
    RegUpd.wr_setReg, RegUpd.sp_setReg, ↓reduceIte, reduceCtorEq, and_self]
  exact ⟨trivial, trivial, trivial, fun r h4 h8 h7 => by simp only [h4, h8, h7, ite_false], trivial⟩

section
variable {bytes count : Nat} {σ : State} (h : EntryPre bytes count σ)
include h

theorem h16 : 16 ≤ σ.sp.toNat := by have := h.stk; simp only [prepStack] at this; omega_using [this]

/-- The frame, below `σ`'s stack pointer. -/
theorem frame_sub : Region.Sub (Argon2.Arm.stkR σ.sp 16) (Argon2.Arm.stkR σ.sp prepStack) :=
  Argon2.Arm.stkR_sub (by decide) h.stk

/-- The buffers, in `σ`. -/
theorem buf_disj {u : State} (h4 : u.gpr .r4 = σ.gpr .r0) (h8 : u.gpr .r8 = σ.gpr .r1)
    (h7 : u.gpr .r7 = σ.gpr .r2) :
    ∀ b ∈ input bytes ++ output bytes count,
      (Argon2.Arm.stkR σ.sp prepStack).Disjoint ⟨State.addr (u.gpr b.1), b.2⟩ := by
  intro b hb
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl
  · rw [h4]; exact h.si
  · rw [h8]; exact h.so
  · rw [h7]; exact h.st

/-- After the push and the moves, the buffers are a layout. -/
theorem entry_lay (hb : bytes < 2 ^ 32) (ho : bytes + 1024 * count < 2 ^ 32) {u : State}
    (h4 : u.gpr .r4 = σ.gpr .r0) (h8 : u.gpr .r8 = σ.gpr .r1) (h7 : u.gpr .r7 = σ.gpr .r2)
    (hsp : u.sp = σ.sp - BitVec.ofNat 32 16) (hrd : u.rd = σ.rd)
    (hwr : u.wr = ⟨State.addr (σ.sp - BitVec.ofNat 32 16), 16⟩ :: σ.wr) :
    Lay callStack (input bytes) (output bytes count) u := by
  have h16 := h16 h
  have hst : Region.Sub (belowA u.sp callStack) (Argon2.Arm.stkR σ.sp prepStack) := by
    rw [hsp]; exact Argon2.Arm.stkR_inner (by decide) h.stk
  have mem : ∀ R ∈ σ.rd ++ σ.wr, InRegions (u.rd ++ u.wr) R.base R.len := fun R hR =>
    ⟨R, by
      rw [hrd, hwr]
      rcases List.mem_append.mp hR with hR | hR
      · exact List.mem_append_left _ hR
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hR), Region.contains_self _ _⟩
  refine ⟨?_, ?_, fun b hb => ((buf_disj h h4 h8 h7) b hb).sub_left hst, ?_, ?_, ?_, ?_⟩
  · intro b hb'
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb'
    rcases hb' with rfl | rfl | rfl
    exacts [hb, ho, by decide]
  · intro b hb' b' hb'' hne _
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb' hb''
    rcases hb' with rfl | rfl | rfl <;> rcases hb'' with rfl | rfl | rfl <;>
      first
      | exact absurd rfl hne
      | simp only [h4, h8, h7]
        first | exact h.io | exact h.it | exact h.ot | exact h.io.symm | exact h.it.symm | exact h.ot.symm
  · intro b hb'
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb'
    rcases hb' with rfl | rfl | rfl <;> simp only [h4, h8, h7]
    exacts [h.ni, h.no, h.nt]
  · intro b hb'
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb'
    rcases hb' with rfl | rfl | rfl <;> simp only [h4, h8, h7]
    · exact mem ⟨State.addr (σ.gpr .r0), bytes⟩ (by rw [h.rd, h.wr]; simp)
    · exact mem ⟨State.addr (σ.gpr .r1), bytes + 1024 * count⟩ (by rw [h.rd, h.wr]; simp)
    · exact mem ⟨State.addr (σ.gpr .r2), 1024⟩ (by rw [h.rd, h.wr]; simp)
  · intro b hb'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb'
    rcases hb' with rfl | rfl <;> simp only [h8, h7] <;>
      exact ⟨_, by rw [hwr, h.wr]; simp, Region.contains_self _ _⟩
  · rw [hsp, FrameStack.sub_toNat' (by omega_using [h16])]
    have := h.stk; simp only [prepStack, callStack] at this ⊢; omega_using [this]

/-- The word `i` of the frame. -/
theorem word_sub {i : Nat} (hi : i < 4) :
    Region.Sub ⟨State.addr (σ.sp - BitVec.ofNat 32 16 + BitVec.ofNat 32 (4 * i)), 4⟩ (Argon2.Arm.stkR σ.sp 16) := by
  have h16 := h16 h
  have e : State.addr (σ.sp - BitVec.ofNat 32 16 + BitVec.ofNat 32 (4 * i)) =
      (State.addr σ.sp - BitVec.ofNat 64 16) + BitVec.ofNat 64 (4 * i) := by
    rw [addr_add (by rw [FrameStack.sub_toNat' h16]; have := σ.sp.isLt; omega_using [hi]), FrameStack.addr_sub' h16]
  rw [e]
  exact Offset.sub_base _ (by omega_using [hi])

end

/-! ## The loads of the registers saved -/

theorem ldrSp_ok (r : Reg) {off : Nat} (ho : off < 4096) (s : State)
    (hA : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 off)) 4) :
    WP isa (.block [.ldrSp r off]) s (· = s.setReg r (s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 off)) 32)) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, State.load32, hA, ho, ↓reduceIte,
    Option.map_some, Option.some.injEq, exists_eq_left']

/-- The address of word `i` of the frame. -/
theorem word_addr {sp : BitVec 32} (h16 : 16 ≤ sp.toNat) {i : Nat} (hi : i < 4) :
    State.addr (sp - BitVec.ofNat 32 16 + BitVec.ofNat 32 (4 * i)) =
      State.addr (sp - BitVec.ofNat 32 16) + BitVec.ofNat 64 (4 * i) :=
  addr_add (by rw [FrameStack.sub_toNat' h16]; have := sp.isLt; omega_using [hi])

/-! ## The entry -/

theorem entry_correct {body : Prog isa} {bytes count : Nat} {B : Mem → Addr → Prop}
    (W : State → List Region) (hb : bytes < 2 ^ 32) (ho : bytes + 1024 * count < 2 ^ 32)
    (hW : ∀ u, ∀ R ∈ W u, ∃ b ∈ input bytes ++ output bytes count, Region.Sub R ⟨State.addr (u.gpr b.1), b.2⟩)
    (hbody : ∀ u, Lay callStack (input bytes) (output bytes count) u → WP isa body u fun t =>
      PostB callStack u t (W u) ∧ CS u t ∧
      bytesAt t.mem (pa t (.r8, 0)) bytes = bytesAt u.mem (pa u (.r4, 0)) bytes ∧ B t.mem (pa t (.r8, 0)))
    (hBl : ∀ m m' a, bytesAt m' a (bytes + 1024 * count) = bytesAt m a (bytes + 1024 * count) → B m a → B m' a)
    {σ : State} (h : EntryPre bytes count σ) :
    WP isa (entry body) σ fun s' => abiPreserved σ s' ∧
      bytesAt s'.mem (State.addr (σ.gpr .r1)) bytes = bytesAt σ.mem (State.addr (σ.gpr .r0)) bytes ∧
      B s'.mem (State.addr (σ.gpr .r1)) := by
  have h16 := h16 h
  unfold entry
  refine WP.frame (rs := saved) (r := .r4) (by decide) (by simp only [List.length_cons, List.length_nil]; omega_using [h16])
    (by decide) ?_
  refine WP.seq (WP.mono (movs_ok _) fun u ⟨g4, g8, g7, g, gm, grd, gwr, gsp⟩ => ?_)
  have u4 : u.gpr .r4 = σ.gpr .r0 := by rw [g4, pushed_gpr]
  have u8 : u.gpr .r8 = σ.gpr .r1 := by rw [g8, pushed_gpr]
  have u7 : u.gpr .r7 = σ.gpr .r2 := by rw [g7, pushed_gpr]
  have usp : u.sp = σ.sp - BitVec.ofNat 32 16 := by rw [gsp, pushed_sp]; rfl
  have urd : u.rd = σ.rd := by rw [grd, pushed_rd]
  have uwr : u.wr = ⟨State.addr (σ.sp - BitVec.ofNat 32 16), 16⟩ :: σ.wr := by rw [gwr, pushed_wr]; rfl
  have L := entry_lay h hb ho u4 u8 u7 usp urd uwr
  refine WP.seq (WP.mono (hbody u L) fun t ⟨hP, hcs, henc, hB⟩ => ?_)
  have umem : u.mem = storeWords σ.mem (σ.sp - BitVec.ofNat 32 16) (saved.map σ.gpr) := gm
  -- The words of the frame are kept.
  have word : ∀ i (hi : i < 4), t.mem.readW (State.addr (σ.sp - BitVec.ofNat 32 16 + BitVec.ofNat 32 (4 * i))) 32 =
      (saved.map σ.gpr)[i]'(by simpa using hi) := by
    intro i hi
    rw [hP.frame.readW (Region.contains_self _ _) ?_ (by decide), umem]
    · exact Argon2.Arm.storeWords_readW _ _ _ (by rw [FrameStack.sub_toNat' h16]; have := σ.sp.isLt; simp; omega_using [])
        (by simpa using hi)
    · intro R hR
      have ws := word_sub h hi
      rcases List.mem_append.mp hR with hR | hR
      · obtain ⟨b, hb', hsub⟩ := hW u R hR
        exact (((buf_disj h u4 u8 u7) b hb').sub_left fun x hx => frame_sub h x (ws x hx)).sub_right hsub
      · rw [List.mem_singleton] at hR; subst hR
        rw [usp, word_addr h16 hi]
        show Region.Disjoint _ ⟨State.addr (σ.sp - BitVec.ofNat 32 16) - BitVec.ofNat 64 callStack, callStack⟩
        exact Offset.disjoint_below _ (by simp only [callStack]; omega_using [hi])
  have tsp : t.sp = σ.sp - BitVec.ofNat 32 16 := hP.sp.trans usp
  have twr : t.wr = ⟨State.addr (σ.sp - BitVec.ofNat 32 16), 16⟩ :: σ.wr := hP.wr.trans uwr
  have inF : ∀ (s : State) (i : Nat), i < 4 → s.sp = σ.sp - BitVec.ofNat 32 16 →
      s.wr = ⟨State.addr (σ.sp - BitVec.ofNat 32 16), 16⟩ :: σ.wr →
      InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 (4 * i))) 4 := fun s i hi hs hw =>
    ⟨_, List.mem_append_right _ (by rw [hw]; exact List.mem_cons_self ..), by
      rw [hs, word_addr h16 hi]; exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  refine WP.seq (WP.mono (ldrSp_ok .r7 (off := 4 * 1) (by decide) t (inF t 1 (by decide) tsp twr)) fun t₁ e₁ => ?_)
  subst e₁
  refine WP.seq (WP.mono (ldrSp_ok .r8 (off := 4 * 2) (by decide) _ (inF _ 2 (by decide) tsp twr)) fun t₂ e₂ => ?_)
  subst e₂
  refine WP.mono (ldrSp_ok .lr (off := 4 * 3) (by decide) _ (inF _ 3 (by decide) tsp twr)) fun t₃ e₃ => ?_
  subst e₃
  intro mL uL hfl
  -- The prepared key is apart from the released frame.
  rw [FrameStack.addr_sub' (by simp only [List.length_cons, List.length_nil]; omega_using [h16])] at hfl
  have hdo : ∀ R ∈ [Argon2.Arm.stkR σ.sp (4 * saved.length)],
      Region.Disjoint ⟨State.addr (σ.gpr .r1), bytes + 1024 * count⟩ R := fun R hR => by
    simp only [List.mem_singleton] at hR; subst hR
    have := (buf_disj h u4 u8 u7) (.r8, bytes + 1024 * count) (by simp)
    rw [u8] at this
    exact (this.sub_left (frame_sub h)).symm
  have hLo : bytesAt mL (State.addr (σ.gpr .r1)) (bytes + 1024 * count) =
      bytesAt t.mem (State.addr (σ.gpr .r1)) (bytes + 1024 * count) :=
    VG.Proof.MlKem.bytesAt_frame hfl hdo (by omega_using [ho])
  have hLb : bytesAt mL (State.addr (σ.gpr .r1)) bytes = bytesAt t.mem (State.addr (σ.gpr .r1)) bytes :=
    VG.Proof.MlKem.bytesAt_frame hfl (fun R hR => (hdo R hR).sub_left (Region.sub_prefix (by omega_using [])))
      (by omega_using [hb])
  dsimp only
  have w0 := word 0 (by decide)
  have w1 := word 1 (by decide)
  have w2 := word 2 (by decide)
  have w3 := word 3 (by decide)
  simp only [Nat.mul_zero, BitVec.add_zero, List.map_cons, List.map_nil, List.getElem_cons_zero,
    List.getElem_cons_succ] at w0 w1 w2 w3
  simp only [RegUpd.sp_setReg, RegUpd.mem_setReg, tsp]
  rw [w1, w2, w3]
  have e8 : t.gpr .r8 = σ.gpr .r1 := (hP.bs .r8 (by decide)).trans u8
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_, ?_⟩
  all_goals try simp only [popped, RegUpd.sp_setReg, RegUpd.mem_setReg]
  · simp only [RegUpd.gpr_setReg]
    by_cases e4 : r = .r4
    · subst e4; simp only [↓reduceIte]; rw [tsp, w0]
    by_cases e7 : r = .r7
    · subst e7; simp only [↓reduceIte, reduceCtorEq]
    by_cases e8' : r = .r8
    · subst e8'; simp only [↓reduceIte, reduceCtorEq]
    by_cases el : r = .lr
    · subst el; simp only [↓reduceIte, reduceCtorEq]
    simp only [e4, e7, e8', el, ite_false]
    rw [hcs r hr el, g r e4 e8' e7, pushed_gpr]
  · rw [tsp]; exact BitVec.sub_add_cancel _ _
  · have ek : bytesAt u.mem (State.addr (σ.gpr .r0)) bytes = bytesAt σ.mem (State.addr (σ.gpr .r0)) bytes := by
      rw [gm]
      exact VG.Proof.MlKem.bytesAt_frame (Argon2.Arm.pushed_stk (rs := saved) (s := σ)
        (by simp only [List.length_cons, List.length_nil]; omega_using [h16])) (fun R hR => by
          simp only [List.mem_singleton] at hR; subst hR; exact (h.si.sub_left (frame_sub h)).symm) (by omega_using [hb])
    simp only [pa, BitVec.add_zero, e8, u4] at henc
    rw [hLb, henc, ek]
  · simp only [pa, BitVec.add_zero, e8] at hB; exact hBl _ _ _ hLo hB

end VG.Proof.MlDsa.Arm.PreparedKey

end

end

/-!
# ML-DSA on ARMv7, preparing keys: constant time

Two runs in the same layout leak the same: the copy and the calls leak only
the addresses of the buffers (`body_tr`), and the frame, the moves and the
loads of the registers saved only the stack pointer (`entry_tr`). So the
preparations leak nothing beyond their pointers and stack pointer, which is
all their contracts make public.
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.PreparedKey

open VG VG.Arm VG.Spec.MlDsa
open VG.Impl.MlDsa.Arm.PreparedKey
open VG.Impl.MlDsa.Arm.Sign (Prims Ptr callR callS copy seqR)
open VG.Proof.MlDsa.Arm.Sign
open VG.Spec.Sha3 (bytesAt)

/-! ## The body -/

section
variable {D bytes count : Nat}

/-- Two runs in the same layout. -/
abbrev Rel (D bytes count : Nat) : State → State → Prop := LRel D (input bytes) (output bytes count)

theorem copy_rel (hb : 0 < bytes) :
    RelCT isa (Rel D bytes count) (copy (.r8, 0) (.r4, 0) bytes) (Rel D bytes count) :=
  postDep (copy_tr (by decide) (by decide) fun x y R =>
      ⟨R.regs (.r8, bytes + 1024 * count) (List.mem_append_right _ (List.mem_cons_self ..)),
        R.regs (.r4, bytes) (List.mem_append_left _ (List.mem_cons_self ..))⟩)
    (fun x y R => ⟨copy_okB R.lx (copy_check bytes count hb), copy_okB R.ly (copy_check bytes count hb)⟩)
    fun _ _ _ _ R ⟨hx, _⟩ ⟨hy, _⟩ => R.post (bases_io _ _) hx hy

/-- What a call that writes a polynomial at `o` leaves for the `NTT` of it. -/
abbrev RelR (D bytes count o : Nat) (x y : State) : Prop :=
  Rel D bytes count x y ∧ Reduced x.mem (pa x (.r8, o)) ∧ Reduced y.mem (pa y (.r8, o))

theorem red_after {s s' : State} {o : Nat} {f : Poly} (hP : PPostB D s s' [((.r8, o), 1024)])
    (h : PolyIs s'.mem (pa s (.r8, o)) f) : Reduced s'.mem (pa s' (.r8, o)) := by
  rw [hP.pa (show Reg.r8 ∈ bases by decide)]; exact h.1

variable {P : Prims} (hP : PrimsOk P D)
include hP

theorem transform_rel {o : Nat}
    (hi : ipChkW (input bytes ++ output bytes count) (output bytes count) (.r8, o) (.r7, 0) = true) :
    RelCT isa (RelR D bytes count o) (transform P o) (Rel D bytes count) :=
  postDep (ipAtW_tr hP.ntt hi) (fun _ _ ⟨R, rx, ry⟩ => ⟨ipAtW_ok hP.ntt R.lx hi rx, ipAtW_ok hP.ntt R.ly hi ry⟩)
    fun _ _ _ _ ⟨R, _, _⟩ ⟨hx, _⟩ ⟨hy, _⟩ => R.post (bases_io _ _) hx hy

omit hP in
theorem publicPoly_rel (C1 : Callee (fun S => unpackT1Contract Arm.abi S) 0 D Impl.MlDsa.Arm.Pack.unpackT1)
    (hP : PrimsOk P D) {p : Params} {i : Nat}
    (hc : rwChk (input bytes ++ output bytes count) (output bytes count) (.r4, 32 + 320 * i) 320
      (.r8, p.pkLen + 1024 * i) 1024 = true)
    (hi : ipChkW (input bytes ++ output bytes count) (output bytes count) (.r8, p.pkLen + 1024 * i) (.r7, 0) = true) :
    RelCT isa (Rel D bytes count) (publicPoly P p i) (Rel D bytes count) := by
  unfold publicPoly
  exact RelCT.seq (postDep (t1At_tr C1 hc) (fun x y R => ⟨t1At_ok C1 R.lx hc, t1At_ok C1 R.ly hc⟩)
    fun _ _ _ _ R ⟨hx, _, px⟩ ⟨hy, _, py⟩ => ⟨R.post (bases_io _ _) hx hy, red_after hx px, red_after hy py⟩)
    (transform_rel hP hi)

theorem secretPoly_rel {p : Params} {i : Nat} {src len a b : Nat} (he : secretPiece p i = (src, len, a, b))
    (hab : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b))
    (hc : rwChk (input bytes ++ output bytes count) (output bytes count) (.r4, src) len
      (.r8, p.skLen + 1024 * i) 1024 = true)
    (hi : ipChkW (input bytes ++ output bytes count) (output bytes count) (.r8, p.skLen + 1024 * i) (.r7, 0) = true) :
    RelCT isa (Rel D bytes count) (secretPoly P p i) (Rel D bytes count) := by
  unfold secretPoly
  rw [he]
  exact RelCT.seq (postDep (bupAt_tr hP hab hl hc) (fun x y R => ⟨bupAt_ok hP R.lx hab hl hc,
      bupAt_ok hP R.ly hab hl hc⟩)
    fun _ _ _ _ R ⟨hx, _, px⟩ ⟨hy, _, py⟩ => ⟨R.post (bases_io _ _) hx hy, red_after hx px, red_after hy py⟩)
    (transform_rel hP hi)

end

section
variable {P : Prims} {D : Nat} (hP : PrimsOk P D)
include hP

theorem public_rel (C1 : Callee (fun S => unpackT1Contract Arm.abi S) 0 D Impl.MlDsa.Arm.Pack.unpackT1)
    {p : Params} (hp : Ok3 p) :
    RelCT isa (Rel D p.pkLen p.k) (.seq (copy (.r8, 0) (.r4, 0) p.pkLen) (seqR (publicPoly P p) 0 p.k))
      (Rel D p.pkLen p.k) := by
  have hpk := pk_eq hp
  refine RelCT.seq (copy_rel (by omega_using [hpk])) ?_
  have := seqR_tr (f := publicPoly P p) (R := fun _ => Rel D p.pkLen p.k) p.k 0 fun i _ hi => by
    obtain ⟨hc, hi'⟩ := public_checks hp (i := i) (by omega_using [hi])
    exact publicPoly_rel C1 hP hc hi'
  exact this

theorem secret_rel {p : Params} (hp : Ok3 p) :
    RelCT isa (Rel D p.skLen (p.ℓ + 2 * p.k))
      (.seq (copy (.r8, 0) (.r4, 0) p.skLen) (seqR (secretPoly P p) 0 (p.ℓ + 2 * p.k)))
      (Rel D p.skLen (p.ℓ + 2 * p.k)) := by
  have hsk : 0 < p.skLen := by rcases hp with rfl | rfl | rfl <;> decide
  refine RelCT.seq (copy_rel hsk) ?_
  have := seqR_tr (f := secretPoly P p) (R := fun _ => Rel D p.skLen (p.ℓ + 2 * p.k)) (p.ℓ + 2 * p.k) 0
    fun i _ hi => by
      have hi' : i < p.ℓ + 2 * p.k := by omega_using [hi]
      obtain ⟨src, len, a, b, he⟩ : ∃ src len a b, secretPiece p i = (src, len, a, b) := by
        rcases secretPiece p i with ⟨src, len, a, b⟩
        exact ⟨src, len, a, b, rfl⟩
      have hchecks := secret_checks hp hi'
      rw [he] at hchecks
      obtain ⟨hc, hab, hl⟩ := hchecks
      exact secretPoly_rel hP he hab hl hc (ip_check _ _ (by omega_using [hi]))
  exact this

end

/-! ## The entry -/

theorem ldrSp_tr {r : Reg} {off : Nat} {P : State → State → Prop} (hP : ∀ x y, P x y → x.sp = y.sp) :
    RelCT isa P (.block [.ldrSp r off]) fun x y => x.sp = y.sp := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  refine ⟨?_, show s₁'.sp = s₂'.sp by rw [(Exec.rdwr e₁).2.2, (Exec.rdwr e₂).2.2, hP _ _ hp]⟩
  rw [Exec.block_iff] at e₁ e₂
  rw [ldrSp_leak e₁, ldrSp_leak e₂, hP _ _ hp]

theorem movs_nomem :
    ∀ i ∈ ([.mov .r4 (.reg .r0), .mov .r8 (.reg .r1), .mov .r7 (.reg .r2)] : List Instr), ∀ s, isa.addrs i s = [] := by
  intro i hi s
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl <;> rfl

/-- The entry states of two runs: preconditions and public data. -/
abbrev Ent2 (bytes count : Nat) (x y : State) : Prop :=
  EntryPre bytes count x ∧ EntryPre bytes count y ∧ x.sp = y.sp ∧ x.gpr .r0 = y.gpr .r0 ∧
    x.gpr .r1 = y.gpr .r1 ∧ x.gpr .r2 = y.gpr .r2

theorem entry_tr {body : Prog isa} {bytes count : Nat} (hb : bytes < 2 ^ 32) (ho : bytes + 1024 * count < 2 ^ 32)
    (hbody : RelCT isa (Rel callStack bytes count) body (Rel callStack bytes count)) :
    RelCT isa (Ent2 bytes count) (entry body) fun _ _ => True := by
  unfold entry
  refine RelCT.frame (fun s₁ s₂ h => h.2.2.1) ?_
  refine RelCT.mono (P := fun a b => ∃ q : State × State, Ent2 bytes count q.1 q.2 ∧
      a = pushed saved q.1 ∧ b = pushed saved q.2) ?_
    (fun a b ⟨s₁, s₂, hp, pa, pb⟩ => ⟨(s₁, s₂), hp, Argon2.Arm.push_eq (by decide) pa,
      Argon2.Arm.push_eq (by decide) pb⟩) (fun _ _ h => h)
  refine RelCT.exists_ fun ⟨σ₁, σ₂⟩ => ?_
  let F (σ u : State) : Prop :=
    u.gpr .r4 = σ.gpr .r0 ∧ u.gpr .r8 = σ.gpr .r1 ∧ u.gpr .r7 = σ.gpr .r2 ∧ u.sp = σ.sp - BitVec.ofNat 32 16 ∧
      u.rd = σ.rd ∧ u.wr = ⟨State.addr (σ.sp - BitVec.ofNat 32 16), 16⟩ :: σ.wr
  have mv : ∀ σ : State, WP isa (.block [.mov .r4 (.reg .r0), .mov .r8 (.reg .r1), .mov .r7 (.reg .r2)])
      (pushed saved σ) (F σ) := fun σ =>
    WP.mono (movs_ok _) fun u ⟨g4, g8, g7, _, _, grd, gwr, gsp⟩ =>
      ⟨by rw [g4, pushed_gpr], by rw [g8, pushed_gpr], by rw [g7, pushed_gpr], by rw [gsp, pushed_sp]; rfl,
        by rw [grd, pushed_rd], by rw [gwr, pushed_wr]; rfl⟩
  refine RelCT.seq (RelCT.wp (F₁ := fun u => Ent2 bytes count σ₁ σ₂ ∧ F σ₁ u) (F₂ := F σ₂)
    (block_nomem_tr movs_nomem) fun a b ⟨h, ha, hb⟩ => ⟨ha ▸ WP.mono (mv σ₁) fun _ e => ⟨h, e⟩, hb ▸ mv σ₂⟩) ?_
  refine RelCT.seq (RelCT.mono hbody (fun x y ⟨_, ⟨h, f₁⟩, f₂⟩ => ?_) fun _ _ h => h) ?_
  · obtain ⟨h₁, h₂, psp, p0, p1, p2⟩ := h
    obtain ⟨x4, x8, x7, xsp, xrd, xwr⟩ := f₁
    obtain ⟨y4, y8, y7, ysp, yrd, ywr⟩ := f₂
    refine ⟨entry_lay h₁ hb ho x4 x8 x7 xsp xrd xwr, entry_lay h₂ hb ho y4 y8 y7 ysp yrd ywr, fun b hb' => ?_,
      by rw [xsp, ysp, psp]⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb'
    rcases hb' with rfl | rfl | rfl
    · rw [x4, y4, p0]
    · rw [x8, y8, p1]
    · rw [x7, y7, p2]
  · exact RelCT.seq (ldrSp_tr fun x y h => h.sp) (RelCT.seq (ldrSp_tr fun x y h => h)
      (RelCT.mono (ldrSp_tr fun x y h => h) (fun _ _ h => h) fun _ _ _ => trivial))

end VG.Proof.MlDsa.Arm.PreparedKey

end

end

/-!
# ML-DSA on ARMv7, preparing keys: verified

`vg_mldsa*_prepare_verifying_key` and `vg_mldsa*_prepare_signing_key`, with
the ARM implementations of the primitives, are verified against
`preparePublicKeyContract` and `prepareSecretKeyContract` with 48 bytes of
stack.
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.PreparedKey

open VG VG.Arm VG.Spec.MlDsa
open VG.Impl.MlDsa.Arm.PreparedKey
open VG.Impl.MlDsa.Arm.Sign (Ptr copy seqR)
open VG.Proof.MlDsa.Arm.Sign
open VG.Spec.Sha3 (bytesAt)

/-- `vg_mldsa_unpack_t1`, with no stack. -/
def t1Callee : Callee (fun S => unpackT1Contract Arm.abi S) 0 callStack Impl.MlDsa.Arm.Pack.unpackT1 :=
  ⟨0, by decide, Pack.unpackT1_verified, by decide +kernel⟩

theorem writes_in (bytes count : Nat) :
    ∀ w ∈ writes bytes count, inB (input bytes ++ output bytes count) w.1 w.2 = true := by
  intro w hw
  simp only [writes, List.cons_append, List.mem_cons, List.mem_append, List.mem_map, List.mem_range] at hw
  rcases hw with rfl | rfl | hw | ⟨i, hi, rfl⟩
  · rw [in8]; simp
  · rw [in7]; simp
  · simp at hw
  · rw [in8, decide_eq_true_eq]; have : 1024 * i + 1024 ≤ 1024 * count := by omega_using [hi]
    omega_using [hi]

theorem writes_sub (bytes count : Nat) (u : State) :
    ∀ R ∈ (writes bytes count).map (toR u), ∃ b ∈ input bytes ++ output bytes count,
      Region.Sub R ⟨State.addr (u.gpr b.1), b.2⟩ := by
  intro R hR
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hR
  obtain ⟨n, hn, hs⟩ := sub_of_inB (s := u) (writes_in bytes count w hw)
  exact ⟨_, hn, hs⟩

/-- The body of `vg_mldsa*_prepare_verifying_key`, as `entry_correct` takes it. -/
theorem public_wp {p : Params} (hp : Ok3 p) (u : State) (L : Lay callStack (input p.pkLen) (output p.pkLen p.k) u) :
    WP isa (.seq (copy (.r8, 0) (.r4, 0) p.pkLen) (seqR (publicPoly prims p) 0 p.k)) u fun t =>
      PostB callStack u t ((writes p.pkLen p.k).map (toR u)) ∧ CS u t ∧
      bytesAt t.mem (pa t (.r8, 0)) p.pkLen = bytesAt u.mem (pa u (.r4, 0)) p.pkLen ∧
      PreparedPublicKey p t.mem (pa t (.r8, 0)) :=
  WP.mono (public_body prims_ok t1Callee hp u L) fun _ ⟨h, hk⟩ => ⟨h.post, h.cs, h.encoded, hk⟩

theorem secret_wp {p : Params} (hp : Ok3 p) (u : State)
    (L : Lay callStack (input p.skLen) (output p.skLen (p.ℓ + 2 * p.k)) u) :
    WP isa (.seq (copy (.r8, 0) (.r4, 0) p.skLen) (seqR (secretPoly prims p) 0 (p.ℓ + 2 * p.k))) u fun t =>
      PostB callStack u t ((writes p.skLen (p.ℓ + 2 * p.k)).map (toR u)) ∧ CS u t ∧
      bytesAt t.mem (pa t (.r8, 0)) p.skLen = bytesAt u.mem (pa u (.r4, 0)) p.skLen ∧
      PreparedSecretKey p t.mem (pa t (.r8, 0)) :=
  WP.mono (secret_body prims_ok hp u L) fun _ ⟨h, hk⟩ => ⟨h.post, h.cs, h.encoded, hk⟩

theorem sizes {p : Params} (hp : Ok3 p) :
    p.pkLen < 2 ^ 32 ∧ p.pkLen + 1024 * p.k < 2 ^ 32 ∧ p.skLen < 2 ^ 32 ∧
      p.skLen + 1024 * (p.ℓ + 2 * p.k) < 2 ^ 32 := by
  rcases hp with rfl | rfl | rfl <;> decide

/-- A state satisfying the precondition of the preparations. -/
def prepSat (bytes total : Nat) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x200000 | .r2 => 0x10000 | _ => 0
  sp := 0x80000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, bytes⟩]
  wr := [⟨0x200000, total⟩, ⟨0x10000, 1024⟩]

theorem prepSat_public {p : Params} (hp : Ok3 p) :
    (preparePublicKeyContract p Arm.abi prepStack).pre (prepSat p.pkLen (preparedPublicKeyBytes p)) := by
  rcases hp with rfl | rfl | rfl <;>
  sig_sat_check [preparePublicKeyContract, preparePublicKeySig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, prepSat]

theorem prepSat_secret {p : Params} (hp : Ok3 p) :
    (prepareSecretKeyContract p Arm.abi prepStack).pre (prepSat p.skLen (preparedSecretKeyBytes p)) := by
  rcases hp with rfl | rfl | rfl <;>
  sig_sat_check [prepareSecretKeyContract, prepareSecretKeySig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, prepSat]

theorem preparePublic_verified {p : Params} (hp : Ok3 p) :
    Verified Arm.target (preparePublic prims p) (preparePublicKeyContract p Arm.abi prepStack) := by
  obtain ⟨s1, s2, -, -⟩ := sizes hp
  refine ⟨fun σ hσ => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, ha, hb, hk⟩ := entry_correct (B := fun m a => PreparedPublicKey p m a) _ s1 s2
      (writes_sub _ _) (public_wp hp)
      (fun _ _ _ hb h => VG.Proof.MlDsa.PreparedKey.preparedPublicKey_of_bytes hb h) (public_pre hσ)
    refine ⟨t, s', he, ha, ?_⟩
    sig_post [preparePublicKeyContract, preparePublicKeySig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val]
    exact ⟨hb, hk⟩
  · refine RelCT.constantTime (RelCT.mono (entry_tr s1 s2 (public_rel prims_ok t1Callee hp))
      (fun x y ⟨hx, hy, hpub⟩ => ?_) fun _ _ h => h)
    sig_pub [preparePublicKeyContract, preparePublicKeySig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at hpub
    exact ⟨public_pre hx, public_pre hy, hpub⟩
  · exact ⟨_, prepSat_public hp⟩

theorem prepareSecret_verified {p : Params} (hp : Ok3 p) :
    Verified Arm.target (prepareSecret prims p) (prepareSecretKeyContract p Arm.abi prepStack) := by
  obtain ⟨-, -, s1, s2⟩ := sizes hp
  refine ⟨fun σ hσ => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, ha, hb, hk⟩ := entry_correct (B := fun m a => PreparedSecretKey p m a) _ s1 s2
      (writes_sub _ _) (secret_wp hp)
      (fun _ _ _ hb h => VG.Proof.MlDsa.PreparedKey.preparedSecretKey_of_bytes hb h) (secret_pre hσ)
    refine ⟨t, s', he, ha, ?_⟩
    sig_post [prepareSecretKeyContract, prepareSecretKeySig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val]
    exact ⟨hb, hk⟩
  · refine RelCT.constantTime (RelCT.mono (entry_tr s1 s2 (secret_rel prims_ok hp))
      (fun x y ⟨hx, hy, hpub⟩ => ?_) fun _ _ h => h)
    sig_pub [prepareSecretKeyContract, prepareSecretKeySig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at hpub
    exact ⟨secret_pre hx, secret_pre hy, hpub⟩
  · exact ⟨_, prepSat_secret hp⟩

/-- Memory holding a prepared public key at `0x200000`, of the key of zeros. -/
theorem prepared_public_mem {p : Params} (hp : Ok3 p) : ∃ m : Mem,
    bytesAt m 0x200000 p.pkLen = bytesAt (fun _ => 0) 0x1000 p.pkLen ∧ PreparedPublicKey p m 0x200000 := by
  obtain ⟨_, s', -, -, hq⟩ := (preparePublic_verified hp).1 _ (prepSat_public hp)
  sig_post [preparePublicKeyContract, preparePublicKeySig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at hq
  exact ⟨s'.mem, hq.1, hq.2⟩

/-- Memory holding a prepared private key at `0x200000`. -/
theorem prepared_secret_mem {p : Params} (hp : Ok3 p) : ∃ m : Mem, PreparedSecretKey p m 0x200000 := by
  obtain ⟨_, s', -, -, hq⟩ := (prepareSecret_verified hp).1 _ (prepSat_secret hp)
  sig_post [prepareSecretKeyContract, prepareSecretKeySig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at hq
  exact ⟨s'.mem, hq.2⟩

end VG.Proof.MlDsa.Arm.PreparedKey
