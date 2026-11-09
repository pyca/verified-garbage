module

public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.PrimsC
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Blocks
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.PrimsB
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.PrimsD
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Top
public import VerifiedGarbage.Impl.MlDsa.Arm.PreparedKey
public import VerifiedGarbage.Proof.MlDsa.PreparedKey.Values
public import VerifiedGarbage.Proof.MlDsa.PreparedKeyContract
import VerifiedGarbage.Proof.MlKem.Mem

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
  refine WP.mono (callR_ok C.ver.1 (by have := C.su; have := C.hS; omega) (t1Args_ok b1 b2) L.sp
    (rd := [⟨pa s v, 320⟩]) (wr := [pR (pa s f)])
    (fun s1 hA k => t1Pre (ent_R L k (by have := C.hS; omega) _ _) hc
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
  have hS : C.S ≤ D := by have := C.hS; omega
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
  exact ⟨⟨⟨⟨⟨by omega, by omega⟩, by omega, by omega⟩, h⟩, by decide⟩, by decide⟩

theorem keep_source (bytes count : Nat) {i : Nat} (hi : i < count) :
    keepB (input bytes ++ output bytes count) [((.r8, bytes + 1024 * i), 1024), ((.r7, 0), 1024)] (.r4, 0) bytes =
      true := by
  simp only [keepB, List.all_cons, List.all_nil, Bool.and_true, sep4_8, sep4_7, in4, Bool.and_eq_true,
    decide_eq_true_eq, bases, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_true, or_false,
    true_and]
  omega

theorem keep_prefix (bytes count : Nat) {i : Nat} (hi : i < count) :
    keepB (input bytes ++ output bytes count) [((.r8, bytes + 1024 * i), 1024), ((.r7, 0), 1024)] (.r8, 0) bytes =
      true := by
  simp only [keepB, List.all_cons, List.all_nil, Bool.and_true, sep8_8, sep8_7, in8, Bool.and_eq_true,
    Bool.or_eq_true, decide_eq_true_eq, bases, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_true, or_false,
    true_and]
  omega

theorem keep_prior (bytes count : Nat) {i j : Nat} (hi : i < count) (hj : j < i) :
    keepB (input bytes ++ output bytes count) [((.r8, bytes + 1024 * i), 1024), ((.r7, 0), 1024)]
      (.r8, bytes + 1024 * j) 1024 = true := by
  simp only [keepB, List.all_cons, List.all_nil, Bool.and_true, sep8_8, sep8_7, in8, Bool.and_eq_true,
    Bool.or_eq_true, decide_eq_true_eq, bases, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_true, or_false,
    true_and]
  omega

theorem keep_copy (bytes count : Nat) :
    keepB (input bytes ++ output bytes count) [((.r8, 0), bytes)] (.r4, 0) bytes = true := by
  simp only [keepB, List.all_cons, List.all_nil, Bool.and_true, sep4_8, in4, Bool.and_eq_true, decide_eq_true_eq, bases, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_true, or_false,
    true_and]
  omega

/-! ## The polynomials -/

/-- Each preparation slice decodes the specified secret polynomial. -/
theorem secret_value (p : Params) (key : List Byte) {i : Nat} (hi : i < p.ℓ + 2 * p.k) :
    let (src, len, a, b) := secretPiece p i
    ntt (toRq (bitUnpack ((key.drop src).take len) a b)) = (preparedSecretPolys p key)[i]! := by
  have hlen : secretLen p = VG.Proof.MlDsa.Sign.lenS p := rfl
  by_cases h1 : i < p.ℓ
  · rw [PreparedKey.secret_s1 p key h1]
    simp only [secretPiece, ite_eq_left (show i < p.ℓ + p.k by omega), hlen]
    rfl
  · by_cases h2 : i < p.ℓ + p.k
    · have hj : i - p.ℓ < p.k := by omega
      have he : p.ℓ + (i - p.ℓ) = i := by omega
      rw [← he, PreparedKey.secret_s2 p key hj]
      simp only [secretPiece, ite_eq_left (show p.ℓ + (i - p.ℓ) < p.ℓ + p.k by omega), hlen]
      unfold VG.Proof.MlDsa.Sign.s2F
      rw [Nat.mul_add]
      congr 5 <;> omega
    · have hj : i - (p.ℓ + p.k) < p.k := by omega
      have he : p.ℓ + p.k + (i - (p.ℓ + p.k)) = i := by omega
      rw [← he, PreparedKey.secret_t0 p key hj]
      simp only [secretPiece, ite_eq_right (show ¬ p.ℓ + p.k + (i - (p.ℓ + p.k)) < p.ℓ + p.k by omega), hlen]
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
  exact ⟨rw_check _ _ (by omega) (by omega), ip_check _ _ (by omega)⟩

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
    exact ⟨rw_check _ _ (by omega) (by omega), by decide, by decide⟩

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
    · exact h.lay.keepPoly ht (keep_prior bytes count hi (by omega)) (h.polys j (by omega))

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
  refine WP.seq (WP.mono (copy_inv (Verify.t1Hat (bytesAt s.mem (pa s (.r4, 0)) p.pkLen)) (by omega) s L)
    fun u hu => ?_)
  refine WP.mono (seqR_ok (I := fun i => Inv D p.pkLen p.k (Verify.t1Hat (bytesAt s.mem (pa s (.r4, 0)) p.pkLen)) s
    (bytesAt s.mem (pa s (.r4, 0)) p.pkLen) i) p.k 0 (fun i _ hi u h => ?_) u hu)
    fun t ht => ?_
  · obtain ⟨hc, hi'⟩ := public_checks hp (i := i) (by omega)
    refine inv_step (by omega) h (WP.mono (publicPoly_ok hP C1 h.lay hc hi') fun t ⟨ht, hct, hpoly⟩ =>
      ⟨ht, hct, ?_⟩)
    have hslice : bytesAt u.mem (pa u (.r4, 32 + 320 * i)) 320 =
        ((bytesAt s.mem (pa s (.r4, 0)) p.pkLen).drop (32 + 320 * i)).take 320 := by
      rw [← h.source, MlKem.bytesAt_slice _ _ (by omega)]
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
  · have hi' : i < p.ℓ + 2 * p.k := by omega
    obtain ⟨src, len, a, b, he⟩ : ∃ src len a b, secretPiece p i = (src, len, a, b) := by
      rcases secretPiece p i with ⟨src, len, a, b⟩
      exact ⟨src, len, a, b, rfl⟩
    have hchecks := secret_checks hp hi'
    rw [he] at hchecks
    obtain ⟨hc, hab, hl⟩ := hchecks
    have hip := ip_check p.skLen (p.ℓ + 2 * p.k) (o := p.skLen + 1024 * i) (by omega)
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
