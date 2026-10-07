import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Base
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Entry
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Contract
import VerifiedGarbage.Proof.Rsa.AArch64.CvFail

/-!
# A candidate on AArch64: the precondition, the zeros to `out`, and the ends

`KCtx`: what the code uses of its precondition (`kctx_of`). `front_ok`: the
zeros to `out` and the check that `rand` has a candidate's octets.
`finNone`, `finUsed` and `finPrime` end the code (`KEnd`), with the status,
the octets read to `used` and, for a prime, the prime to `out`; and the
postcondition follows (`candEnd_post`).
-/

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

/-! ## Comparisons -/

/-- The carry of `a − b` (`subs`): no borrow. -/
theorem subs_carry (a b : BitVec 64) :
    decide (2 ^ 64 ≤ a.toNat + (~~~b).toNat + true.toNat) = decide (b.toNat ≤ a.toNat) := by
  rw [BitVec.toNat_not, show true.toNat = 1 from rfl]
  have := b.isLt
  exact decide_eq_decide.mpr (by omega)

/-- `geFlag`: `x5 := 1` if `x4 ≤ x3`, else 0. -/
theorem geFlag_ok (s : State) :
    WP isa (.block geFlag) s fun t =>
      (t.gpr .x5 = BitVec.ofNat 64 (decide ((s.gpr .x4).toNat ≤ (s.gpr .x3).toNat)).toNat ∧ t.mem = s.mem) ∧
        Keep [.x3, .x4, .x5, .x7] s t := by
  refine WP.keep [.x3, .x4, .x5, .x7] ?_ (by decide) (by decide) (by decide +kernel)
  brun [geFlag, subs_carry]
  cases decide ((s.gpr .x4).toNat ≤ (s.gpr .x3).toNat) <;> rfl

/-! ## `out` and `used` -/

/-- The facts about `out` (`k` octets at `op`) and `used` (8 at `up`) every
end needs. -/
structure OutUp (s : State) (B : Addr) (Z : Nat) (op up : Addr) (k : Nat) : Prop where
  upw : InRegions s.wr up 8
  upZ : ∀ b < 8, Z ≤ ofs B (up + BitVec.ofNat 64 b)
  outw : ∀ j < k, InRegions s.wr (op + BitVec.ofNat 64 j) 1
  outZ : ∀ j < k, Z ≤ ofs B (op + BitVec.ofNat 64 j)
  ou : ∀ j < k, ∀ b < 8, op + BitVec.ofNat 64 j ≠ up + BitVec.ofNat 64 b

theorem OutUp.congr {s t : State} {B : Addr} {Z : Nat} {op up : Addr} {k : Nat} (h : OutUp s B Z op up k)
    (hw : t.wr = s.wr) : OutUp t B Z op up k :=
  ⟨by rw [hw]; exact h.upw, h.upZ, fun j hj => by rw [hw]; exact h.outw j hj, h.outZ, h.ou⟩

theorem OutUp.outOk {s : State} {B : Addr} {Z : Nat} {op up : Addr} {k : Nat} (h : OutUp s B Z op up k) :
    OutOk s B Z op k := ⟨h.outw, h.outZ⟩

/-! ## The precondition -/

/-- What `code` uses of its precondition, for the working space at stack
argument 1 of `Z` bytes and the prime's length in `x1`. -/
structure KCtx (s : State) : Prop where
  k1 : 32 ≤ (s.gpr .x1).toNat
  k2 : (s.gpr .x1).toNat ≤ 512
  k8 : (s.gpr .x1).toNat % 8 = 0
  el1 : 1 ≤ (s.gpr .x4).toNat
  el8 : (s.gpr .x4).toNat ≤ 8
  pl : (s.gpr .x6).toNat = 0 ∨ (s.gpr .x6).toNat = (s.gpr .x1).toNat
  hZ : 128 * (s.gpr .x1).toNat ≤ (stackArg s 2).toNat * 8
  hs : Scr s (stackArg s 1) ((stackArg s 2).toNat * 8)
  ha : ∀ j < 3, InRegions (s.rd ++ s.wr) (stackArgAddr s j) 8
  hsep : ∀ j < 3, ∀ m', Outside (stackArg s 1) 0 (8 * 32) s.mem m' → m'.readW (stackArgAddr s j) 64 = stackArg s j
  esrc : Src s (stackArg s 1) ((stackArg s 2).toNat * 8) (s.gpr .x3)
    (Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat)
  psrc : Src s (stackArg s 1) ((stackArg s 2).toNat * 8) (s.gpr .x5)
    (Spec.Rsa.bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat)
  rsrc : Src s (stackArg s 1) ((stackArg s 2).toNat * 8) (s.gpr .x7)
    (Spec.Rsa.bytesAt s.mem (s.gpr .x7) (stackArg s 0).toNat)
  ou : OutUp s (stackArg s 1) ((stackArg s 2).toNat * 8) (s.gpr .x0) (s.gpr .x2) (s.gpr .x1).toNat
  doe : ∀ i < (s.gpr .x4).toNat, ∀ j < (s.gpr .x1).toNat,
    s.gpr .x3 + BitVec.ofNat 64 i ≠ s.gpr .x0 + BitVec.ofNat 64 j
  dop : ∀ i < (s.gpr .x6).toNat, ∀ j < (s.gpr .x1).toNat,
    s.gpr .x5 + BitVec.ofNat 64 i ≠ s.gpr .x0 + BitVec.ofNat 64 j
  dor : ∀ i < (stackArg s 0).toNat, ∀ j < (s.gpr .x1).toNat,
    s.gpr .x7 + BitVec.ofNat 64 i ≠ s.gpr .x0 + BitVec.ofNat 64 j

theorem stackArgAddr_add (s : State) (i : Nat) :
    stackArgAddr s i = stackArgAddr s 0 + BitVec.ofNat 64 (8 * i) := by
  simp only [stackArgAddr]; rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega

theorem kctx_of {s : State} (h : candPre s) : KCtx s := by
  simp only [candPre] at h
  obtain ⟨hsp, hrd, hwr, dOu, dOe, dOp, dOr, dOs, dOa, dUe, dUp, dUr, dUs, dUa, des, dps, drs, dsa,
    wO, wU, wE, wP, wR, wS, hk, hl1, hl8, hpl, hsl⟩ := h
  obtain ⟨hk1, hk2, hk8⟩ := hk
  unfold Spec.Rsa.scratchWords at hsl
  have hs : Scr s (stackArg s 1) ((stackArg s 2).toNat * 8) := Scr.of_mem (by rw [hwr]; simp) wS
  have hn := hs.nowrap
  have ha : ∀ j < 3, InRegions (s.rd ++ s.wr) (stackArgAddr s j) 8 := fun j hj =>
    ⟨⟨stackArgAddr s 0, 24⟩, by rw [hrd]; simp,
      by rw [stackArgAddr_add s j]; exact Offset.contains_base _ (by omega) (by omega)⟩
  have hsep : ∀ j < 3, ∀ m', Outside (stackArg s 1) 0 (8 * 32) s.mem m' →
      m'.readW (stackArgAddr s j) 64 = stackArg s j :=
    fun j hj m' ho => Mem.readW_congr fun b hb => ho _ (Or.inr (by
      have := out_scr dsa.symm (contains_byte (stackArgAddr s 0) (i := 8 * j + b) (len := 24) (by omega) (by omega))
      rw [stackArgAddr_add s j, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; omega))
  have he := src_of_region (s := s) (B := stackArg s 1) (Z := (stackArg s 2).toNat * 8) (by rw [hrd]; simp)
    (by omega) des
  have hp := src_of_region (s := s) (B := stackArg s 1) (Z := (stackArg s 2).toNat * 8) (by rw [hrd]; simp)
    (by omega) dps
  have hr := src_of_region (s := s) (B := stackArg s 1) (Z := (stackArg s 2).toNat * 8) (by rw [hrd]; simp)
    (by omega) drs
  have ho : OutUp s (stackArg s 1) ((stackArg s 2).toNat * 8) (s.gpr .x0) (s.gpr .x2) (s.gpr .x1).toNat := by
    refine ⟨⟨⟨s.gpr .x2, 8⟩, by rw [hwr]; simp, ?_⟩, fun b hb => out_scr dUs (contains_byte _ (by omega) (by omega)),
      fun j hj => ⟨_, by rw [hwr]; exact List.mem_cons_self .., contains_byte _ (by omega) (by omega)⟩,
      fun j hj => out_scr dOs (contains_byte _ (by omega) (by omega)), fun j hj b hb he => ?_⟩
    · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
    · exact dOu _ (contains_byte _ (by omega) (by omega)) (by rw [he]; exact contains_byte _ (by omega) (by omega))
  exact ⟨hk1, hk2, hk8, hl1, hl8, hpl, by omega, hs, ha, hsep, he, hp, hr, ho,
    fun i hi j hj hh => dOe _ (contains_byte (s.gpr .x0) (i := j) (by omega) (by omega))
      (by rw [← hh]; exact contains_byte _ (by omega) (by omega)),
    fun i hi j hj hh => dOp _ (contains_byte (s.gpr .x0) (i := j) (by omega) (by omega))
      (by rw [← hh]; exact contains_byte _ (by omega) (by omega)),
    fun i hi j hj hh => dOr _ (contains_byte (s.gpr .x0) (i := j) (by omega) (by omega))
      (by rw [← hh]; exact contains_byte _ (by omega) (by omega))⟩

/-! ## The ends -/

/-- `finish r`: `x3` to `used`, and `r` returned. -/
theorem finish_ok {s : State} {B : Addr} {Z : Nat} {up : Addr} {r : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (hZ : 8 * 32 ≤ Z) (hr : r < 2 ^ 16) (hU : word s.mem B (8 * kUsedP) = up) (hw : InRegions s.wr up 8) :
    WP isa (.block (finish r)) s fun t =>
      (t.gpr .x0 = BitVec.ofNat 64 r ∧ t.mem = s.mem.writeW up (s.gpr .x3)) ∧ Keep [.x0, .x2] s t := by
  have hn := hs.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega)
  refine WP.keep [.x0, .x2] ?_ rfl rfl rfl
  have hup : up + BitVec.ofNat 64 0 = up := off_zero up
  brun [finish, h0, hdr_enc (show kUsedP < 32 by decide), hl kUsedP (by decide), hU, hup, hw]
  exact BitVec.eq_of_toNat_eq (by simp [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega)

/-- What an end leaves: the status `r` returned and `u` at `used`, the
rest of memory as it was. -/
structure FinPost (s t : State) (up : Addr) (r u : Nat) : Prop where
  x0 : t.gpr .x0 = BitVec.ofNat 64 r
  mem : t.mem = s.mem.writeW up (BitVec.ofNat 64 u)
  keep : Keep (.x0 :: mmRegs) s t

/-- `finNone`: 0 to `used`, and 0 returned. -/
theorem finNone_ok {s : State} {B : Addr} {Z : Nat} {up : Addr} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (hZ : 8 * 32 ≤ Z) (hU : word s.mem B (8 * kUsedP) = up) (hw : InRegions s.wr up 8) :
    WP isa finNone s fun t => FinPost s t up 0 0 := by
  unfold finNone
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.gpr .x3 = BitVec.ofNat 64 0 ∧ t.mem = s.mem) (by brun)
    (by decide) (by decide) (by decide +kernel)) fun t₁ ⟨⟨h3, hm⟩, k₁⟩ => ?_
  refine WP.mono (finish_ok (up := up) (hs.congr k₁.wr) ((k₁.gpr .x0 (by decide)).trans h0) hZ (by decide)
    (by rw [hm]; exact hU) (by rw [k₁.wr]; exact hw)) fun t ⟨⟨hx, hm'⟩, k₂⟩ => ⟨hx, by rw [hm', h3, hm], ?_⟩
  exact (k₁.trans k₂).mono (by decide)

/-- `finUsed r`: `kUsed` to `used`, and `r` returned. -/
theorem finUsed_ok {s : State} {B : Addr} {Z : Nat} {up : Addr} {r u : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (hZ : 8 * 32 ≤ Z) (hr : r < 2 ^ 16) (hu : word s.mem B (8 * kUsed) = BitVec.ofNat 64 u)
    (hU : word s.mem B (8 * kUsedP) = up) (hw : InRegions s.wr up 8) :
    WP isa (finUsed r) s fun t => FinPost s t up r u := by
  have hn := hs.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega)
  unfold finUsed
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.gpr .x3 = BitVec.ofNat 64 u ∧ t.mem = s.mem)
    (by brun [h0, hdr_enc (show kUsed < 32 by decide), hl kUsed (by decide), hu])
    (by decide) (by decide) (by decide +kernel)) fun t₁ ⟨⟨h3, hm⟩, k₁⟩ => ?_
  refine WP.mono (finish_ok (up := up) (hs.congr k₁.wr) ((k₁.gpr .x0 (by decide)).trans h0) hZ hr
    (by rw [hm]; exact hU) (by rw [k₁.wr]; exact hw)) fun t ⟨⟨hx, hm'⟩, k₂⟩ => ⟨hx, by rw [hm', h3, hm], ?_⟩
  exact (k₁.trans k₂).mono (by decide)

/-- The octets of `out`. -/
abbrev outBytes (m : Mem) (op : Addr) (k : Nat) : List Byte := (List.range k).map fun i => m (op + BitVec.ofNat 64 i)

/-- A byte apart from the 8 at `up` survives a store there. -/
theorem writeW64_other {m : Mem} {up x : Addr} (v : BitVec 64) (h : ∀ b < 8, x ≠ up + BitVec.ofNat 64 b) :
    m.writeW up v x = m x := by
  unfold Mem.writeW
  refine Mem.write_apply fun hlt => h (x - up).toNat (by simpa using hlt) ?_
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]

/-- The octets at `op` after a store of `used`, apart from them. -/
theorem outBytes_writeW {m : Mem} {op up : Addr} {k : Nat} (v : BitVec 64)
    (ho : ∀ j < k, ∀ b < 8, op + BitVec.ofNat 64 j ≠ up + BitVec.ofNat 64 b) :
    outBytes (m.writeW up v) op k = outBytes m op k :=
  List.map_congr_left fun j hj => writeW64_other v (ho j (List.mem_range.mp hj))

/-- How a candidate ends, from `s`: status `r`, `u` to `used`, and `out`
the `k` octets of `c` if `outv = some c`, else unchanged. -/
structure KEnd (s t : State) (op up : Addr) (k r u : Nat) (outv : Option Nat) : Prop where
  x0 : t.gpr .x0 = BitVec.ofNat 64 r
  used : t.mem.readW up 64 = BitVec.ofNat 64 u
  out : outBytes t.mem op k = match outv with
    | some c => Spec.Rsa.i2osp c k
    | none => outBytes s.mem op k
  keep : Keep (.x0 :: mmRegs) s t

theorem KEnd.of_fin {s t : State} {B : Addr} {Z : Nat} {op up : Addr} {k r u : Nat} (ho : OutUp s B Z op up k)
    (h : FinPost s t up r u) : KEnd s t op up k r u none :=
  ⟨h.x0, by rw [h.mem, Mem.readW_writeW_self64], by rw [h.mem]; exact outBytes_writeW _ ho.ou, h.keep⟩

/-- `KEnd` from an earlier state, whose `out` octets are those of `s₀`. -/
theorem KEnd.trans_pre {s₀ s t : State} {op up : Addr} {k r u : Nat} {outv : Option Nat}
    (h : KEnd s t op up k r u outv) (hout : outBytes s.mem op k = outBytes s₀.mem op k)
    (k₀ : Keep (.x0 :: mmRegs) s₀ s) : KEnd s₀ t op up k r u outv := by
  refine ⟨h.x0, h.used, ?_, (k₀.trans h.keep).mono (by decide)⟩
  rw [h.out]
  cases outv
  · exact hout
  · rfl

end VG.Proof.RsaKeyGen.AArch64
