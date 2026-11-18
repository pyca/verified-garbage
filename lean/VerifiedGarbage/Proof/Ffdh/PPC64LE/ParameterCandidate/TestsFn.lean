module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Tests
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Sieved
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Residue
public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.RsaKeyGen.Bits
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Mr
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Phase
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.Proof.Ffdh.Contract
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Base
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMid
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubOut

/-! ### `Ffdh.PPC64LE.ParameterCandidate.Result`, which this module and modules that import it used -/

section

/-! ### `Ffdh.PPC64LE.ParameterCandidate.WriteP`, which this module and modules that import it used -/

section

/-!
# An FFDH parameter candidate on PPC64LE: p to `out`

`writeP_ok`: `out`'s byte `i` is array 0's byte `k − 1 − i`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search (ldh)

/-- `writeP`'s first block: `out`, `out_len`, and the address of p's last
octet. -/
theorem writeHead_ok {s : State} {B O : Addr} {Z k : Nat} (hs : Scr s B Z)
    (h31 : s.gpr .r31 = B) (h10 : s.gpr .r10 = off B 256)
    (hO : s.mem.readW (B + BitVec.ofNat 64 16) 64 = O) (hL : s.mem.readW (B + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 k)
    (hk : 1 ≤ k) (hZ : 256 + k ≤ Z) :
    WP isa (.block [ldh .r4 hOut, ldh .r5 hLen, .add .r6 .r10 .r5, .subi .r6 .r6 1]) s fun s₂ =>
      (s₂.gpr .r6 = off B (256 + (k - 1)) ∧ s₂.gpr .r4 = O ∧ s₂.gpr .r5 = BitVec.ofNat 64 k ∧ s₂.mem = s.mem) ∧
        Keep [.r4, .r5, .r6] s s₂ := by
  have hnw := hs.nowrap
  refine WP.keep [.r4, .r5, .r6] ?_ (by decide)
  simp only [ldh, hOut, hLen]
  prun [h31, h10, hO, hL, hs.ld (d := 16) (n := 8) (by omega_arith), hs.ld (d := 24) (n := 8) (by omega_arith),
    off_add, BitVec.add_zero]
  rw [off_sub1 _ (by omega_arith)]; congr 2; omega_arith

theorem writeP_ok {s : State} {B O : Addr} {Z k : Nat} (hs : Scr s B Z) (ho : Scr s O k)
    (h31 : s.gpr .r31 = B) (h10 : s.gpr .r10 = off B 256)
    (hO : s.mem.readW (B + BitVec.ofNat 64 16) 64 = O) (hL : s.mem.readW (B + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 k)
    (hk : 1 ≤ k) (hZ : 256 + k ≤ Z) (hsep : ∀ x, ofs O x < k → Z ≤ ofs B x) :
    WP isa writeP s fun t =>
      ((∀ i < k, t.mem (off O i) = s.mem (off B (256 + (k - 1 - i)))) ∧ Outside O 0 k s.mem t.mem) ∧
      Keep [.r0, .r4, .r5, .r6] s t := by
  have hnw := hs.nowrap
  have hno := ho.nowrap
  unfold writeP
  refine WP.seq ?_
  refine WP.mono (writeHead_ok hs h31 h10 hO hL hk hZ) fun s₂ ⟨⟨b6, b4, b5, m2⟩, k2⟩ => ?_
  let Inv : Nat → State → Prop := fun j t =>
    t.gpr .r6 = off B (256 + (k - 1) - j) ∧ t.gpr .r4 = off O j ∧ Outside O 0 j s.mem t.mem ∧
      (∀ i < j, t.mem (off O i) = s.mem (off B (256 + (k - 1 - i)))) ∧ Keep [.r0, .r4, .r5, .r6] s t
  refine WP.mono (wp_countdown (body := .block ([.lbz .r0 .r6 0, .stb .r0 .r4 0, .addi .r4 .r4 1,
      .subi .r6 .r6 1] ++ ([.subi .r5 .r5 1] : List Instr)))
    (cnt := .r5) (N := k) (by omega_arith) (by omega_arith) Inv (fun j hj t ⟨t6, t4, tout, tb, tk⟩ hc => ?_)
    ⟨by rw [b6]; rfl, by rw [b4]; simp [off], by rw [m2]; exact Outside.refl _ _ _ _, fun _ h => absurd h (by omega_arith),
      k2.mono (by decide)⟩ b5) fun t ⟨_, _, tout, tb, tk⟩ => ⟨⟨tb, tout⟩, tk⟩
  have hrd : InRegions (t.rd ++ t.wr) (off B (256 + (k - 1) - j)) 1 := by
    rw [tk.rd, tk.wr]; exact hs.ld (show 256 + (k - 1) - j + 1 ≤ Z by omega_arith)
  have hst : WP isa (.block [.lbz .r0 .r6 0, .stb .r0 .r4 0, .addi .r4 .r4 1, .subi .r6 .r6 1,
      .subi .r5 .r5 1]) t fun t' => t' = ((({ (t.write .r0
        ((t.mem.read (off B (256 + (k - 1) - j)) 1).setWidth 64)) with
        mem := t.mem.write (off O j) 1 (((t.mem.read (off B (256 + (k - 1) - j)) 1).setWidth 64).setWidth 8) } :
          State).write .r4 (off O (j + 1))).write .r6
            (off B (256 + (k - 1) - j) - BitVec.ofNat 64 1)).write .r5 (t.gpr .r5 - BitVec.ofNat 64 1) := by
    prun [t6, t4, exec_lbz' (show Reg.r6 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide),
      exec_stb (show Reg.r4 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide), hrd,
      (ho.congr tk.wr).st (d := j) (n := 1) (by omega_arith)]
  refine WP.mono hst fun t' e => ?_
  subst e
  have hw1 := write1_outside t.mem O (d := j) (((t.mem.read (off B (256 + (k - 1) - j)) 1).setWidth 64).setWidth 8)
    (by omega_arith)
  have harr : t.mem (off B (256 + (k - 1) - j)) = s.mem (off B (256 + (k - 1) - j)) := by
    refine tout _ (Or.inr ?_)
    by_contra hc
    have := hsep (off B (256 + (k - 1) - j)) (by omega_arith)
    rw [show ofs B (off B (256 + (k - 1) - j)) = 256 + (k - 1) - j from
      Mem.sub_ofNat_toNat B (by omega_arith)] at this
    omega_arith
  refine ⟨⟨?_, by gsimp, ?_, ?_, ?_⟩, by gsimp⟩
  · gsimp; rw [off_sub1 _ (by omega_arith), show 256 + (k - 1) - j - 1 = 256 + (k - 1) - (j + 1) by omega_arith]
  · gsimp; exact (tout.mono (Nat.le_refl _) (by omega_arith)).trans (hw1.mono (by omega_arith) (by omega_arith))
  · intro i hi
    gsimp
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [hw1 _ (by rw [ofs_off0 O (by omega_arith)]; omega_arith)]; exact tb i hi
    · rw [write1_self, Pub.read1_setWidth, show 256 + (k - 1 - i) = 256 + (k - 1) - i by omega_arith, ← harr]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth]
      have := (t.mem (off B (256 + (k - 1) - i))).isLt
      omega_arith
  · exact tk.trans' (((((Keep.write _ _ _).trans (Keep.mem _ _)).trans
      (Keep.write _ _ _)).trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).mono

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate

end

end

/-! ### `Ffdh.PPC64LE.ParameterCandidate.End`, which this module and modules that import it used -/

section

/-! ### `Ffdh.PPC64LE.ParameterCandidate.Finish`, which only this module used -/

section

/-!
# An FFDH parameter candidate on PPC64LE: the result

`finish_ok`: `used := ` the octets read (0 for the status 0) and `r3 := `
the status.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search

theorem finish_ok (r : Nat) (hr : r ≤ 2) {s : State} {B U : Addr} {Z v : Nat} (hs : Scr s B Z) (hu : Scr s U 8)
    (h31 : s.gpr .r31 = B) (hU : s.mem.readW (B + BitVec.ofNat 64 32) 64 = U)
    (hV : s.mem.readW (B + BitVec.ofNat 64 152) 64 = BitVec.ofNat 64 v) (hZ : 160 ≤ Z) :
    WP isa (.block (finish r)) s fun t => (t.gpr .r3 = BitVec.ofNat 64 r ∧
      t.mem = s.mem.writeW (off U 0) (BitVec.ofNat 64 (if r = 0 then 0 else v))) ∧ Keep [.r3, .r4, .r5] s t := by
  obtain rfl | rfl | rfl : r = 0 ∨ r = 1 ∨ r = 2 := by omega_using [hr]
  · refine WP.keep [.r3, .r4, .r5] ?_ (by decide)
    simp only [finish, ldh, hUsedP, ↓reduceIte]
    prun [h31, hU, hs.ld (d := 32) (n := 8) (by omega_using [hZ]), hu.st (d := 0) (n := 8) (by omega_using [])]
  all_goals
    refine WP.keep [.r3, .r4, .r5] ?_ (by decide)
    simp only [finish, ldh, hUsedP, hUsed, Nat.reduceEqDiff, ↓reduceIte, List.cons_append,
      List.nil_append]
    prun [h31, hU, hV, hs.ld (d := 32) (n := 8) (by omega_using [hZ]), hs.ld (d := 152) (n := 8) (by omega_using [hZ]),
      hu.st (d := 0) (n := 8) (by omega_using [])]

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate

end

end


/-!
# An FFDH parameter candidate on PPC64LE: the end of a candidate

`CEnd p res`: before the exit, the status of `res` in `r3`, `out` and `used`
as the contract states them, and what the exit reads (`ESt`). `finEnd`:
`finish` for a candidate without p; `pEnd`: p to `out`, then `finish`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search

/-- What the exit reads: the working space, its length and the save area. -/
structure ESt (p : PP) (s : State) : Prop where
  scr : Scr s p.B p.Z
  r31 : s.gpr .r31 = p.B
  len : word s.mem p.B 0 = BitVec.ofNat 64 p.n
  save : ∀ i < 19, word s.mem p.B (8 * p.n - saveBytes + 8 * i) = p.sv i
  sp : s.sp = p.sp
  dims : Dims p
  r2 : s.gpr .r2 = p.toc

theorem St.toE {p : PP} {s : State} (h : St p s) : ESt p s :=
  ⟨h.scr, h.r31, h.args.wsLen, h.save, h.sp, h.dims, h.r2⟩

/-- `ESt` survives a change outside the working space. -/
theorem ESt.frame {p : PP} {s t : State} (h : ESt p s) (hm : ∀ x, ofs p.B x < p.Z → t.mem x = s.mem x)
    {regs : List Reg} (k : Keep regs s t) (h31 : Reg.r31 ∉ regs) (h2 : Reg.r2 ∉ regs := by decide) : ESt p t := by
  have hnw := h.scr.nowrap
  have hdn := h.dims.n
  have hb := h.dims.b1
  have hf : Frm p.B [(p.Z, 2 ^ 64)] s.mem t.mem := fun x hx => hm x (by
    have h1 := hx _ (List.mem_singleton_self _)
    have h2 := (x - p.B).isLt
    simp only [ofs] at h1 h2 ⊢; omega_arith)
  have wd : ∀ d, d + 8 ≤ p.Z → word t.mem p.B d = word s.mem p.B d := fun d hd =>
    hf.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl hd) (by omega_arith)
  exact ⟨h.scr.congr k.wr, (k.gpr _ h31).trans h.r31, (wd 0 (by simp only [PP.Z, PP.L] at *; omega_arith)).trans h.len,
    fun i hi => (wd _ (by simp only [PP.Z, PP.L, saveBytes] at *; omega_arith)).trans (h.save i hi), k.sp.trans h.sp,
    h.dims, (k.gpr _ h2).trans h.r2⟩

/-- `out` as the contract states it. -/
def outOf (p : PP) : Option (Option Nat × List Byte) → List Byte
  | some (some c, _) => Spec.Rsa.i2osp c p.L
  | _ => List.replicate p.L 0

/-- `used` as the contract states it. -/
def usedOf (p : PP) : Option (Option Nat × List Byte) → Nat
  | some (_, rest) => p.r.length - rest.length
  | none => 0

/-- The end of a candidate, before the exit. -/
def CEnd (p : PP) (res : Option (Option Nat × List Byte)) (t : State) : Prop :=
  ESt p t ∧ t.gpr .r3 = BitVec.ofNat 64 (Proof.Ffdh.candidateStatus res) ∧
    Spec.Rsa.bytesAt t.mem p.op p.L = outOf p res ∧ t.mem.readW p.up 64 = BitVec.ofNat 64 (usedOf p res)

/-- A store to `used` keeps the working space and `out`. -/
theorem used_store {p : PP} {s : State} (h : Bufs p s) {m m' : Mem} (hm : Outside p.up 0 8 m m') :
    (∀ x, ofs p.B x < p.Z → m' x = m x) ∧ Spec.Rsa.bytesAt m' p.op p.L = Spec.Rsa.bytesAt m p.op p.L := by
  have hnu := h.scrU.nowrap
  have hno := h.scrO.nowrap
  refine ⟨fun x hx => hm x (Or.inr ?_), ?_⟩
  · by_contra hc
    have := h.sepU x (by omega_arith)
    omega_arith
  · simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => hm _ (Or.inr ?_)
    have hi' := List.mem_range.mp hi
    by_contra hc
    exact h.dOU _ (VG.Proof.Bignum.contains_byte p.op hi' (by omega_arith)) (by
      simp only [Region.Contains]; simp only [ofs] at hc; omega)

/-- `finish` for a candidate without p, from `St`. -/
theorem finEnd {p : PP} {s : State} (h : St p s) {r v : Nat} (hr : r = 0 ∨ r = 2)
    {res : Option (Option Nat × List Byte)} (hst : Proof.Ffdh.candidateStatus res = r)
    (hout : outOf p res = List.replicate p.L 0) (huse : usedOf p res = if r = 0 then 0 else v)
    (hv : word s.mem p.B 152 = BitVec.ofNat 64 v) :
    WP isa (.block (finish r)) s (CEnd p res) := by
  have hdn := h.dims.n
  refine WP.mono (finish_ok r (by omega_arith) h.scr h.bufs.scrU h.r31 h.args.usedP' hv
    (by simp only [PP.Z, PP.L] at *; omega_arith)) fun t ⟨⟨t3, tm⟩, k⟩ => ?_
  have hO : Outside p.up 0 8 s.mem t.mem := by rw [tm]; exact writeW_outside _ _ _ (by omega_arith)
  obtain ⟨hws, hob⟩ := used_store h.bufs hO
  refine ⟨h.toE.frame hws k (by decide), by rw [t3, hst], by rw [hob, h.bufs.bO, hout], ?_⟩
  have e0 : off p.up 0 = p.up := by simp [off]
  rw [tm, e0, Mem.readW_writeW_self64, huse]

/-- A header word, kept by a change outside the working space. -/
theorem word_of_ws {p : PP} {m m' : Mem} (hm : ∀ x, ofs p.B x < p.Z → m' x = m x) {d : Nat} (hd : d + 8 ≤ p.Z)
    (hnw : p.B.toNat + p.Z ≤ 2 ^ 64) : m'.readW (p.B + BitVec.ofNat 64 d) 64 = m.readW (p.B + BitVec.ofNat 64 d) 64 :=
  (show Frm p.B [(p.Z, 2 ^ 64)] m m' from fun x hx => hm x (by
    have h1 := hx _ (List.mem_singleton_self _)
    have h2 := (x - p.B).isLt
    simp only [ofs] at h1 h2 ⊢; omega_arith)).word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl hd)
    (by omega_arith)

/-- p to `out`, then `finish` with the status 1. -/
theorem pEnd {C : Nat} {p : PP} {s : State} {c u : Nat} (h : St p s) (hp : Ph p p.bits C s)
    (hn : Mont.val32 s.mem p.B 256 (2 * wOf p.bits) = c) (hc : c < 2 ^ p.bits)
    (hv : word s.mem p.B 152 = BitVec.ofNat 64 u) (hul : u ≤ p.r.length) :
    WP isa (.seq writeP (.block (finish 1))) s (CEnd p (some (some c, p.r.drop u))) := by
  have hdn := h.dims.n
  have hb1 := h.dims.b1
  have hnw := h.scr.nowrap
  have hLe : p.L = (p.bits + 7) / 8 := rfl
  have hZe : p.Z = 8 * p.n := rfl
  have h10 : s.gpr .r10 = off p.B 256 := hp.r10.trans (by rw [show slot (wOf p.bits) 0 = 256 by simp [slot, hdrBytes]])
  refine WP.seq (WP.mono (writeP_ok h.scr h.bufs.scrO h.r31 h10 h.args.out' h.args.len' (by omega_arith) (by omega_arith)
    h.bufs.sepO) fun t₁ ⟨⟨tb, tout⟩, k₁⟩ => ?_)
  have hws₁ : ∀ x, ofs p.B x < p.Z → t₁.mem x = s.mem x := fun x hx => tout x (Or.inr (by
    by_contra hc'
    have := h.bufs.sepO x (by omega_arith)
    omega_arith))
  have E₁ := h.toE.frame hws₁ k₁ (by decide)
  refine WP.mono (finish_ok 1 (by decide) E₁.scr (h.bufs.scrU.congr k₁.wr) E₁.r31
    ((word_of_ws hws₁ (d := 32) (by omega_arith) hnw).trans h.args.usedP')
    ((word_of_ws hws₁ (d := 152) (by omega_arith) hnw).trans hv) (by omega_arith)) fun t ⟨⟨t3, tm⟩, k⟩ => ?_
  have hO : Outside p.up 0 8 t₁.mem t.mem := by rw [tm]; exact writeW_outside _ _ _ (by omega_arith)
  obtain ⟨hws, hob⟩ := used_store h.bufs hO
  refine ⟨E₁.frame hws k (by decide), by rw [t3]; rfl, ?_, ?_⟩
  · rw [hob]
    simp only [outOf]
    refine Pub.out_bytes (w := wOf p.bits) (by simp only [wOf]; omega_arith) hn ?_ tb
    rw [VG.Proof.Bignum.pow256_eq]
    exact Nat.lt_of_lt_of_le hc (Nat.pow_le_pow_right (by decide) (by omega_arith))
  · have e0 : off p.up 0 = p.up := by simp [off]
    rw [tm, e0, Mem.readW_writeW_self64]
    simp only [usedOf, List.length_drop, Nat.one_ne_zero, ↓reduceIte]
    congr 1; omega_arith

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate

end

end

/-!
# An FFDH parameter candidate on PPC64LE: the results of the tests

`pResult_ok`: after p's test, p to `out` if it passed, the status by its
`hStat`; `qResult_ok`: after a failed test of q.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search VG.Proof.MillerRabin.PPC64LE.Search

theorem ofNat_toNat64' (x : BitVec 64) : x = BitVec.ofNat 64 x.toNat := by
  apply BitVec.eq_of_toNat_eq; simp

/-- `hStat` into `r3`. -/
theorem statLoad_ok {C : Nat} {p : PP} {mb N : Nat} {s : State} (M : MSt p mb N C s) :
    WP isa (.block [ldh .r3 hStat]) s fun t => MSt p mb N C t ∧ t.gpr .r3 = word s.mem p.B 160 ∧ t.mem = s.mem ∧
      Keep [.r3] s t := by
  have l160 : InRegions (s.rd ++ s.wr) (p.B + BitVec.ofNat 64 160) 8 := M.st.ld (d := 160) (by decide)
  refine WP.mono (WP.keep [.r3] (Q := fun t => t.gpr .r3 = word s.mem p.B 160 ∧ t.mem = s.mem)
    (by simp only [ldh, hStat]; prun [M.st.r31, l160]) (by decide)) fun t ⟨⟨t3, tm⟩, k⟩ => ?_
  exact ⟨M.frm (rs := []) (by rw [tm]; exact Frm.refl _ _ _) (by simp) k (by decide) (k.gpr _ (by decide))
    (k.gpr _ (by decide)) (k.gpr _ (by decide)), t3, tm, k⟩

/-- After p's test. -/
theorem pResult_ok {C : Nat} {p : PP} {s : State} {c : Nat} {resP : Option (Bool × List Byte)}
    (hE : MrEnd p p.bits c C resP s) (hc : c < 2 ^ p.bits) :
    WP isa pResult s (CEnd p (resP.map fun x => (if x.1 then some c else none, x.2))) := by
  obtain ⟨M, hnone, hsome⟩ := hE
  unfold pResult
  refine WP.seq (WP.mono (statLoad_ok M) fun t ⟨Mt, t3, tm, _⟩ => ?_)
  have h152 : word t.mem p.B 152 = word s.mem p.B 152 := by rw [tm]
  rcases resP with _ | ⟨b, rest⟩
  · have h0 := hnone rfl
    refine WP.ite true (eval_zero_ofNat t .r3 (k := 0) (by decide) (t3.trans h0)) (fun _ => ?_)
      (fun h => absurd h (by decide))
    exact finEnd Mt.st (r := 0) (Or.inl rfl) rfl rfl rfl (ofNat_toNat64' _)
  · obtain ⟨hS, u, hul, rfl, hU⟩ := hsome b rest rfl
    have hU' : word t.mem p.B 152 = BitVec.ofNat 64 u := h152.trans hU
    cases b
    · refine WP.ite false (eval_zero_ofNat t .r3 (k := 2) (by decide) (t3.trans hS)) (fun h => absurd h (by decide))
        (fun _ => ?_)
      refine WP.seq (WP.mono (WP.keep [.r3] (Q := fun v => v.gpr .r3 = BitVec.ofNat 64 1 ∧ v.mem = t.mem)
        (by prun [t3, hS]; rfl) (by decide)) fun v ⟨⟨v3, vm⟩, k⟩ => ?_)
      have Mv : MSt p p.bits c C v := Mt.frm (rs := []) (by rw [vm]; exact Frm.refl _ _ _) (by simp) k (by decide)
        (k.gpr _ (by decide)) (k.gpr _ (by decide)) (k.gpr _ (by decide))
      refine WP.ite false (eval_zero_ofNat v .r3 (k := 1) (by decide) v3) (fun h => absurd h (by decide))
        (fun _ => ?_)
      refine finEnd Mv.st (r := 2) (v := u) (Or.inr rfl) rfl rfl ?_ (by rw [vm]; exact hU')
      simp only [Option.map_some, Bool.false_eq_true, ↓reduceIte, usedOf, List.length_drop, Nat.reduceEqDiff]
      omega_arith
    · refine WP.ite false (eval_zero_ofNat t .r3 (k := 1) (by decide) (t3.trans hS)) (fun h => absurd h (by decide))
        (fun _ => ?_)
      refine WP.seq (WP.mono (WP.keep [.r3] (Q := fun v => v.gpr .r3 = BitVec.ofNat 64 0 ∧ v.mem = t.mem)
        (by prun [t3, hS]; rfl) (by decide)) fun v ⟨⟨v3, vm⟩, k⟩ => ?_)
      have Mv : MSt p p.bits c C v := Mt.frm (rs := []) (by rw [vm]; exact Frm.refl _ _ _) (by simp) k (by decide)
        (k.gpr _ (by decide)) (k.gpr _ (by decide)) (k.gpr _ (by decide))
      refine WP.ite true (eval_zero_ofNat v .r3 (k := 0) (by decide) v3) (fun _ => ?_) (fun h => absurd h (by decide))
      have hn : Mont.val32 v.mem p.B 256 (2 * wOf p.bits) = c := by
        have := Mv.prep.n
        simp only [MillerRabin.PPC64LE.arr] at this
        rw [show slot (wOf p.bits) 0 = 256 by simp [slot, hdrBytes]] at this
        exact this
      exact pEnd Mv.st Mv.ph hn hc (by rw [vm]; exact hU') hul

/-- After a failed test of q. -/
theorem qResult_ok {C : Nat} {p : PP} {s : State} {mb N : Nat} {resQ : Option (Bool × List Byte)}
    (hE : MrEnd p mb N C resQ s) (hq : ∀ rest, resQ ≠ some (true, rest)) :
    WP isa qResult s (CEnd p (resQ.map fun x => (none, x.2))) := by
  obtain ⟨M, hnone, hsome⟩ := hE
  unfold qResult
  refine WP.seq (WP.mono (statLoad_ok M) fun t ⟨Mt, t3, tm, _⟩ => ?_)
  rcases resQ with _ | ⟨b, rest⟩
  · refine WP.ite true (eval_zero_ofNat t .r3 (k := 0) (by decide) (t3.trans (hnone rfl))) (fun _ => ?_)
      (fun h => absurd h (by decide))
    exact finEnd Mt.st (r := 0) (Or.inl rfl) rfl rfl rfl (ofNat_toNat64' _)
  · cases b
    · obtain ⟨hS, u, hul, rfl, hU⟩ := hsome false rest rfl
      refine WP.ite false (eval_zero_ofNat t .r3 (k := 2) (by decide) (t3.trans hS)) (fun h => absurd h (by decide))
        (fun _ => ?_)
      refine finEnd Mt.st (r := 2) (v := u) (Or.inr rfl) rfl rfl ?_ (by rw [tm]; exact hU)
      simp only [Option.map_some, ↓reduceIte, usedOf, List.length_drop, Nat.reduceEqDiff]
      omega_arith
    · exact absurd rfl (hq rest)

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate

end

end

/-! ### `Ffdh.PPC64LE.ParameterCandidate.Halve`, which this module and modules that import it used -/

section

/-! ### `Ffdh.ParameterCandidate.WordHalf`, which only this module used -/

section

/-!
# FFDH parameter candidates: halving a number of words in place

Each word shifted right by one, with the next word's low bit shifted in at
the top, is the number halved (`wv_half`). For any target whose words are 64
bits.
-/

@[expose] public section

namespace VG.Proof.Ffdh.ParameterCandidate

open VG VG.Proof.Bignum VG.Proof.RsaKeyGen

theorem wv_half {m m' : Mem} {p : Addr} {d w : Nat} (hw : 1 ≤ w)
    (hlo : ∀ j, j + 1 < w →
      word m' p (d + 8 * j) = (word m p (d + 8 * j) >>> 1) ||| (word m p (d + 8 * (j + 1)) <<< 63))
    (htop : word m' p (d + 8 * (w - 1)) = word m p (d + 8 * (w - 1)) >>> 1) :
    wv m' p d w = wv m p d w / 2 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_div_two]
  by_cases hi : i < 64 * w
  · rw [testBit_wv m' p d w i hi]
    by_cases hj : i / 64 + 1 < w
    · rw [hlo _ hj, BitVec.testBit_toNat, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
      by_cases hb : i % 64 < 63
      · rw [testBit_wv m p d w (i + 1) (by omega), show (i + 1) / 64 = i / 64 by omega,
          show (i + 1) % 64 = 1 + i % 64 by omega, BitVec.testBit_toNat]
        simp only [show decide (i % 64 < 63) = true from decide_eq_true hb, Bool.not_true, Bool.and_false,
          Bool.false_and, Bool.or_false]
      · rw [testBit_wv m p d w (i + 1) (by omega), show (i + 1) / 64 = i / 64 + 1 by omega,
          show (i + 1) % 64 = 0 by omega, BitVec.testBit_toNat, BitVec.getLsbD_of_ge _ _ (by omega),
          show i % 64 - 63 = 0 by omega, Nat.mul_add, Nat.mul_one]
        simp only [show decide (i % 64 < 64) = true from decide_eq_true (by omega),
          show decide (i % 64 < 63) = false from decide_eq_false hb, Bool.not_false, Bool.true_and, Bool.false_or]
    · have he : i / 64 = w - 1 := by omega
      rw [he, htop, BitVec.testBit_toNat, BitVec.getLsbD_ushiftRight]
      by_cases hb : i % 64 < 63
      · rw [testBit_wv m p d w (i + 1) (by omega), show (i + 1) / 64 = w - 1 by omega,
          show (i + 1) % 64 = 1 + i % 64 by omega, BitVec.testBit_toNat]
      · rw [BitVec.getLsbD_of_ge _ _ (by omega), Nat.testBit_lt_two_pow]
        exact Nat.lt_of_lt_of_le (wv_lt m p d w) (Nat.pow_le_pow_right (by decide) (by omega))
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (wv_lt m' p d w) (Nat.pow_le_pow_right (by decide) (by omega))),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (wv_lt m p d w) (Nat.pow_le_pow_right (by decide) (by omega)))]

end VG.Proof.Ffdh.ParameterCandidate

end

end


/-!
# An FFDH parameter candidate on PPC64LE: q

`halveQ_ok`: array 0 halved in place (p into q = (p − 1) / 2, p being odd),
and `hBad` nonzero when q is even.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search VG.Proof.MillerRabin.PPC64LE.Search

theorem low_flag (x : BitVec 64) : (x &&& 1#64) ^^^ 1#64 = 0#64 ↔ x.toNat % 2 = 1 := by
  obtain e : x &&& 1#64 = BitVec.ofNat 64 (x.toNat % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.and_one_is_mod]
    omega_arith
  rw [e]
  rcases Nat.mod_two_eq_zero_or_one x.toNat with h | h <;> rw [h] <;> decide

theorem wv_mod_two (m : Mem) (p : Addr) (d : Nat) {w : Nat} (hw : 1 ≤ w) :
    wv m p d w % 2 = (word m p d).toNat % 2 := by
  obtain e := VG.Proof.RsaKeyGen.testBit_wv m p d w 0 (by omega_arith)
  simp only [Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.zero_mod, Nat.testBit_zero, decide_eq_decide] at e
  omega_arith

/-- The registers `halveQ` writes. -/
def hqRegs : List Reg := [.r3, .r4, .r5, .r6]

/-- Word `j` of the halved number. -/
abbrev halfW (m : Mem) (B : Addr) (a j : Nat) : BitVec 64 :=
  (word m B (a + 8 * j) >>> 1) ||| (word m B (a + 8 * (j + 1)) <<< 63)

theorem halveQ_ok {p : PP} {s : State} {w x : Nat} (hs : St p s) (h10 : s.gpr .r10 = off p.B (slot w 0))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (hx : wv s.mem p.B (slot w 0) w = x) (hw2 : 2 ≤ w)
    (hw : w < 2 ^ 31) (hZ : slot w 0 + 8 * w ≤ p.Z) :
    WP isa halveQ s fun t =>
      (wv t.mem p.B (slot w 0) w = x / 2 ∧
        (word t.mem p.B (8 * hBad) = 0#64 ↔ word s.mem p.B (8 * hBad) = 0#64 ∧ x / 2 % 2 = 1) ∧
        Frm p.B [(slot w 0, 8 * w), (8 * hBad, 8)] s.mem t.mem) ∧ Keep hqRegs s t := by
  have hnw := hs.scr.nowrap
  obtain h0 : slot w 0 = 256 := by simp [slot, hdrBytes]
  rw [h0] at h10 hx hZ ⊢
  simp only [PP.Z] at hZ hnw
  unfold halveQ
  refine WP.seq (WP.mono (WP.keep [.r5, .r6] (Q := fun u => u.gpr .r5 = off p.B 256 ∧
      u.gpr .r6 = BitVec.ofNat 64 (w - 1) ∧ u.mem = s.mem) ?_ (by decide)) fun u ⟨⟨u5, u6, um⟩, ku⟩ => ?_)
  · prun [h10, h11, BitVec.add_zero]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow]
    omega_arith
  let Inv : Nat → State → Prop := fun i t =>
    (t.gpr .r5 = off p.B (256 + 8 * i) ∧ (∀ j < i, word t.mem p.B (256 + 8 * j) = halfW s.mem p.B 256 j) ∧
      (∀ j, i ≤ j → j < w → word t.mem p.B (256 + 8 * j) = word s.mem p.B (256 + 8 * j)) ∧
      Frm p.B [(256, 8 * w)] s.mem t.mem) ∧ Keep hqRegs s t
  refine WP.seq (WP.mono (wp_countdown (cnt := .r6) (N := w - 1) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨⟨t5, tlo, thi, tf⟩, kt⟩ _ => ?_)
    ⟨⟨by rw [u5], fun j hj => absurd hj (Nat.not_lt_zero _), fun j _ _ => by rw [um],
      by rw [um]; exact Frm.refl _ _ _⟩, ku.mono (by decide)⟩ u6) fun t ht => ?_)
  · have hsc : Scr t p.B (8 * p.n) := hs.scr.congr kt.wr
    obtain l0 : InRegions (t.rd ++ t.wr) (off p.B (256 + 8 * i)) 8 := hsc.ld (by omega_arith)
    obtain l1 : InRegions (t.rd ++ t.wr) (off p.B (256 + 8 * (i + 1))) 8 := hsc.ld (by omega_arith)
    obtain s0 : InRegions t.wr (off p.B (256 + 8 * i)) 8 := hsc.st (by omega_arith)
    obtain e8 : off p.B (256 + 8 * i) + BitVec.ofNat 64 8 = off p.B (256 + 8 * (i + 1)) := by
      rw [show off p.B (256 + 8 * i) + BitVec.ofNat 64 8 = off (off p.B (256 + 8 * i)) 8 from rfl, off_off,
        show 256 + 8 * i + 8 = 256 + 8 * (i + 1) by omega_arith]
    obtain r0 : t.mem.readW (off p.B (256 + 8 * i)) 64 = word s.mem p.B (256 + 8 * i) := thi i (by omega_arith) (by omega_arith)
    obtain r1 : t.mem.readW (off p.B (256 + 8 * (i + 1))) 64 = word s.mem p.B (256 + 8 * (i + 1)) :=
      thi (i + 1) (by omega_arith) (by omega_arith)
    refine WP.mono (WP.keep [.r3, .r4, .r5, .r6] (Q := fun u => u.gpr .r5 = off p.B (256 + 8 * (i + 1)) ∧
        u.mem = t.mem.writeW (off p.B (256 + 8 * i)) (halfW s.mem p.B 256 i) ∧
        u.gpr .r6 = t.gpr .r6 - BitVec.ofNat 64 1) ?_ (by decide))
      fun u ⟨⟨u5, um, u6⟩, ku⟩ => ⟨⟨⟨u5, ?_, ?_, ?_⟩, (kt.trans ku).mono (by decide)⟩, u6⟩
    · prun [t5, BitVec.add_zero, e8, l0, l1, s0, r0, r1]
    · intro j hj
      rw [um]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [word, rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]; exact tlo j hj
      · exact rw_self _ _ _
    · intro j hj hj'
      rw [um, word, rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]
      exact thi j (by omega_arith) hj'
    · rw [um]
      exact frm_writeW tf _ ⟨_, List.mem_singleton_self _, by dsimp only; omega_arith, by dsimp only; omega_arith⟩ (by omega_arith)
  obtain ⟨⟨t5, tlo, thi, tf⟩, kt⟩ := ht
  obtain hsc : Scr t p.B (8 * p.n) := hs.scr.congr kt.wr
  obtain lT : InRegions (t.rd ++ t.wr) (off p.B (256 + 8 * (w - 1))) 8 := hsc.ld (by omega_arith)
  obtain sT : InRegions t.wr (off p.B (256 + 8 * (w - 1))) 8 := hsc.st (by omega_arith)
  obtain rT : t.mem.readW (off p.B (256 + 8 * (w - 1))) 64 = word s.mem p.B (256 + 8 * (w - 1)) :=
    thi (w - 1) (by omega_arith) (by omega_arith)
  obtain h31 : t.gpr .r31 = p.B := (kt.gpr .r31 (by decide)).trans hs.r31
  obtain t10 : t.gpr .r10 = off p.B 256 := (kt.gpr .r10 (by decide)).trans h10
  obtain lB : InRegions (t.rd ++ t.wr) (p.B + BitVec.ofNat 64 200) 8 := hsc.ld (d := 200) (by omega_arith)
  obtain sB : InRegions t.wr (p.B + BitVec.ofNat 64 200) 8 := hsc.st (d := 200) (by omega_arith)
  obtain l0 : InRegions (t.rd ++ t.wr) (off p.B 256) 8 := hsc.ld (by omega_arith)
  obtain rB : ∀ v : BitVec 64, (t.mem.writeW (off p.B (256 + 8 * (w - 1))) v).readW (p.B + BitVec.ofNat 64 200) 64 =
      word s.mem p.B 200 := fun v => by
    rw [rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]
    exact tf.word_eq (fun r hr => by rw [List.mem_singleton] at hr; subst hr; dsimp only; omega_arith) (by omega_arith)
  obtain r0 : ∀ v : BitVec 64, (t.mem.writeW (off p.B (256 + 8 * (w - 1))) v).readW (off p.B 256) 64 =
      halfW s.mem p.B 256 0 := fun v => by
    rw [show off p.B 256 = off p.B (256 + 8 * 0) from rfl, rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]
    exact tlo 0 (by omega_arith)
  refine WP.mono (WP.keep [.r3, .r4, .r5] (Q := fun u => u.mem =
      (t.mem.writeW (off p.B (256 + 8 * (w - 1))) (word s.mem p.B (256 + 8 * (w - 1)) >>> 1)).writeW
        (p.B + BitVec.ofNat 64 200) (word s.mem p.B 200 ||| ((halfW s.mem p.B 256 0 &&& 1#64) ^^^ 1#64))) ?_
      (by decide)) fun u ⟨um, ku⟩ => ⟨?_, (kt.trans ku).mono (by decide)⟩
  · simp only [ldh, sth, hBad]
    prun [t5, t10, h31, BitVec.add_zero, lT, sT, rT, lB, sB, l0, rB, r0]
  obtain hv : wv u.mem p.B 256 w = x / 2 := by
    rw [← hx]
    refine Proof.Ffdh.ParameterCandidate.wv_half (by omega_arith) (fun j hj => ?_) ?_
    · rw [um, word, rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]
      exact tlo j (by omega_arith)
    · rw [um, word, rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), rw_self]
  refine ⟨hv, ?_, ?_⟩
  · have e := wv_mod_two u.mem p.B 256 (w := w) (by omega_arith)
    obtain t0 : t.mem.readW (p.B + BitVec.ofNat 64 256) 64 = halfW s.mem p.B 256 0 := tlo 0 (by omega_arith)
    rw [hv, um, word, rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith),
      t0] at e
    simp only [word, off, hBad, Nat.reduceMul, um, rw_self, BitVec.or_eq_zero_iff, low_flag]
    rw [e]
  · rw [um]
    refine frm_writeW (frm_writeW (tf.mono fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self) _
        ⟨_, List.mem_cons_self, by dsimp only; omega_arith, by dsimp only; omega_arith⟩ (by omega_arith)) _
      ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by decide, by decide⟩ (by omega_arith)

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate

end

end

/-!
# An FFDH parameter candidate on PPC64LE: the tests

`tests_ok`: one witness of p, then q's if it passed, then p's others if q
passed, and their result (`Proof.Ffdh.ParameterCandidate.sievedTests`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search VG.Proof.MillerRabin.PPC64LE.Search
open VG.Proof.MillerRabin.PPC64LE (RoundImpl)
open VG.Proof.Ffdh.ParameterCandidate (checkWitnesses onPass sievedTests)

theorem stat_one {n : Nat} (hn : n < 2 ^ 60) :
    (BitVec.ofNat 64 n - BitVec.ofNat 64 1 == 0) = decide (n = 1) := by
  by_cases h : n = 1
  · subst h; decide
  · rw [decide_eq_false h]
    apply Bool.eq_false_iff.mpr
    intro he
    have := congrArg BitVec.toNat (beq_iff_eq.mp he)
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
    have h0 : (0 : BitVec 64).toNat = 0 := rfl
    rw [h0] at this
    omega_arith

/-- `hStat` against 1. -/
theorem stat1_ok {C : Nat} {p : PP} {mb N v : Nat} {s : State} (M : MSt p mb N C s) (hv : v < 2 ^ 60)
    (hS : word s.mem p.B 160 = BitVec.ofNat 64 v) :
    WP isa (.block [ldh .r3 hStat, .subi .r3 .r3 1]) s fun t =>
      isa.eval (.zero .d .r3) t = some (decide (v = 1)) ∧ MSt p mb N C t ∧ t.mem = s.mem := by
  have l160 : InRegions (s.rd ++ s.wr) (p.B + BitVec.ofNat 64 160) 8 := M.st.ld (d := 160) (by decide)
  refine WP.mono (WP.keep [.r3] (Q := fun t => t.gpr .r3 = BitVec.ofNat 64 v - BitVec.ofNat 64 1 ∧ t.mem = s.mem)
    (by simp only [ldh, hStat]; prun [M.st.r31, l160, show s.mem.readW (p.B + BitVec.ofNat 64 160) 64 =
      BitVec.ofNat 64 v from hS]) (by decide)) fun t ⟨⟨t3, tm⟩, k⟩ => ?_
  exact ⟨by rw [eval_zero, t3, stat_one hv], M.frm (rs := []) (by rw [tm]; exact Frm.refl _ _ _) (by simp) k
    (by decide) (k.gpr _ (by decide)) (k.gpr _ (by decide)) (k.gpr _ (by decide)), tm⟩

/-- After a test that ended with `res`: the end of the candidate when it did
not pass (`qResult`), else `cont` from octet `u` of the tape. -/
theorem stage_ok {C : Nat} {p : PP} {mb N : Nat} {t₁ : State} {res : Option (Bool × List Byte)}
    {k : List Byte → Option (Option Nat × List Byte)} {cont : Prog isa} (e₁ : MrEnd p mb N C res t₁)
    (hcont : ∀ u t₂, u ≤ p.r.length → res = some (true, p.r.drop u) → MSt p mb N C t₂ → t₂.mem = t₁.mem →
      word t₂.mem p.B 152 = BitVec.ofNat 64 u → WP isa cont t₂ (CEnd p (k (p.r.drop u)))) :
    WP isa (.seq (.block [ldh .r3 hStat, .subi .r3 .r3 1]) (.ite (.zero .d .r3) cont qResult)) t₁
      (CEnd p (onPass res k)) := by
  obtain ⟨M₁, hnone, hsome⟩ := e₁
  rcases res with _ | ⟨b, rest⟩
  · refine WP.seq (WP.mono (stat1_ok M₁ (v := 0) (by decide) (hnone rfl)) fun t₂ ⟨hz, M₂, hm⟩ => ?_)
    refine WP.ite false hz (fun h => absurd h (by decide)) (fun _ => ?_)
    exact qResult_ok (resQ := none) ⟨M₂, fun _ => (by rw [hm]; exact hnone rfl), fun _ _ h => (by cases h)⟩
      (fun _ h => by cases h)
  · obtain ⟨hS, u, hul, rfl, hUu⟩ := hsome b rest rfl
    refine WP.seq (WP.mono (stat1_ok M₁ (v := if b then 1 else 2) (by cases b <;> decide) hS)
      fun t₂ ⟨hz, M₂, hm⟩ => ?_)
    cases b
    · refine WP.ite false hz (fun h => absurd h (by decide)) (fun _ => ?_)
      have e₂ : MrEnd p mb N C (some (false, p.r.drop u)) t₂ := by
        refine ⟨M₂, fun h => (by cases h), fun b' rest' h => ?_⟩
        cases h
        exact ⟨by rw [hm]; exact hS, u, hul, rfl, by rw [hm]; exact hUu⟩
      exact qResult_ok e₂ (fun _ h => by cases h)
    · refine WP.ite true hz (fun _ => ?_) (fun h => absurd h (by decide))
      exact hcont u t₂ hul rfl M₂ hm (by rw [hm]; exact hUu)

/-- q, from p in array 0. -/
theorem halveQ_from {K : Nat} {p : PP} {s : State} {c u : Nat} (M : MSt p p.bits c K s)
    (hc : c = Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L)))
    (hU : word s.mem p.B 152 = BitVec.ofNat 64 u) :
    WP isa halveQ s fun t => St p t ∧ wv t.mem p.B (slot (wOf p.bits) 0) (wOf p.bits) = (c - 1) / 2 ∧
      word t.mem p.B 152 = BitVec.ofNat 64 u := by
  have hb1 := M.st.dims.b1
  have hb2 := M.st.dims.b2
  have hdn := M.st.dims.n
  obtain ⟨hpo, _, _⟩ := VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := p.bits) (by omega_arith)
    (Spec.Rsa.os2ip (p.r.take p.L))
  rw [← hc] at hpo
  have hsl : slot (wOf p.bits) 0 = 256 := slot_zero _
  have hLe : p.L = (p.bits + 7) / 8 := rfl
  have hwe : wOf p.bits = (p.bits + 63) / 64 := rfl
  have hZe : p.Z = 8 * p.n := rfl
  have hn₂ : wv s.mem p.B (slot (wOf p.bits) 0) (wOf p.bits) = c := by
    rw [← Pre.val32_eq_wv]; exact M.prep.n
  refine WP.mono (halveQ_ok M.st M.ph.r10 M.ph.r11 hn₂ (by omega_arith) (by omega_arith)
    (by rw [hsl]; omega_arith)) fun t₃ ⟨⟨hq₃, _, f₃⟩, k₃⟩ => ⟨?_, ?_, ?_⟩
  · exact M.st.step (Frm.toMut f₃ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [hsl]; exact InMut.arrays (by decide) (by simp only [saveBytes]; omega_arith)
      · exact InMut.hdr (i := 25) (by decide)) k₃ (by decide) (by decide)
  · rw [hq₃]; omega_arith
  · rw [f₃.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [hsl]; exact .inl (by dsimp only; omega_arith)
      · exact .inl (by decide)) (by decide)]
    exact hU

/-- The tests, once the shape passed: one witness of p, all of q's, then
p's others, `used` after p's octets. -/
theorem tests_ok (R : RoundImpl) {p : PP} {s : State} {c : Nat} (h : St p s)
    (hc : c = Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L))) (hqo : ((c - 1) / 2) % 2 = 1)
    (hU : word s.mem p.B 152 = BitVec.ofNat 64 p.L) (hL : p.L ≤ p.r.length) :
    WP isa (tests R.name R.code) s (CEnd p (sievedTests c (p.r.drop p.L))) := by
  have hb1 := h.dims.b1
  have hb2 := h.dims.b2
  have hdn := h.dims.n
  have hbq : Spec.RsaKeyGen.bitLength ((c - 1) / 2) = p.bits - 1 := by
    rw [hc]; exact VG.Proof.Ffdh.ParameterCandidate.half_bitLength (by omega_arith) _
  have hbp : Spec.RsaKeyGen.bitLength c = p.bits := by
    rw [hc]; exact (VG.Proof.Ffdh.ParameterCandidate.candidate_bitLength (by omega_arith) _).1
  obtain ⟨hpo, _, hcu⟩ := VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := p.bits) (by omega_arith)
    (Spec.Rsa.os2ip (p.r.take p.L))
  rw [← hc] at hcu hpo
  unfold sievedTests tests
  rw [hbq, hbp]
  -- p's first witness.
  refine WP.seq (WP.mono (testP1_ok R h hc hU hL hL) fun t₁ e₁ => ?_)
  refine stage_ok e₁ fun u₁ t₂ hu₁ _ M₂ _ hU₂ => ?_
  -- q, from p in array 0, and its test.
  unfold testQ
  refine WP.seq (WP.mono (halveQ_from M₂ hc hU₂) fun t₃ ⟨st₃, hq₃, hU₃⟩ => ?_)
  refine WP.seq (WP.mono (testQ_ok R st₃ hc hq₃ hqo hU₃ hu₁) fun t₄ e₄ => ?_)
  refine stage_ok e₄ fun u₂ t₅ hu₂ _ M₅ _ hU₅ => ?_
  -- p's other witnesses.
  unfold testRest
  refine WP.seq (WP.mono (testPR_ok R M₅.st hc hU₅ hu₂ hL) fun t₆ e₆ => ?_)
  exact pResult_ok e₆ hcu

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate
