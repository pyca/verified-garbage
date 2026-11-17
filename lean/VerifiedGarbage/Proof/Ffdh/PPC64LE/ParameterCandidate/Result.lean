module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Mr
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Phase
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.Proof.Ffdh.Contract
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Base
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.WriteP
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMid
import VerifiedGarbage.Proof.Bignum.Octets

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
