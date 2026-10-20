module

import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.AddTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.AddCTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256Bounds
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafDigitRead
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Cache
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeStore
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Digit
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTableTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowState
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafDigit
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Table
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad

/-!
# Timing of the public NAF's digits

From two runs with the same field values in the slots the loop reads
(`FieldPair`) and the same digits, a digit's step (`digit_relCT`) and an
iteration (`step_relCT`) leak the same trace: the addresses of the table's
entries and the branches depend on the digits and on those values only.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.PubNaf

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.AArch64.PubNaf
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open Spec.Weierstrass

/-- The pieces of a digit's step whose timing taint tracking checks. -/
structure DigitChecks (K : WinCfg) : Prop where
  read : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0, .x19]))
    (.block (Naf.digitRead K))
  lookup : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0, .x2]))
    (.block (Naf.digitIndex ++ entry K))
  sign : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0, .x19]))
    (.block (Naf.signRead K))
  neg : FieldCT (.block (VG.Impl.Mont.AArch64.sub K.M K.E.y K.zero K.E.y))
  add : AddCChecks K K.D K.E K.R
  copy : FieldCT (.block (copyPt K.M.n K.R K.D))

/-- The slots the entry writes: `E`, and `R.y`, `R.z` for its cached `Z²` and `Z³`. -/
def entryW (K : WinCfg) : List Nat := jacCoords K.E ++ [K.R.y, K.R.z]

theorem entryW_other (K : WinCfg) : ∀ x ∈ entryW K, x ∈ winOther K := by
  intro x hx
  simp only [entryW, jacCoords, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with (rfl | rfl | rfl) | rfl | rfl
  · exact E_other K _ (by simp)
  · exact E_other K _ (by simp)
  · exact E_other K _ (by simp)
  · exact R_other K _ (by simp)
  · exact R_other K _ (by simp)

/-- Entry `(|b| + 1) / 2` into `E`, with the values of the table's, and its
`z`'s square and cube into `R.y` and `R.z`. -/
theorem entryFields_ok {K : WinCfg} {base : Addr} {size : Nat} {b : BitVec 8} {C : Curve}
    (hL : NafLay K size) {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base size C.p (· ∈ winSlots K) V E s) (hc : CacheOk K C base s)
    (h2 : s.gpr .x2 = b.setWidth 64) (ha1 : 1 ≤ (nafMagnitude b + 1) / 2)
    (ha8 : (nafMagnitude b + 1) / 2 ≤ 8)
    (hT : ∀ x ∈ jacCoords (K.tblPt ((nafMagnitude b + 1) / 2)), x ∈ V) :
    WP isa (.block (Naf.digitIndex ++ entry K)) s fun t =>
      ProgKeep K.M base (entryW K) s t ∧
      Inv K.M base size C.p (· ∈ winSlots K) (entryW K ++ V) (tmv C K.M.n base t) t ∧
      (tmv C K.M.n base t K.E.x, tmv C K.M.n base t K.E.y, tmv C K.M.n base t K.E.z) =
        (E (K.tblPt ((nafMagnitude b + 1) / 2)).x, E (K.tblPt ((nafMagnitude b + 1) / 2)).y,
          E (K.tblPt ((nafMagnitude b + 1) / 2)).z) ∧
      tmv C K.M.n base t K.R.y =
        E (K.tblPt ((nafMagnitude b + 1) / 2)).z * E (K.tblPt ((nafMagnitude b + 1) / 2)).z ∧
      tmv C K.M.n base t K.R.z = E (K.tblPt ((nafMagnitude b + 1) / 2)).z *
        (E (K.tblPt ((nafMagnitude b + 1) / 2)).z * E (K.tblPt ((nafMagnitude b + 1) / 2)).z) := by
  have hW := hL.win
  rw [WP.block_append_iff]
  refine WP.mono (nafIndex_ok h2) fun u ⟨u2, ku⟩ => ?_
  have hIu := hI.of_keeps ku (by decide)
  have cu := CacheUpTo.ofMem ku.mem hc
  refine WP.mono (entry_ok hL hIu.scr u2 ha1 ha8) fun t ⟨ev, er, kv, Uv⟩ => ?_
  have eEx : wordsVal t.mem base K.E.x K.M.n = wordsVal u.mem base (K.tblPt ((nafMagnitude b + 1) / 2)).x K.M.n := by
    have := ev 0 (by decide); rw [tblPt_x]; simpa using this
  have eEy : wordsVal t.mem base K.E.y K.M.n = wordsVal u.mem base (K.tblPt ((nafMagnitude b + 1) / 2)).y K.M.n := by
    have := ev 1 (by decide); rw [tblPt_y, hL.exy]; simpa using this
  have eEz : wordsVal t.mem base K.E.z K.M.n = wordsVal u.mem base (K.tblPt ((nafMagnitude b + 1) / 2)).z K.M.n := by
    have := ev 2 (by decide)
    rw [tblPt_z, hL.exz, show K.E.x + 16 * K.M.n = K.E.x + 8 * K.M.n * 2 by omega]
    exact this
  have eRy : wordsVal t.mem base K.R.y K.M.n = wordsVal u.mem base (cacheAt K ((nafMagnitude b + 1) / 2)) K.M.n := by
    have := er 0 (by decide); simpa using this
  have eRz : wordsVal t.mem base K.R.z K.M.n = wordsVal u.mem base (cacheAt K ((nafMagnitude b + 1) / 2) + 8 * K.M.n) K.M.n := by
    have := er 1 (by decide)
    rw [hL.rxz, show K.R.x + 16 * K.M.n = K.R.y + 8 * K.M.n * 1 by rw [hL.rxy]; omega]
    simpa using this
  obtain ⟨cl2, cl3, ce2, ce3⟩ := cu _ ha1 ha8
  have kp : ProgKeep K.M base (entryW K) s t := by
    refine ⟨fun r hr => ?_, kv.rd.trans ku.rd, kv.wr.trans ku.wr, kv.sp.trans ku.sp, fun x hx _ => ?_⟩
    · rw [kv.gpr r (fun h => hr (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl | rfl <;> simp [clob])), ku.gpr r (fun h => hr (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl <;> simp [clob]))]
    · rw [← ku.mem]
      exact Uv x (fun w hw => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl | rfl
        · exact hx K.E.x (by simp [entryW, jacCoords])
        · exact hx K.E.y (by simp [entryW, jacCoords])
        · exact hx K.E.z (by simp [entryW, jacCoords])
        · exact hx K.R.y (by simp [entryW])
        · exact hx K.R.z (by simp [entryW]))
  have tu : ∀ x ∈ jacCoords (K.tblPt ((nafMagnitude b + 1) / 2)), wordsVal u.mem base x K.M.n = wordsVal s.mem base x K.M.n := by
    intro x _; rw [ku.mem]
  have zu : tmv C K.M.n base u (K.tblPt ((nafMagnitude b + 1) / 2)).z = E (K.tblPt ((nafMagnitude b + 1) / 2)).z := by
    show toM _ _ _ = _; rw [tu _ (by simp [jacCoords]), hI.val _ (hT _ (by simp [jacCoords]))]
  have hlt : ∀ x ∈ entryW K, wordsVal t.mem base x K.M.n < C.p := by
    intro x hx
    simp only [entryW, jacCoords, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl) | rfl | rfl
    · rw [eEx, tu _ (by simp [jacCoords])]; exact hI.lt _ (hT _ (by simp [jacCoords]))
    · rw [eEy, tu _ (by simp [jacCoords])]; exact hI.lt _ (hT _ (by simp [jacCoords]))
    · rw [eEz, tu _ (by simp [jacCoords])]; exact hI.lt _ (hT _ (by simp [jacCoords]))
    · rw [eRy]; exact cl2
    · rw [eRz]; exact cl3
  have hEs : ∀ x ∈ entryW K, x ∈ winSlots K := fun x hx => winOther_mem (entryW_other K x hx)
  refine ⟨kp, hI.of_progKeep hW.lay kp hEs hlt, ?_, ?_, ?_⟩
  · simp only [Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · show toM _ _ _ = _; rw [eEx, tu _ (by simp [jacCoords]), hI.val _ (hT _ (by simp [jacCoords]))]
    · show toM _ _ _ = _; rw [eEy, tu _ (by simp [jacCoords]), hI.val _ (hT _ (by simp [jacCoords]))]
    · show toM _ _ _ = _; rw [eEz, tu _ (by simp [jacCoords]), hI.val _ (hT _ (by simp [jacCoords]))]
  · rw [← zu, ← ce2]; show toM _ _ _ = toM _ _ _; rw [eRy]
  · rw [← zu, ← ce3]; show toM _ _ _ = toM _ _ _; rw [eRz]

theorem pub_x0 {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop} {V : List Nat}
    {E : Nat → Fin m} {s t : State} (hp : FieldPair M base size m Sl V E s t) {r : Reg}
    (hr : r ∈ [Reg.x0]) : s.gpr r = t.gpr r := by
  simp only [List.mem_singleton] at hr; subst hr
  exact hp.left.scr.x0.trans hp.right.scr.x0.symm

/-- Registers that agree in two runs. -/
theorem agree_of {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop} {V : List Nat}
    {E : Nat → Fin m} {s t : State} (hp : FieldPair M base size m Sl V E s t) {r : Reg}
    (hr : s.gpr r = t.gpr r) : AArch64.Taint.Agree (Taint.ofRegs [.x0, r]) s t := by
  refine ⟨hp.sp, fun q hq => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact hp.left.scr.x0.trans hp.right.scr.x0.symm
  · exact hr

/-- What the entry of a digit leaves in two runs: the same values in `E` and
the slots before, and `E.z`'s square and cube in `R.y` and `R.z`. -/
def EntryPair (K : WinCfg) (C : Curve) (base : Addr) (size : Nat) (V : List Nat) (s t : State) : Prop :=
  ∃ E' : Nat → Fe C, FieldPair K.M base size C.p (· ∈ winSlots K) (entryW K ++ V) E' s t ∧
    E' K.R.y = E' K.E.z * E' K.E.z ∧ E' K.R.z = E' K.E.z * (E' K.E.z * E' K.E.z)

/-- The entry of a nonzero digit, negated for a negative one. -/
theorem signedEntry_relCT {K : WinCfg} {C : Curve} {base : Addr} {size k j : Nat}
    (hL : NafLay K size) (hm : UnitMod C.p (2^(64*K.M.n))) (hc : DigitChecks K)
    {P : Point C} {s₀ t₀ : State} (hF₁ : NafFixed K C base s₀ P k) (hF₂ : NafFixed K C base t₀ P k)
    (hj : j < 64 * K.M.n + 1) (hm0 : Naf5.magnitude k j ≠ 0)
    {V : List Nat} (hV : ∀ x ∈ winRo K ++ winTblSlots K, x ∈ V) {E : Nat → Fe C} :
    RelCT isa (fun s t => FieldPair K.M base size C.p (· ∈ winSlots K) V E s t ∧
      NSt K C base size P s₀ s ∧ NSt K C base size P t₀ t ∧
      CacheOk K C base s ∧ CacheOk K C base t ∧
      s.gpr .x19 = BitVec.ofNat 64 j ∧ t.gpr .x19 = BitVec.ofNat 64 j ∧
      s.gpr .x2 = (Naf5.byte k j).setWidth 64 ∧ t.gpr .x2 = (Naf5.byte k j).setWidth 64)
      (signedEntry K)
      (EntryPair K C base size V) := by
  have hW := hL.win
  have hmag := Naf5.magnitude_le k j
  have hodd := (Naf5.magnitude_odd_or_zero k j).resolve_left hm0
  have hma : nafMagnitude (Naf5.byte k j) = Naf5.magnitude k j := nafMagnitude_byte k j
  have ha1 : 1 ≤ (nafMagnitude (Naf5.byte k j) + 1) / 2 := by omega
  have ha8 : (nafMagnitude (Naf5.byte k j) + 1) / 2 ≤ 8 := by omega
  have hT : ∀ x ∈ jacCoords (K.tblPt ((nafMagnitude (Naf5.byte k j) + 1) / 2)), x ∈ V := by
    intro x hx
    obtain ⟨i, hi, rfl, -, -⟩ := tblPt_mem K ha1 ha8 x (by simpa [jacCoords] using hx)
    exact hV _ (List.mem_append_right _ (winTbl_mem K hi))
  have hEs : ∀ x ∈ entryW K, x ∈ winSlots K := fun x hx => winOther_mem (entryW_other K x hx)
  obtain ⟨-, -, nRyz, hRE, exy, exz, eyz, -⟩ := hW.other_ne
  have nR : ∀ x ∈ [K.R.y, K.R.z], ∀ y ∈ [K.E.x, K.E.y, K.E.z], x ≠ y := by
    intro x hx y hy e
    have hxR : x ∈ [K.R.x, K.R.y, K.R.z] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; rcases hx with rfl | rfl <;> simp
    exact hRE x hxR (by rw [e]; rcases mem3 hy with rfl | rfl | rfl <;> simp)
  have yx : K.R.y ≠ K.E.x := nR K.R.y (by simp) K.E.x (by simp)
  have yy : K.R.y ≠ K.E.y := nR K.R.y (by simp) K.E.y (by simp)
  have yz : K.R.y ≠ K.E.z := nR K.R.y (by simp) K.E.z (by simp)
  have zx : K.R.z ≠ K.E.x := nR K.R.z (by simp) K.E.x (by simp)
  have zy : K.R.z ≠ K.E.y := nR K.R.z (by simp) K.E.y (by simp)
  have zz : K.R.z ≠ K.E.z := nR K.R.z (by simp) K.E.z (by simp)
  let q := K.tblPt ((nafMagnitude (Naf5.byte k j) + 1) / 2)
  let F := fun x => if x = K.E.x then E q.x else if x = K.E.y then E q.y else if x = K.E.z then E q.z
    else if x = K.R.y then E q.z * E q.z else E q.z * (E q.z * E q.z)
  have load : RelCT isa (fun s t => FieldPair K.M base size C.p (· ∈ winSlots K) V E s t ∧
      (s.gpr .x2 = (Naf5.byte k j).setWidth 64 ∧ CacheOk K C base s) ∧
      (t.gpr .x2 = (Naf5.byte k j).setWidth 64 ∧ CacheOk K C base t))
      (.block (Naf.digitIndex ++ entry K))
      (fun s t => ∃ E', FieldPair K.M base size C.p (· ∈ winSlots K) (entryW K ++ V) E' s t) := by
    apply fieldWrite_relCT (F := F) (W := entryW K)
      (Pre := fun s => s.gpr .x2 = (Naf5.byte k j).setWidth 64 ∧ CacheOk K C base s) hW.lay hc.lookup
    · intro s t hp ps pt
      exact agree_of hp (ps.1.trans pt.1.symm)
    · exact hEs
    · intro x hx; exact List.mem_append.mp hx
    · intro s hi hp
      refine WP.mono (entryFields_ok hL hi hp.2 hp.1 ha1 ha8 hT) fun t ⟨hk, it, ht, hy, hz⟩ =>
        ⟨_, hk, it, ?_⟩
      intro x _ hx
      simp only [Prod.mk.injEq] at ht
      simp only [entryW, jacCoords, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with (rfl | rfl | rfl) | rfl | rfl
      · simpa only [F, ite_true] using ht.1
      · simpa only [F, Ne.symm exy, ite_false, ite_true] using ht.2.1
      · simpa only [F, Ne.symm exz, Ne.symm eyz, ite_false, ite_true] using ht.2.2
      · simpa only [F, yx, yy, yz, ite_false, ite_true] using hy
      · simpa only [F, zx, zy, zz, Ne.symm nRyz, ite_false] using hz
  have load' : RelCT isa (fun s t => FieldPair K.M base size C.p (· ∈ winSlots K) V E s t ∧
      NSt K C base size P s₀ s ∧ NSt K C base size P t₀ t ∧
      CacheOk K C base s ∧ CacheOk K C base t ∧
      s.gpr .x19 = BitVec.ofNat 64 j ∧ t.gpr .x19 = BitVec.ofNat 64 j ∧
      s.gpr .x2 = (Naf5.byte k j).setWidth 64 ∧ t.gpr .x2 = (Naf5.byte k j).setWidth 64)
      (.block (Naf.digitIndex ++ entry K))
      (fun s t => EntryPair K C base size V s t ∧
        NSt K C base size P s₀ s ∧ NSt K C base size P t₀ t ∧
        s.gpr .x19 = BitVec.ofNat 64 j ∧ t.gpr .x19 = BitVec.ofNat 64 j) := by
    intro s t ts tt s' t' ⟨hp, ss, st, cs, ct, s19, t19, s2, t2⟩ es et
    obtain ⟨he, E', pair⟩ := load _ _ _ _ _ _ ⟨hp, ⟨s2, cs⟩, ⟨t2, ct⟩⟩ es et
    obtain ⟨_, _, xs, ks, _, vs, ys, zs⟩ := entryFields_ok hL hp.left cs s2 ha1 ha8 hT
    obtain ⟨_, _, xt, kt, _, _, _, _⟩ := entryFields_ok hL hp.right ct t2 ha1 ha8 hT
    obtain ⟨_, rfl⟩ := Exec.det es xs
    obtain ⟨_, rfl⟩ := Exec.det et xt
    have hU : ∀ {a b : State}, ProgKeep K.M base (entryW K) a b → Unch base (loopW K) a.mem b.mem :=
      fun kk => kk.unch.mono fun w hw => by
        simp only [List.mem_append, List.mem_map, List.mem_singleton] at hw
        simp only [loopW, List.mem_append, List.mem_map, List.mem_singleton]
        rcases hw with ⟨y, hy, rfl⟩ | rfl
        · exact Or.inl ⟨y, entryW_other K y hy, rfl⟩
        · exact Or.inr rfl
    simp only [Prod.mk.injEq] at vs
    have v : ∀ x ∈ entryW K ++ V, E' x = tmv C K.M.n base s' x := fun x hx =>
      (pair.left.val x hx).symm
    have e2 : E' K.R.y = E' K.E.z * E' K.E.z := by
      rw [v _ (by simp [entryW]), v _ (by simp [entryW, jacCoords]), ys, vs.2.2]
    have e3 : E' K.R.z = E' K.E.z * (E' K.E.z * E' K.E.z) := by
      rw [v _ (by simp [entryW]), v _ (by simp [entryW, jacCoords]), zs, vs.2.2]
    exact ⟨he, ⟨E', pair, e2, e3⟩,
      ss.next hW pair.left.scr ((⟨ks.gpr, ks.rd, ks.wr, ks.sp⟩ : KeepRegs (clob K.M.n) s _).mono
        clob_nafClob) (hU ks),
      st.next hW pair.right.scr ((⟨kt.gpr, kt.rd, kt.wr, kt.sp⟩ : KeepRegs (clob K.M.n) t _).mono
        clob_nafClob) (hU kt),
      (ks.gpr _ (x19_not_clob _)).trans s19, (kt.gpr _ (x19_not_clob _)).trans t19⟩
  rw [signedEntry]
  apply RelCT.seq load'
  intro s t ts tt s' t' ⟨⟨E', hp, e2, e3⟩, ss, st, s19, t19⟩ es et
  have hb4 := hL.al.bits4
  have hbits := hW.bits
  have hdig := hL.digits
  cases es with
  | seq es₁ es₂ =>
    cases et with
    | seq et₁ et₂ =>
      obtain ⟨_, _, xs, vs, ks⟩ := nafSignRead_ok hp.left.scr (by omega) (by omega) s19 (ss.digits hL hF₁ j hj)
      obtain ⟨_, _, xt, vt, kt⟩ := nafSignRead_ok hp.right.scr (by omega) (by omega) t19 (st.digits hL hF₂ j hj)
      obtain ⟨_, rfl⟩ := Exec.det es₁ xs
      obtain ⟨_, rfl⟩ := Exec.det et₁ xt
      have he₁ := hc.sign _ _ _ _ _ _ trivial trivial (agree_of hp (s19.trans t19.symm)) es₁ et₁
      have pair₁ : FieldPair K.M base size C.p (· ∈ winSlots K) (entryW K ++ V) E' _ _ :=
        ⟨hp.left.of_keeps ks (by decide), hp.right.of_keeps kt (by decide),
          ks.sp.trans (hp.sp.trans kt.sp.symm)⟩
      have hS : ∀ x ∈ (FOp.sub K.E.y K.zero K.E.y).out :: (FOp.sub K.E.y K.zero K.E.y).ins,
          x ∈ winSlots K := by
        intro x hx
        simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact hEs _ (by simp [entryW, jacCoords])
        · exact winRo_slots K _ (by simp [winRo])
        · exact hEs _ (by simp [entryW, jacCoords])
      have hR : ∀ x ∈ (FOp.sub K.E.y K.zero K.E.y).ins, x ∈ entryW K ++ V := by
        intro x hx
        simp only [FOp.ins, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact List.mem_append_right _ (hV _ (List.mem_append_left _ (by simp [winRo])))
        · exact List.mem_append_left _ (by simp [entryW, jacCoords])
      have op : RelCT isa (FieldPair K.M base size C.p (· ∈ winSlots K) (entryW K ++ V) E')
          (.block (VG.Impl.Mont.AArch64.sub K.M K.E.y K.zero K.E.y))
          (FieldPair K.M base size C.p (· ∈ winSlots K) (K.E.y :: (entryW K ++ V))
            ((FOp.sub K.E.y K.zero K.E.y).run E')) :=
        fieldWP_relCT hc.neg fun s hi => WP.mono (fop_ok hW.lay hL.al.al hm hi hS hR)
          fun _ ⟨hk, it⟩ => ⟨it, hk.sp⟩
      have hx3 : ∀ {a : State}, a.gpr .x3 = BitVec.ofNat 64 (nafNegative (Naf5.byte k j)).toNat →
          eval (.nonzero .x .x3) a = some (nafNegative (Naf5.byte k j)) := by
        intro a ha
        change some (a.read .x .x3 != 0) = _
        rw [read_x, ha]; cases nafNegative (Naf5.byte k j) <;> decide
      cases es₂ with
      | iteT cs ys =>
        cases et₂ with
        | iteT ct yt =>
          obtain ⟨he₂, pair₂⟩ := op _ _ _ _ _ _ pair₁ ys yt
          refine ⟨by rw [he₁, he₂], _, pair₂.sub (fun _ hx => List.mem_cons_of_mem _ hx), ?_, ?_⟩
          · simp only [FOp.run, Function.update_apply, yy, Ne.symm eyz, ite_false]; exact e2
          · simp only [FOp.run, Function.update_apply, zy, Ne.symm eyz, ite_false]; exact e3
        | iteF cf _ => cases ((hx3 vs).symm.trans cs).symm.trans ((hx3 vt).symm.trans cf)
      | iteF cs ns =>
        cases et₂ with
        | iteT ct _ => cases ((hx3 vs).symm.trans cs).symm.trans ((hx3 vt).symm.trans ct)
        | iteF ct nt =>
          have hs : ∀ {a a' : State} {ta : List Leak}, Exec isa (.block []) a ta a' → a' = a ∧ ta = [] := by
            intro a a' ta ea
            cases ea with | block he => simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at he; exact ⟨he.1.symm, he.2.symm⟩
          obtain ⟨rfl, rfl⟩ := hs ns
          obtain ⟨rfl, rfl⟩ := hs nt
          exact ⟨by rw [he₁], E', pair₁, e2, e3⟩

/-- The slots a digit's step reads: the read-only ones, the table and `D`. -/
def digitLive (K : WinCfg) : List Nat := winRo K ++ winTblSlots K ++ jacCoords K.D

/-- The slots the loop reads: the read-only ones, the table and `R`. -/
def loopLive (K : WinCfg) : List Nat := winRo K ++ winTblSlots K ++ jacCoords K.R

theorem digitLive_slots (K : WinCfg) : ∀ x ∈ digitLive K, x ∈ winSlots K := by
  intro x hx
  simp only [digitLive, List.mem_append] at hx
  rcases hx with (hx | hx) | hx
  · exact winRo_slots K x hx
  · simp only [winSlots, List.mem_append]; exact Or.inr hx
  · exact winOther_mem (D_other K x (by simpa [jacCoords] using hx))

theorem loopLive_slots (K : WinCfg) : ∀ x ∈ loopLive K, x ∈ winSlots K := by
  intro x hx
  simp only [loopLive, List.mem_append] at hx
  rcases hx with (hx | hx) | hx
  · exact winRo_slots K x hx
  · simp only [winSlots, List.mem_append]; exact Or.inr hx
  · exact winOther_mem (R_other K x (by simpa [jacCoords] using hx))

/-- A digit's step: `R = D + [d_j]P`, or `R = D`. -/
theorem digit_relCT {K : WinCfg} {C : Curve} {base : Addr} {size k j : Nat}
    (hL : NafLay K size) (hm : UnitMod C.p (2^(64*K.M.n))) (hone : K.one < C.p) (hc : DigitChecks K)
    {P : Point C} {s₀ t₀ : State} (hF₁ : NafFixed K C base s₀ P k) (hF₂ : NafFixed K C base t₀ P k)
    (hj : j < 64 * K.M.n + 1) {E : Nat → Fe C} :
    RelCT isa (fun s t => FieldPair K.M base size C.p (· ∈ winSlots K) (digitLive K) E s t ∧
      NSt K C base size P s₀ s ∧ NSt K C base size P t₀ t ∧
      CacheOk K C base s ∧ CacheOk K C base t ∧
      s.gpr .x19 = BitVec.ofNat 64 j ∧ t.gpr .x19 = BitVec.ofNat 64 j)
      (PubNaf.digit K)
      (fun s t => ∃ E', FieldPair K.M base size C.p (· ∈ winSlots K) (jacCoords K.R ++ digitLive K) E' s t) := by
  have hW := hL.win
  have hb4 := hL.al.bits4
  have hbits := hW.bits
  have hdig := hL.digits
  obtain ⟨-, a2, -, -, -, -, -, -⟩ := rcbApart_naf hW
  have read : RelCT isa (fun s t => FieldPair K.M base size C.p (· ∈ winSlots K) (digitLive K) E s t ∧
      NSt K C base size P s₀ s ∧ NSt K C base size P t₀ t ∧
      CacheOk K C base s ∧ CacheOk K C base t ∧
      s.gpr .x19 = BitVec.ofNat 64 j ∧ t.gpr .x19 = BitVec.ofNat 64 j)
      (.block (Naf.digitRead K))
      (fun s t => FieldPair K.M base size C.p (· ∈ winSlots K) (digitLive K) E s t ∧
        NSt K C base size P s₀ s ∧ NSt K C base size P t₀ t ∧
        CacheOk K C base s ∧ CacheOk K C base t ∧
        s.gpr .x19 = BitVec.ofNat 64 j ∧ t.gpr .x19 = BitVec.ofNat 64 j ∧
        s.gpr .x2 = (Naf5.byte k j).setWidth 64 ∧ t.gpr .x2 = (Naf5.byte k j).setWidth 64) := by
    intro s t ts tt s' t' ⟨hp, ss, st, cs, ct, s19, t19⟩ es et
    obtain ⟨_, _, xs, vs, ks⟩ := nafRead_ok hp.left.scr (by omega) (by omega) s19 (ss.digits hL hF₁ j hj) .x2
    obtain ⟨_, _, xt, vt, kt⟩ := nafRead_ok hp.right.scr (by omega) (by omega) t19 (st.digits hL hF₂ j hj) .x2
    obtain ⟨_, rfl⟩ := Exec.det es xs
    obtain ⟨_, rfl⟩ := Exec.det et xt
    have kc : ∀ r ∈ [Reg.x2, .x16], r ∈ nafClob K.M.n := fun r hr => nafClob_mem (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp)
    exact ⟨hc.read _ _ _ _ _ _ trivial trivial (agree_of hp (s19.trans t19.symm)) es et,
      ⟨hp.left.of_keeps ks (by decide), hp.right.of_keeps kt (by decide), ks.sp.trans (hp.sp.trans kt.sp.symm)⟩,
      ss.regs hW ks kc (by decide), st.regs hW kt kc (by decide),
      CacheUpTo.ofMem ks.mem cs, CacheUpTo.ofMem kt.mem ct,
      (ks.gpr _ (by decide)).trans s19, (kt.gpr _ (by decide)).trans t19, vs, vt⟩
  rw [PubNaf.digit]
  apply RelCT.seq read
  apply RelCT.ite
  · intro s t ⟨_, _, _, _, _, _, _, s2, t2⟩
    change some (s.read .x .x2 != 0) = some (t.read .x .x2 != 0)
    rw [read_x, read_x, s2, t2]
  · -- A nonzero digit.
    intro s t ts tt s' t' ⟨⟨hp, ss, st, cs, ct, s19, t19, s2, t2⟩, hz⟩ es et
    have hm0 : Naf5.magnitude k j ≠ 0 := by
      have : (s.read .x .x2 != 0) = true := Option.some.inj hz
      rw [read_x, s2, byteTest, nafMagnitude_byte] at this
      exact of_decide_eq_true this
    have hV : ∀ x ∈ winRo K ++ winTblSlots K, x ∈ digitLive K := fun x hx =>
      List.mem_append_left _ hx
    cases es with
    | seq es₁ es₂ =>
      cases et with
      | seq et₁ et₂ =>
        obtain ⟨he₁, E', pair, e2, e3⟩ := signedEntry_relCT hL hm hc hF₁ hF₂ hj hm0 hV (E := E)
          _ _ _ _ _ _ ⟨hp, ss, st, cs, ct, s19, t19, s2, t2⟩ es₁ et₁
        have sD : ∀ x ∈ [K.D.x, K.D.y, K.D.z], x ∈ winRo K ++ winOther K :=
          fun x hx => List.mem_append_right _ (D_other K x hx)
        have sE : ∀ x ∈ [K.E.x, K.E.y, K.E.z], x ∈ winRo K ++ winOther K :=
          fun x hx => List.mem_append_right _ (E_other K x hx)
        have sl := winJ_sl (o := K.R) (p := K.D) (q := K.E) (R_other K) sD sE
        have hRV : ∀ x ∈ rcbR K.S K.D K.E, x ∈ entryW K ++ digitLive K := by
          intro x hx
          simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with h | h | h | h | h | h | h | h <;> subst h <;>
            simp [digitLive, entryW, jacCoords, winRo]
        obtain ⟨he₂, E'', pair'⟩ := addCB_relCT hW.lay hL.al.al hL.n4 hm a2 sl.1 (hL.al.low sl.2.2)
          hRV (by simp [entryW]) (by simp [entryW]) e2 e3 hone hc.add _ _ _ _ _ _ pair es₂ et₂
        refine ⟨by rw [he₁, he₂], E'', pair'.sub fun x hx => ?_⟩
        rcases List.mem_append.mp hx with hx | hx
        · exact List.mem_append_left _ hx
        · exact List.mem_append_right _ (List.mem_append_right _ hx)
  · -- A zero digit: `R = D`.
    have os : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x ∈ winSlots K := fun x hx => winOther_mem (R_other K x hx)
    have dv : ∀ x ∈ [K.D.x, K.D.y, K.D.z], x ∈ digitLive K := fun x hx =>
      List.mem_append_right _ (by simpa [jacCoords] using hx)
    exact (copyPoint_relCT hW.lay hL.al.al os dv hc.copy).mono (fun _ _ h => h.1.1)
      (fun _ _ h => ⟨_, h⟩)

/-- The pieces of an iteration whose timing taint tracking checks. -/
structure StepChecks (K : WinCfg) : Prop where
  dec : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0, .x19]))
    (.block [decCounter])
  dbl : FieldCT (fprogB K.M (dblJ K.S K.R K.D))
  digit : DigitChecks K

/-- An iteration, for the values it computes. -/
theorem stepRaw_relCT {K : WinCfg} {C : Curve} {base : Addr} {size k j : Nat}
    (hL : NafLay K size) (hm : UnitMod C.p (2^(64*K.M.n))) (hone : K.one < C.p) (hc : StepChecks K)
    {P : Point C} {s₀ t₀ : State} (hF₁ : NafFixed K C base s₀ P k) (hF₂ : NafFixed K C base t₀ P k)
    (hj : j < 64 * K.M.n + 1) :
    RelCT isa (fun s t => (∃ E, FieldPair K.M base size C.p (· ∈ winSlots K) (loopLive K) E s t) ∧
      NSt K C base size P s₀ s ∧ NSt K C base size P t₀ t ∧
      CacheOk K C base s ∧ CacheOk K C base t ∧
      s.gpr .x19 = BitVec.ofNat 64 (j + 1) ∧ t.gpr .x19 = BitVec.ofNat 64 (j + 1))
      (PubNaf.step K)
      (fun s t => ∃ E', FieldPair K.M base size C.p (· ∈ winSlots K) (loopLive K) E' s t) := by
  have hW := hL.win
  have h6 := hL.n6
  obtain ⟨-, -, -, -, a5, -, -, -⟩ := rcbApart_naf hW
  have dec : RelCT isa (fun s t => (∃ E, FieldPair K.M base size C.p (· ∈ winSlots K) (loopLive K) E s t) ∧
      NSt K C base size P s₀ s ∧ NSt K C base size P t₀ t ∧
      CacheOk K C base s ∧ CacheOk K C base t ∧
      s.gpr .x19 = BitVec.ofNat 64 (j + 1) ∧ t.gpr .x19 = BitVec.ofNat 64 (j + 1))
      (.block [decCounter])
      (fun s t => (∃ E, FieldPair K.M base size C.p (· ∈ winSlots K) (loopLive K) E s t) ∧
        NSt K C base size P s₀ s ∧ NSt K C base size P t₀ t ∧
        CacheOk K C base s ∧ CacheOk K C base t ∧
        s.gpr .x19 = BitVec.ofNat 64 j ∧ t.gpr .x19 = BitVec.ofNat 64 j) := by
    intro s t ts tt s' t' ⟨⟨E, hp⟩, ss, st, cs, ct, s19, t19⟩ es et
    obtain ⟨_, _, xs, vs, ks⟩ := decCounter_ok s (j := j + 1) (by omega) (by omega) s19
    obtain ⟨_, _, xt, vt, kt⟩ := decCounter_ok t (j := j + 1) (by omega) (by omega) t19
    obtain ⟨_, rfl⟩ := Exec.det es xs
    obtain ⟨_, rfl⟩ := Exec.det et xt
    have kc : ∀ r ∈ [Reg.x19], r ∈ nafClob K.M.n := fun r hr => nafClob_mem (by
      simp only [List.mem_singleton] at hr; subst hr; simp)
    exact ⟨hc.dec _ _ _ _ _ _ trivial trivial (agree_of hp (s19.trans t19.symm)) es et,
      ⟨E, hp.left.of_keeps ks (by decide), hp.right.of_keeps kt (by decide),
        ks.sp.trans (hp.sp.trans kt.sp.symm)⟩,
      ss.regs hW ks kc (by decide), st.regs hW kt kc (by decide),
      CacheUpTo.ofMem ks.mem cs, CacheUpTo.ofMem kt.mem ct,
      by rw [vs, Nat.add_sub_cancel], by rw [vt, Nat.add_sub_cancel]⟩
  rw [PubNaf.step]
  apply RelCT.seq dec
  intro s t ts tt s' t' ⟨⟨E, hp⟩, ss, st, cs, ct, s19, t19⟩ es et
  cases es with
  | seq es₁ es₂ =>
    cases et with
    | seq et₁ et₂ =>
      have sR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x ∈ winRo K ++ winOther K :=
        fun x hx => List.mem_append_right _ (R_other K x hx)
      have sl := winJ_sl (o := K.D) (p := K.R) (q := K.R) (D_other K) sR sR
      have hRV : ∀ x ∈ rcbR K.S K.R K.R, x ∈ loopLive K := by
        intro x hx
        simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with h | h | h | h | h | h | h | h <;> subst h <;> simp [loopLive, jacCoords, winRo]
      have e : dblJ K.S K.R K.D = ofN (dblJChoiceN false) K.S K.R K.R K.D := dblJChoice_eq false K.S K.R K.D
      have hdc := hc.dbl
      rw [e] at hdc es₁ et₁
      obtain ⟨he₁, pair₁⟩ := ofNB_relCT (base := base) (E := E) hW.lay hL.al.al hm (dblJChoiceN_ok false) a5
        sl.1 (hL.al.low sl.2.2) hRV hdc _ _ _ _ _ _ hp es₁ et₁
      -- Each run's state after the doubling.
      have side : ∀ {a a' : State} {ta : List Leak} {a₀ : State},
          Exec isa (fprogB K.M (ofN (dblJChoiceN false) K.S K.R K.R K.D)) a ta a' →
          Inv K.M base size C.p (· ∈ winSlots K) (loopLive K) E a → NSt K C base size P a₀ a →
          CacheOk K C base a → a.gpr .x19 = BitVec.ofNat 64 j →
          NSt K C base size P a₀ a' ∧ CacheOk K C base a' ∧ a'.gpr .x19 = BitVec.ofNat 64 j := by
        intro a a' ta a₀ ea ia sa ca xa
        obtain ⟨_, _, xa', ka, _⟩ := ofN_ok hW.lay hL.al.al hm (dblJChoiceN_ok false) a5 sl.1
          (hL.al.low sl.2.2) ia hRV
        obtain ⟨_, rfl⟩ := Exec.det ea xa'
        have hU : Unch base (loopW K) a.mem a'.mem := ka.unch.mono fun w hw => by
          simp only [loopW, List.mem_append, List.mem_map, List.mem_singleton] at hw ⊢
          rcases hw with ⟨y, hy, rfl⟩ | rfl
          · exact Or.inl ⟨y, rcbW_other (Or.inr (Or.inl rfl)) y hy, rfl⟩
          · exact Or.inr rfl
        exact ⟨sa.next hW (ka.scr sa.scr) ((⟨ka.gpr, ka.rd, ka.wr, ka.sp⟩ : KeepRegs (clob K.M.n) a a').mono
          clob_nafClob) hU, CacheOk.unch hW hL.cache ca hU sa.scr.nowrap, (ka.gpr _ (x19_not_clob _)).trans xa⟩
      obtain ⟨ss₁, cs₁, s19₁⟩ := side es₁ hp.left ss cs s19
      obtain ⟨st₁, ct₁, t19₁⟩ := side et₁ hp.right st ct t19
      have hDl : ∀ x ∈ digitLive K, x ∈ [K.D.x, K.D.y, K.D.z] ++ loopLive K := by
        intro x hx
        simp only [digitLive, List.mem_append] at hx
        rcases hx with (hx | hx) | hx
        · exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _ hx))
        · exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _ hx))
        · exact List.mem_append_left _ (by simpa [jacCoords] using hx)
      obtain ⟨he₂, E', pair₂⟩ := digit_relCT hL hm hone hc.digit hF₁ hF₂ hj
        _ _ _ _ _ _ ⟨pair₁.sub hDl, ss₁, st₁, cs₁, ct₁, s19₁, t19₁⟩ es₂ et₂
      refine ⟨by rw [he₁, he₂], E', pair₂.sub fun x hx => ?_⟩
      simp only [loopLive, List.mem_append] at hx
      rcases hx with (hx | hx) | hx
      · exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _ hx))
      · exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _ hx))
      · exact List.mem_append_left _ hx

end VG.Proof.Weierstrass.AArch64.PubNaf
