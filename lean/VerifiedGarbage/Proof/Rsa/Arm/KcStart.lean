module

public import VerifiedGarbage.Proof.Rsa.Arm.KeyDiv
public import VerifiedGarbage.Proof.Rsa.Arm.KcBase
import VerifiedGarbage.Proof.Rsa.Arm.KcOps
import VerifiedGarbage.Proof.Rsa.Arm.CvDivN
import VerifiedGarbage.Proof.Rsa.Arm.InvParts
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Rsa.Arm.KeyWord
import VerifiedGarbage.Proof.Rsa.Arm.KeyBits
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-! ### `Rsa.Arm.KcDiv`, which only this module used -/

section

/-! # The checks of an RSA key on ARMv7: the divisions

`divSet_ok`: `divSet a d` sets up the division of `[a]` by `[d]`, after which
`Div.code` leaves the quotient in `aVQ` and the remainder in `aVR` (`StgD`);
`ctxDiv_ok`: `r7` and `r9` again, from `w` in the division's header.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.KeyCheck
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.KeyCheck
open VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm

/-- The geometry of the divisions. -/
abbrev gDiv (g : Geo) : VG.Proof.Rsa.Arm.Div.Geometry := divGeom g.B g.Z g.w aVQ aVR aVD aVT

theorem clobbers_body : ∀ x ∈ (.r6 :: VG.Proof.Rsa.Arm.Div.clobbers), x ∈ bodyRegs := by decide

/-- The division from its set-up state. -/
theorem Stg.div_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) (hh : DivHdr s.mem g.B g.w aVQ aVR aVD aVT)
    (hfree : ∀ j ∈ live, j ∉ [aVQ, aVR, aVT]) :
    WP isa VG.Impl.Rsa.Arm.Div.code s fun t => ∃ Xq Xr,
      (0 < num s.mem g.B g.w aVD → Xr = num s.mem g.B g.w aVQ % num s.mem g.B g.w aVD ∧
        Xq = num s.mem g.B g.w aVQ / num s.mem g.B g.w aVD) ∧
      StgD g s0 (upd (upd A aVQ Xq) aVR Xr) (aVR :: aVQ :: live) c t := by
  refine WP.mono (Keys.div_ok h.ws (q := aVQ) (r := aVR) (d := aVD) (t := aVT) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hh h.vdTop)
    fun t ⟨k, r, v⟩ => ⟨num t.mem g.B g.w aVQ, num t.mem g.B g.w aVR, fun pos => ⟨(v pos).1, (v pos).2⟩, ?_⟩
  have hw := h.ws
  refine ⟨⟨hw.nowrap, by rw [r.wr]; exact hw.writable, hw.fits, hw.wpos, hw.wle,
      by rw [r.gpr _ (by decide)]; exact hw.r8⟩,
    h.keep.trans (k.mono (by decide) (by simp)), h.rest.trans (r.mono clobbers_body), ?_, ?_, ?_,
    h.vd_keep k (by decide) (by simp), h.mask_keep k (by simp)⟩
  · rw [slot_eq_of_keep k (by decide) (by simp), h.cnt]
  · intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · rw [upd_self]
    rcases List.mem_cons.mp hj with rfl | hj
    · rw [upd_ne _ _ (by decide), upd_self]
    have hn := hfree j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    rw [upd_ne _ _ hn.2.1, upd_ne _ _ hn.1, k.num (by simp; omega_using [hn]) (by simp) (hw.fit64 (h.live_lt j hj)),
      h.arrs.get hj]
  · intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · decide
    rcases List.mem_cons.mp hj with rfl | hj
    · decide
    exact h.live_lt j hj

/-- `divSet a d`, then the division: `[a] / [d]` in `aVQ`, `[a] mod [d]` in `aVR`. -/
theorem Stg.divSet_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {a d : Nat} (ha : a ∈ live) (hd : d ∈ live)
    (hfree : ∀ j ∈ live, j ∉ [aVQ, aVR, aVD, aVT]) :
    WP isa (seqs (divSet a d)) s fun u => VG.Proof.Rsa.Arm.Div.Context (gDiv g) u ∧
      WP isa VG.Impl.Rsa.Arm.Div.code u fun t => ∃ Xq Xr, (0 < A d → Xr = A a % A d ∧ Xq = A a / A d) ∧
        StgD g s0 (upd (upd A aVQ Xq) aVR Xr) (aVR :: aVQ :: live) c t := by
  have aQ : a ≠ aVQ := fun e => hfree a ha (by simp [e])
  have aD : a ≠ aVD := fun e => hfree a ha (by simp [e])
  have dQ : d ≠ aVQ := fun e => hfree d hd (by simp [e])
  have dD : d ≠ aVD := fun e => hfree d hd (by simp [e])
  unfold divSet
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (h.copy_ok (o := aVQ) (a := a) (by decide) ha (Ne.symm aQ)) fun t1 h1 => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (h1.copy_ok (o := aVD) (a := d) (by decide) (List.mem_cons_of_mem _ hd) (Ne.symm dD))
    fun t2 h2 => ?_
  show WP isa (.block (VG.Impl.Rsa.Arm.CrtValues.divHdr aVQ aVR aVD aVT)) t2 _
  rw [← List.append_nil (VG.Impl.Rsa.Arm.CrtValues.divHdr _ _ _ _)]
  refine VG.Proof.Rsa.Arm.CrtValues.divHdr_ok h2.ws (by decide) (by decide) (by decide) (by decide) h2.cnt
    fun u hu ku du ru => WP.block_nil ?_
  have h3 := h2.next hu ku (by simp) (by decide) ru opRegs_body (h2.arrs_keep ku (by simp) (by decide))
    h2.live_lt (h2.vd_keep ku (by simp) (by decide)) (h2.mask_keep ku (by decide))
  refine ⟨divGeom_ctx hu (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) du, ?_⟩
  have fq : num u.mem g.B g.w aVQ = A a := by
    rw [h3.arrs.get (by simp), upd_ne (j := aVD) _ _ (by decide), upd_self]
  have fd : num u.mem g.B g.w aVD = A d := by
    rw [h3.arrs.get (by simp), upd_self, upd_ne (j := aVQ) _ _ dQ]
  have h3' : Stg g s0 A live c u := (h3.sub (live' := live) fun j hj =>
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hj)).congr' fun j hj => by
    have hn := hfree j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    rw [upd_ne _ _ hn.2.2.1, upd_ne _ _ hn.1]
  refine WP.mono (h3'.div_ok du fun j hj => by
    have hn := hfree j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn ⊢
    exact ⟨hn.1, hn.2.1, hn.2.2.2⟩) fun t ⟨Xq, Xr, hv, ht⟩ => ⟨Xq, Xr, fun pos => ?_, ht⟩
  rw [fq, fd] at hv
  exact hv pos

end VG.Proof.Rsa.Arm.KeyCheck

end

end


/-! # The checks of an RSA key on ARMv7: the start, and `r7`–`r9` after a division

`BodyIn g v s`: what the entry leaves for the checks: the working space,
`n_len` in `r11`, `w` in the division's header and the numbers `v` in their
arrays, every other array zero. `start_ok`: the working space's registers,
`1`, the mask `p` odd, and the division of `n` by `p`.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.KeyCheck
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.KeyCheck
open VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm

structure BodyIn (g : Geo) (v : Vals) (s : State) : Prop where
  nowrap : g.B.toNat + g.Z ≤ 2 ^ 32
  writable : (⟨State.addr g.B, g.Z⟩ : Region) ∈ s.wr
  fits : arr g.w nArr ≤ g.Z
  kb : 64 ≤ g.K ∧ g.K ≤ 1024
  r8 : s.gpr .r8 = g.B
  r11 : s.gpr .r11 = BitVec.ofNat 32 g.K
  cnt : s.mem.readW (off (State.addr g.B) 16) 32 = BitVec.ofNat 32 g.w
  arrs : Arrs s.mem g.B g.w (vals v) (List.range nArr)
  vdTop : w32 s.mem (State.addr g.B) (arr g.w aVD + 4 * g.w) = 0

/-- `stride`: `r7 = 4 (r9 + 2)`. -/
theorem stride_ok {s : State} {w : Nat} (_hw : w ≤ 1024) (h9 : s.gpr .r9 = BitVec.ofNat 32 w)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, t.gpr .r7 = BitVec.ofNat 32 (S w) → Rest [.r7] s t → t.mem = s.mem → WP isa (.block rest) t Q) :
    WP isa (.block (stride ++ rest)) s Q := by
  unfold stride
  simp only [List.cons_append, List.nil_append]
  refine wp_dp (op2_imm (by decide)) fun s1 u1 => ?_
  refine wp_mov (op2_lsl (by decide)) fun t u2 => ?_
  refine k t ?_ ((u1.rest (by simp)).trans (u2.rest (by simp))) (u2.mem.trans u1.mem)
  rw [u2.gpr, u1.gpr, dpVal, h9]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show (2 : BitVec 32).toNat = 2 from rfl]
  simp only [S]
  omega_using []

/-- `ctxDiv`: `r7` and `r9` again after a division. -/
theorem StgD.ctx_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : StgD g s0 A live c s) : WP isa (.block ctxDiv) s (Stg g s0 A live c) := by
  have hw := h.ws
  have hz := Nat.le_trans (Nat.le_add_right hdr _) hw.fits
  have nw := hw.nowrap
  simp only [hdr] at hz
  unfold ctxDiv
  refine wp_ldr (by decide) (by rw [hw.r8]; exact VG.Arm.addr_add (by omega_using [hz, nw]))
    ⟨_, List.mem_append_right _ hw.writable, Offset.contains_base _ (by omega_using [hz]) (by omega_using [])⟩ fun s1 u1 => ?_
  have h9 : s1.gpr .r9 = BitVec.ofNat 32 g.w := by rw [u1.gpr, h.cnt]
  rw [← List.append_nil stride]
  refine stride_ok hw.wle h9 fun t h7 r m => WP.block_nil ?_
  have r1 : Rest [.r9, .r7] s t := (u1.rest (by simp)).trans (r.mono (by simp))
  have mt : t.mem = s.mem := m.trans u1.mem
  refine ⟨⟨hw.nowrap, by rw [r1.wr]; exact hw.writable, hw.fits, hw.wpos, hw.wle, h7,
      by rw [r1.gpr _ (by decide)]; exact hw.r8, by rw [r.gpr _ (by decide)]; exact h9⟩,
    by rw [mt]; exact h.keep, h.rest.trans (r1.mono (by decide)), by rw [mt]; exact h.cnt,
    by rw [mt]; exact h.arrs, h.live_lt, by rw [mt]; exact h.vdTop, by rw [mt]; exact h.mask⟩

/-- The arrays first tracked. -/
abbrev live0 : List Nat := [aZ, aOne, aN, aE, aP, aQ, aDP, aDQ, aQI, aD]

/-- The block that starts the checks: `ctxK`, `1`, and the mask `p` odd. -/
theorem first_ok {g : Geo} {v : Vals} {s : State} (h : BodyIn g v s) :
    WP isa (.block (ctxK ++ setOne aOne ++ bitOf sMask aP)) s
      (Stg g s (upd (vals v) aOne 1) live0 (decide (v.p % 2 = 1))) := by
  have kb := h.kb
  have hw16 : 16 ≤ g.w ∧ g.w ≤ 256 := by simp only [Geo.w]; omega_using [kb]
  unfold ctxK
  simp only [List.append_assoc, List.cons_append]
  refine wp_dp (op2_imm (by decide)) fun s1 u1 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s2 u2 => ?_
  have h9 : s2.gpr .r9 = BitVec.ofNat 32 g.w := by
    rw [u2.gpr, u1.gpr, dpVal, h.r11]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_add, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, show (3 : BitVec 32).toNat = 3 from rfl]
    simp only [Geo.w]
    omega_using [kb]
  refine stride_ok (by omega_using [hw16]) h9 fun s3 h7 r3 m3 => ?_
  have r12 : Rest [.r9, .r7] s s3 := (u1.rest (by simp)).trans ((u2.rest (by simp)).trans (r3.mono (by simp)))
  have m12 : s3.mem = s.mem := m3.trans (u2.mem.trans u1.mem)
  have ws : Ws s3 g.B g.Z g.w nArr :=
    ⟨h.nowrap, by rw [r12.wr]; exact h.writable, h.fits, by omega_using [hw16], by omega_using [hw16], h7,
      by rw [r12.gpr _ (by decide), h.r8], by rw [r3.gpr _ (by decide), h9]⟩
  refine setOne_ok ws (j := aOne) (by decide) (by decide) fun s4 h4 k4 e4 r4 => ?_
  rw [← List.append_nil (bitOf sMask aP)]
  refine bitOf_ok h4 (j := aP) (by decide) (by decide) (by decide) fun t ht k5 e5 r5 => WP.block_nil ?_
  have fit := fun j (hj : j < nArr) => ws.fit64 (j := j) hj
  have a3 : Arrs s3.mem g.B g.w (vals v) live0 := by
    rw [m12]; exact h.arrs.sub (by decide)
  have a4 : Arrs s4.mem g.B g.w (upd (vals v) aOne 1) live0 := by
    refine a3.write k4 ws ?_ (by decide) (by simp)
    rw [e4, a3.get (by decide), show vals v aOne = 0 by simp [vals, upd, aN, aE, aP, aQ, aDP, aDQ, aQI, aD, aOne]]
  have p4 : num s4.mem g.B g.w aP = v.p := by rw [a4.get (by decide)]; rfl
  refine ⟨ht, (k4.mono (by decide) (by simp)).trans (k5.mono (by simp) (by decide)) |> (m12 ▸ ·), ?_, ?_,
    a4.keep k5 ht (by decide) (by decide), by decide, ?_, ?_⟩
  · exact (r12.mono (by decide)).trans ((r4.mono (by decide)).trans (r5.mono (by decide)))
  · rw [slot_eq_of_keep k5 (by decide) (by decide), slot_eq_of_keep k4 (by decide) (by simp), m12, h.cnt]
  · rw [k5.word (by simp only [S]; omega_using []) (by simp) (by decide) (fit _ (by decide)),
      k4.word (by simp only [S]; omega_using []) (by decide) (by simp) (fit _ (by decide)), m12, h.vdTop]
  · rw [e5, p4]
    rcases Nat.mod_two_eq_zero_or_one v.p with e | e <;> simp [e]

/-- `start`: the first block, and the division of `n` by `p` set up; then the division. -/
theorem start_ok {g : Geo} {v : Vals} {s : State} (h : BodyIn g v s) :
    WP isa start s fun u => VG.Proof.Rsa.Arm.Div.Context (gDiv g) u ∧
      WP isa VG.Impl.Rsa.Arm.Div.code u fun t => ∃ Xq Xr, (0 < v.p → Xr = v.n % v.p ∧ Xq = v.n / v.p) ∧
        StgD g s (upd (upd (upd (vals v) aOne 1) aVQ Xq) aVR Xr) (aVR :: aVQ :: live0) (decide (v.p % 2 = 1)) t := by
  unfold start
  rw [List.singleton_append, wp_seqs_cons (by simp [divSet])]
  exact WP.mono (first_ok h) fun u hu => hu.divSet_ok (a := aN) (d := aP) (by decide) (by decide) (by decide)

end VG.Proof.Rsa.Arm.KeyCheck
