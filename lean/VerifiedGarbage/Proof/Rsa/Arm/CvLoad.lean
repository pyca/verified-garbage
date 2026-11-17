module

public import VerifiedGarbage.Proof.Rsa.Arm.CvFail
import VerifiedGarbage.Proof.Framework.Arm.Spill
import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheck
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Bignum.Arm.LoadBE
import VerifiedGarbage.Proof.Rsa.KeyWorkspace
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Rsa.Arm.KeyWs
public import VerifiedGarbage.Proof.Rsa.Arm.DivReduce
import VerifiedGarbage.Proof.Rsa.Arm.DivLoop
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Rsa.KeyMath

/-! ### `Rsa.Arm.KeyDiv`, which this module and modules that import it used -/

section

/-! # The division of `Impl/Rsa/Arm/Div.lean` on arrays of the key working space

With the division's header (bytes 0–19) naming the arrays `q`, `r`, `d`
and `t` and the count `w`, and the word after `[d]` zero, `div_ok`:
`[q] := [q] / [d]` and `[r] := [q] mod [d]` for `[d] > 0`.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Keys
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Proof.Rsa.Arm.Div
open VG.Proof.X25519.Arm

/-- The division's geometry on arrays `q`, `r`, `d`, `t`. -/
def divGeom (B : BitVec 32) (Z w q r d t : Nat) : Geometry where
  base := B
  size := Z
  offsets i := match i.val with | 0 => arr w q | 1 => arr w r | 2 => arr w d | _ => arr w t
  n := w

theorem divGeom_o0 {B : BitVec 32} {Z w q r d t : Nat} : (divGeom B Z w q r d t).offsets 0 = arr w q := rfl
theorem divGeom_o1 {B : BitVec 32} {Z w q r d t : Nat} : (divGeom B Z w q r d t).offsets 1 = arr w r := rfl
theorem divGeom_o3 {B : BitVec 32} {Z w q r d t : Nat} : (divGeom B Z w q r d t).offsets 3 = arr w t := rfl
theorem divGeom_base {B : BitVec 32} {Z w q r d t : Nat} : (divGeom B Z w q r d t).base = B := rfl
theorem divGeom_n {B : BitVec 32} {Z w q r d t : Nat} : (divGeom B Z w q r d t).n = w := rfl

/-- The division's header in memory. -/
structure DivHdr (m : Mem) (B : BitVec 32) (w q r d t : Nat) : Prop where
  q : m.readW (off (State.addr B) 0) 32 = B + BitVec.ofNat 32 (arr w q)
  r : m.readW (off (State.addr B) 4) 32 = B + BitVec.ofNat 32 (arr w r)
  d : m.readW (off (State.addr B) 8) 32 = B + BitVec.ofNat 32 (arr w d)
  t : m.readW (off (State.addr B) 12) 32 = B + BitVec.ofNat 32 (arr w t)
  n : m.readW (off (State.addr B) 16) 32 = BitVec.ofNat 32 w

theorem divGeom_ctx {s : State} {B : BitVec 32} {Z w N q r d t : Nat} (h : Ws s B Z w N)
    (hq : q < N) (hr : r < N) (hd : d < N) (ht : t < N)
    (hqr : q ≠ r) (hqd : q ≠ d) (hqt : q ≠ t) (hrd : r ≠ d) (hrt : r ≠ t) (hdt : d ≠ t)
    (hh : DivHdr s.mem B w q r d t) : Context (divGeom B Z w q r d t) s := by
  have fq := h.arr_fit hq
  have fr := h.arr_fit hr
  have fd := h.arr_fit hd
  have ft := h.arr_fit ht
  have hS : S w = 4 * (w + 2) := rfl
  have hw := h.wle
  have hf : 20 ≤ Z := by have := h.hdr_le; simp only [hdr] at this; omega_arith
  refine ⟨⟨h.nowrap, h.writable⟩, h.wpos, by rw [divGeom_n]; omega_arith, hf, ?_, ?_, ?_, h.r8, ?_, hh.n⟩
  · intro i; rcases i with ⟨_ | _ | _ | _ | i, hi⟩ <;> simp only [divGeom, Geometry.words] <;>
      (try split) <;> first | omega_arith | (simp at hi; omega_arith) | (simp at *)
  · intro i
    have e : ∀ x, 20 ≤ arr w x := fun x => Nat.le_trans (by decide : 20 ≤ hdr) (Nat.le_add_right _ _)
    rcases i with ⟨_ | _ | _ | _ | i, hi⟩ <;> simp only [divGeom] <;> first | exact e _ | (simp at hi)
  · intro i j hij
    -- Keep the arithmetic solver independent of the workspace and memory facts.
    have qr := arr_disj (w := w) hqr; have qd := arr_disj (w := w) hqd; have qt := arr_disj (w := w) hqt
    have rd := arr_disj (w := w) hrd; have rt := arr_disj (w := w) hrt; have dt := arr_disj (w := w) hdt
    rcases i with ⟨_ | _ | _ | _ | i, hi⟩ <;> rcases j with ⟨_ | _ | _ | _ | j, hj⟩ <;>
      simp only [divGeom, Geometry.words, Fin.mk.injEq, ne_eq, not_true_eq_false] at hij ⊢ <;>
      (try split) <;> (try split) <;>
      first | omega_using [qr, qd, qt, rd, rt, dt, hij, hi, hj, hS] | (exact absurd rfl hij) | (simp at hi) | (simp at hj)
  · intro i; rcases i with ⟨_ | _ | _ | _ | i, hi⟩
    · exact hh.q
    · exact hh.r
    · exact hh.d
    · exact hh.t
    · omega_arith

theorem val32_top {m : Mem} {base : Addr} {d w : Nat} (h : w32 m base (d + 4 * w) = 0) :
    val32 m base d (w + 1) = val32 m base d w := by
  rw [val32_succ, h, Nat.mul_zero, Nat.add_zero]

theorem val32_low {m : Mem} {base : Addr} {d w : Nat} (h : val32 m base d (w + 1) < 2 ^ (32 * w)) :
    val32 m base d w = val32 m base d (w + 1) := by
  rw [val32_succ] at h ⊢
  have := val32_lt m base d w
  rcases Nat.eq_zero_or_pos (w32 m base (d + 4 * w)) with e | e
  · rw [e, Nat.mul_zero, Nat.add_zero]
  · exfalso
    have : 2 ^ (32 * w) ≤ 2 ^ (32 * w) * w32 m base (d + 4 * w) := Nat.le_mul_of_pos_right _ e
    omega_arith

theorem div_ok {s : State} {B : BitVec 32} {Z w N q r d t : Nat} (h : Ws s B Z w N)
    (hq : q < N) (hr : r < N) (hd : d < N) (ht : t < N)
    (hqr : q ≠ r) (hqd : q ≠ d) (hqt : q ≠ t) (hrd : r ≠ d) (hrt : r ≠ t) (hdt : d ≠ t)
    (hh : DivHdr s.mem B w q r d t) (top : w32 s.mem (State.addr B) (arr w d + 4 * w) = 0) :
    WP isa Impl.Rsa.Arm.Div.code s fun u => Keep B w [q, r, t] [] s.mem u.mem ∧
      Rest (.r6 :: clobbers) s u ∧
      (0 < num s.mem B w d → num u.mem B w r = num s.mem B w q % num s.mem B w d ∧
        num u.mem B w q = num s.mem B w q / num s.mem B w d) := by
  have c := divGeom_ctx h hq hr hd ht hqr hqd hqt hrd hrt hdt hh
  refine WP.mono (code_ok c) fun u ⟨_, fr, rest, v⟩ => ⟨?_, rest, fun pos => ?_⟩
  · intro x hx
    refine fr x fun rg hrg => ?_
    simp only [Geometry.ranges, divGeom_o0, divGeom_o1, divGeom_o3, divGeom_n, List.mem_cons,
      List.not_mem_nil, or_false] at hrg
    have hS : S w = 4 * (w + 2) := rfl
    rw [divGeom_base]
    rcases hrg with rfl | rfl | rfl
    · have := hx (arr w q, S w) (by simp [ranges]); dsimp only; omega_arith
    · have := hx (arr w r, S w) (by simp [ranges]); dsimp only; omega_arith
    · have := hx (arr w t, S w) (by simp [ranges]); dsimp only; omega_arith
  · have eD : (divGeom B Z w q r d t).value s.mem 2 = num s.mem B w d := val32_top top
    have lt := val32_lt s.mem (State.addr B) (arr w d) w
    have v' := v (by rw [eD]; exact pos) (by rw [eD]; exact lt)
    rw [eD] at v'
    obtain ⟨vr, vq⟩ := v'
    refine ⟨?_, vq⟩
    have : (divGeom B Z w q r d t).value u.mem 1 < 2 ^ (32 * w) := by
      rw [vr]; exact Nat.lt_of_lt_of_le (Nat.mod_lt _ pos) (Nat.le_of_lt lt)
    exact (val32_low this).trans vr

end VG.Proof.Rsa.Arm.Keys

end

end

/-! ### `Rsa.Arm.CvEntry`, which only this module used -/

section

/-! # `vg_rsa_crt_values` on ARMv7: the entry

The registers are saved in the header, and `n` checked (`entry_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.CrtValues
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.CrtValues
open VG.Proof.Rsa.Arm.Keys VG.Proof.Bignum.Arm VG.Arm.Spill VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm

/-- The registers saved, and where. -/
def saveL : List (Reg × Nat) :=
  [(.r4, 20), (.r5, 24), (.r6, 28), (.r7, 32), (.r8, 36), (.r9, 40), (.r10, 44), (.r11, 48), (.lr, 52),
   (.r0, 56), (.r2, 60)]

theorem entry_eq : entry = .ldrSp .r12 (4 * 10) :: (saveL.map (fun p => Instr.str p.1 .r12 p.2) ++
    (([.mov .r8 (.reg .r12), .mov .r3 (.reg .r2)] : List Instr) ++ (.ldrSp .r4 (4 * 2) :: .ldrSp .r6 (4 * 3) :: modulusCheck))) := rfl

theorem saveL_mem {i : Nat} (hi : i < 11) : (savedReg i, 20 + 4 * i) ∈ saveL := by
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10)
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The bytes of `n`. -/
abbrev nBytes (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 2)) (cvK s)

theorem entry_ok {s0 : State} (h : CvPre s0) :
    WP isa (.block entry) s0 fun t => Base s0 t ∧ t.gpr .r8 = cvB s0 ∧ t.gpr .r0 = s0.gpr .r0 ∧
      t.gpr .r3 = s0.gpr .r2 ∧ t.gpr .r6 = stackArg s0 3 ∧
      t.z = Spec.Rsa.modulusValid (Spec.Rsa.os2ip (nBytes s0)) (cvK s0) := by
  have fS := h.fS
  have fits := h.fits
  have kb := h.kb
  rw [entry_eq]
  obtain hrd : rA s0 ∈ s0.rd := by rw [h.rd]; simp
  refine wp_ldrSp hrd h.sp48 (by decide) fun s1 u1 => ?_
  obtain hz : 64 ≤ cvZ s0 := Nat.le_trans (by simp only [arr, hdr, nArr, S]; omega_using []) fits
  refine save_slots_ok (lo := 20) (hi := 64) (by decide) (by rw [u1.gpr]; simp only [cvZ] at hz; omega_using [fS, hz])
    (fun d h1 h2 => ⟨rS s0, by rw [u1.wr, h.wr]; simp, by
      rw [u1.gpr]; exact Offset.contains_base _ (by simp only [cvZ] at hz; omega_using [hz, h2]) (by omega_using [h2])⟩) ?_
  -- The state after the stores.
  obtain b2 : Base s0 { s1 with mem := saveMem s1.mem (State.addr (s1.gpr .r12)) s1.gpr saveL } := by
    refine ⟨h, u1.sp, u1.rd, u1.wr, ?_, fun i hi => ?_⟩
    · rw [u1.gpr]
      refine Frame.sub (rs := [⟨State.addr (stackArg s0 10), 64⟩]) ?_ fun r hr => ⟨rS s0, by simp, ?_⟩
      · rw [← u1.mem]
        exact saveMem_frame _ _ _ (by decide) _ (by decide)
      · simp only [List.mem_singleton] at hr; subst hr
        exact Region.sub_prefix (by simp only [cvZ] at hz; omega_using [hz])
    · have sv := saveMem_saved (lo := 20) (hi := 64) (State.addr (s1.gpr .r12)) s1.gpr s1.mem saveL (by decide)
        _ (saveL_mem hi)
      simp only [u1.gpr] at sv
      show ((saveMem s1.mem (State.addr (s1.gpr .r12)) s1.gpr saveL).readW
        (off (State.addr (cvB s0)) (20 + 4 * i)) 32).toNat = _
      rw [u1.gpr]
      erw [sv]
      have : savedReg i ≠ .r12 := by
        rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10)
          with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [u1.other _ this]
  refine wp_mov (op2_reg _ _) fun s3 u3 => ?_
  refine wp_mov (op2_reg _ _) fun s4 u4 => ?_
  obtain b4 := (b2.of_rest (u3.rest (ws := [.r8, .r3]) (by simp)) u3.mem).of_rest (u4.rest (ws := [.r3]) (by simp)) u4.mem
  obtain sp4 : s4.sp.toNat + 48 ≤ 2 ^ 32 := by rw [b4.sp]; exact h.sp48
  refine wp_ldrSp b4.rA_mem sp4 (by decide) fun s5 u5 => ?_
  obtain b5 := b4.of_rest (u5.rest (ws := [.r4]) (by simp)) u5.mem
  refine wp_ldrSp b5.rA_mem (by rw [b5.sp]; exact h.sp48) (by decide) fun s6 u6 => ?_
  obtain b6 := b5.of_rest (u6.rest (ws := [.r6]) (by simp)) u6.mem
  have nfit := h.fN
  refine WP.mono (modulusCheck_ok s6 (src := stackArg s0 2) (k := cvK s0) kb.1 kb.2 (by simp only [cvK]; omega_using [nfit])
    ?_ (by rw [u6.other _ (by decide), u5.gpr, b4.arg (by decide)])
    (by rw [u6.gpr, b5.arg (by decide)]; simp only [cvK, BitVec.ofNat_toNat, BitVec.setWidth_eq])) ?_
  · refine ⟨rN s0, List.mem_append_left _ (by rw [b6.rd, h.rd]; simp), Region.contains_self _ _⟩
  · rintro t ⟨z, m, r⟩
    obtain bt := b6.of_rest r m
    refine ⟨bt, ?_, ?_, ?_, ?_, ?_⟩
    · rw [r.gpr _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.gpr,
        u1.gpr]
    · rw [r.gpr _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide),
        u3.other _ (by decide)]
      exact u1.other _ (by decide)
    · rw [r.gpr _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.gpr, u3.other _ (by decide)]
      exact u1.other _ (by decide)
    · rw [r.gpr _ (by decide), u6.gpr, b5.arg (by decide)]
    · have e : Spec.Rsa.bytesAt s6.mem (State.addr (stackArg s0 2)) (cvK s0) = nBytes s0 := by
        unfold Spec.Rsa.bytesAt
        refine List.map_congr_left fun i hi => ?_
        simp only [List.mem_range] at hi
        exact b6.frame.bytes (R := rN s0)
          (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.nS) (by simp; omega_using []) hi
      rw [z, e]

end VG.Proof.Rsa.Arm.CrtValues

end

end


/-! # `vg_rsa_crt_values` on ARMv7: reading the numbers into arrays -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.CrtValues
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.CrtValues
open VG.Proof.Rsa.Arm.Keys VG.Proof.Bignum.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm

theorem val32_off (m : Mem) (base : Addr) (d : Nat) : ∀ (e n : Nat),
    val32 m (off base d) e n = val32 m base (d + e) n
  | _, 0 => rfl
  | e, n + 1 => by
    rw [val32, val32, val32_off m base d (e + 4) n, show d + (e + 4) = d + e + 4 by omega_using []]
    simp only [w32, off, Offset.add_add]

alias val32_zero_part := VG.Proof.Rsa.KeyWorkspace.val32_zero_part

theorem val32_low2 {m : Mem} {base : Addr} {d w : Nat} (h : val32 m base d (w + 2) < 2 ^ (32 * w)) :
    val32 m base d w = val32 m base d (w + 2) := by
  obtain h1 : val32 m base d (w + 1) = val32 m base d (w + 2) :=
    val32_low (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (by omega_using [])))
  rw [← h1] at h ⊢
  exact val32_low h

theorem Keep.of_frame_arr {B : BitVec 32} {w j : Nat} {m m' : Mem}
    (h : Frame [⟨off (State.addr B) (arr w j), S w⟩] m m') (fit : arr w j + S w ≤ 2 ^ 64) :
    Keep B w [j] [] m m' := by
  intro x hx
  refine h x fun r hr hc => ?_
  simp only [List.mem_singleton] at hr; subst hr
  have := hx (arr w j, S w) (by simp [ranges])
  simp only [Region.Contains, off] at hc
  have := (Offset.lt_iff x (State.addr B) (d := arr w j) (n := S w) fit).mp (by omega_using [hc])
  simp only [ofs] at *
  omega_arith

/-- An input buffer: readable, apart from the working space, and short enough. -/
structure Input (s0 : State) (R : Region) (src : BitVec 32) (k : Nat) : Prop where
  base : R = ⟨State.addr src, k⟩
  rd : R ∈ s0.rd
  sep : R.Disjoint (rS s0)
  fit : src.toNat + k ≤ 2 ^ 32
  pos : 0 < k
  le : k ≤ cvK s0

/-- `load j`: array `j` := the `k` bytes at `r4` (`r6 = k`). -/
theorem load_ok {s0 s : State} (h : Base s0 s) (hw : Ws s (cvB s0) (cvZ s0) (cvW s0) nArr) {j : Nat}
    (hj : j < nArr) {R : Region} {src : BitVec 32} {k : Nat} (hi : Input s0 R src k)
    (p4 : s.gpr .r4 = src) (p6 : s.gpr .r6 = BitVec.ofNat 32 k) :
    WP isa (load j) s fun t => Base s0 t ∧ Ws t (cvB s0) (cvZ s0) (cvW s0) nArr ∧
      Keep (cvB s0) (cvW s0) [j] [] s.mem t.mem ∧
      val32 t.mem (State.addr (cvB s0)) (arr (cvW s0) j) (cvW s0 + 2) =
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (State.addr src) k) ∧
      Rest [.r0, .r1, .r2, .r3, .r5, .lr] s t := by
  have pre := h.pre
  obtain fit := hw.arr_fit hj
  have nw := hw.nowrap
  have w16 := pre.w16
  have kb := pre.kb
  have hS : S (cvW s0) = 4 * (cvW s0 + 2) := rfl
  obtain hkw : k ≤ 4 * cvW s0 := by have := hi.le; simp only [cvW] at *; omega_using [this]
  rw [load, WP.seq_iff]
  refine ptr_ok hw (by decide) (by simp only [nArr] at hj; omega_using [hj]) fun s1 p1 r1 m1 h1 => ?_
  refine wp_mov (op2_reg _ _) fun s2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun s3 u3 => ?_
  refine wp_mov (op2_imm (by decide)) fun u u4 => WP.block_nil ?_
  obtain rest : Rest [.r0, .r3, .r5, .lr] s u :=
    (r1.mono (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans (u4.rest (by simp))))
  obtain mu : u.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, m1]
  obtain bu := h.of_rest rest mu
  obtain hu := hw.rest rest
  obtain ad : State.addr (cvB s0 + BitVec.ofNat 32 (arr (cvW s0) j)) = off (State.addr (cvB s0)) (arr (cvW s0) j) :=
    hw.addr (by omega_using [fit, hS])
  obtain p0 : u.gpr .r0 = cvB s0 + BitVec.ofNat 32 (arr (cvW s0) j) := by
    rw [u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), p1]
  refine WP.mono (loadBE_ok u (src := src) (dst := cvB s0 + BitVec.ofNat 32 (arr (cvW s0) j)) (n := cvW s0 + 2)
    hi.pos (by omega_using [hkw]) (by have := hi.fit; omega_using [w16, hkw]) hi.fit
    (by rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat]; omega_using [fit, nw, hS]), BitVec.toNat_ofNat]; omega_using [fit, nw, hS])
    ⟨R, List.mem_append_left _ (by rw [bu.rd]; exact hi.rd), by rw [hi.base]; exact Region.contains_self _ _⟩
    ⟨rS s0, by rw [bu.wr, pre.wr]; simp, by rw [ad]; exact Offset.contains_base _ (by omega) (by omega_using [fit, nw])⟩
    (by rw [← hi.base, ad]
        refine fun a ha hb => hi.sep a ha ?_
        exact Region.Contains.byte (r := rS s0) (b := off (State.addr (cvB s0)) (arr (cvW s0) j)) (n := 4 * (cvW s0 + 2))
          (Offset.contains_base _ (by omega) (by omega_using [fit, nw])) (by simp only [Region.Contains] at hb; omega_using [hb]))
    p0 (by rw [rest.gpr _ (by decide), p4])
    (by rw [u4.other _ (by decide), u3.other _ (by decide), u2.gpr, p1])
    (by rw [rest.gpr _ (by decide), p6])
    (by rw [u4.other _ (by decide), u3.gpr, dpVal, u2.other .r9 (by decide), r1.gpr .r9 (by decide), hw.r9,
          BitVec.ofNat_add]; rfl)
    (by rw [u4.gpr])) ?_
  rintro t ⟨v, f, r⟩
  rw [ad] at f v
  obtain k : Keep (cvB s0) (cvW s0) [j] [] u.mem t.mem := Keep.of_frame_arr f (by omega_using [fit, nw])
  refine ⟨bu.keep k (by simpa using hj) (by simp) (by simp) r.sp r.rd r.wr, hu.rest r, mu ▸ k, ?_,
    (rest.mono (by simp)).trans (r.mono (by simp))⟩
  rw [val32_off, Nat.add_zero] at v
  rw [v, mu, bytes_frame h.frame (by simpa [← hi.base] using hi.sep) (by omega_using [w16, hkw])]

end VG.Proof.Rsa.Arm.CrtValues

namespace VG.Proof.Rsa.Arm.CrtValues
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.CrtValues
open VG.Proof.Rsa.Arm.Keys VG.Proof.Bignum.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm

/-- A store outside the header's saved words keeps `Base`. -/
theorem Base.outside {s0 s t : State} (h : Base s0 s) {o n : Nat}
    (hf : Outside (State.addr (cvB s0)) o n s.mem t.mem) (ho : o + n ≤ 20 ∨ 64 ≤ o) (hn : o + n ≤ cvZ s0)
    (sp : t.sp = s.sp) (rd : t.rd = s.rd) (wr : t.wr = s.wr) : Base s0 t := by
  have fS := h.pre.fS
  refine ⟨h.pre, sp.trans h.sp, rd.trans h.rd, wr.trans h.wr, h.frame.trans fun x hx => ?_, fun i hi => ?_⟩
  · exact hf x (.inr (Nat.le_trans hn (out_of_ofs (by simpa using hx))))
  · rw [← h.saved i hi]
    exact hf.w32 (d := 20 + 4 * i) (by omega_using [ho, hi]) (by simp only [cvZ] at hn; omega_using [hi])

abbrev pBytes (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 4)) (cvPl s)
abbrev qBytes (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 6)) (cvQl s)
abbrev dBytes (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 8)) (cvDl s)

/-- The arrays the loads leave zero. -/
def zeroArrs : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 19, 20, 21, 22, 23]

/-- After the loads. -/
structure StA (s0 s : State) : Prop where
  base : Base s0 s
  ws : Ws s (cvB s0) (cvZ s0) (cvW s0) nArr
  count : s.mem.readW (off (State.addr (cvB s0)) 16) 32 = BitVec.ofNat 32 (cvW s0)
  n : num s.mem (cvB s0) (cvW s0) aDQ = Spec.Rsa.os2ip (nBytes s0)
  p : num s.mem (cvB s0) (cvW s0) aP = Spec.Rsa.os2ip (pBytes s0)
  q : num s.mem (cvB s0) (cvW s0) aQ = Spec.Rsa.os2ip (qBytes s0)
  d : num s.mem (cvB s0) (cvW s0) aD = Spec.Rsa.os2ip (dBytes s0)
  zeros : ∀ j ∈ zeroArrs, val32 s.mem (State.addr (cvB s0)) (arr (cvW s0) j) (cvW s0 + 2) = 0

end VG.Proof.Rsa.Arm.CrtValues
