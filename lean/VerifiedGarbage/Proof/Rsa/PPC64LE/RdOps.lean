module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvLoads
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyOps
public import VerifiedGarbage.Proof.Rsa.PPC64LE.Div
public import VerifiedGarbage.Impl.Rsa.PPC64LE.RecoverDet
public import VerifiedGarbage.Proof.Rsa.RecoverDetModel
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyBits
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyHalf
public import VerifiedGarbage.Proof.Rsa.PPC64LE.DivLoop
public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvTop
public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvCtx
public import VerifiedGarbage.Proof.Rsa.PPC64LE.InvLaw
import VerifiedGarbage.Proof.Rsa.PPC64LE.Shifts
import VerifiedGarbage.Proof.Rsa.PPC64LE.EvenW
import VerifiedGarbage.Proof.Rsa.PPC64LE.WordLoops
import VerifiedGarbage.Proof.Rsa.PPC64LE.Loops
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Mont.RangeCover
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# `vg_rsa_recover_primes_det` on PPC64LE: the arrays of both views

`shlC_ok`: `[j] := 2 [j] + r9`, the bit shifted out in `r9`; `copyOut_ok`:
`copy_ok`, with exactly the digits it writes.

`DS s0 wide A live V ls s`: after the entry and the loads, with the view
`wide` (`w` digits and 44 arrays, or `W = 2 w + 2` digits and 22), each
array `(v, j) ∈ live` of view `v` holds `A v j` and each slot `d ∈ ls`
holds `V d`. A write of array `o` of a view keeps the arrays of `live` apart
from it (`Sep`): those of the same view but `o`, and of the other view those
apart from its bytes (wide array `j` is narrow arrays `2 j` and `2 j + 1`).
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.RecDet

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys VG.Proof.Rsa.PPC64LE.Loops
open VG.Proof.Rsa.PPC64LE.Recover
open VG.Impl.Rsa.PPC64LE.Keys (ptr countLoop copy copyBody copyWBody)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot arr_disj)
open VG.Impl.Rsa.PPC64LE.Recover (nArr)

/-! ## Shifts and copies -/

/-- `shlC j`: `[j] := 2 [j] + r9`, the bit shifted out in `r9`. -/
theorem shlC_ok {s : State} {B : Addr} {Z w N j : Nat} (h : Ws s B Z w N) (hj : j < N) (hN : N ≤ 256)
    (c9 : (s.gpr .r9).toNat ≤ 1) :
    WP isa (VG.Impl.Rsa.PPC64LE.RecoverDet.shlC j) s fun t => Ws t B Z w N ∧
      Outside B (arr w j) (4 * w) s.mem t.mem ∧ (t.gpr .r9).toNat ≤ 1 ∧
      num t.mem B w j + 2 ^ (32 * w) * (t.gpr .r9).toNat = 2 * num s.mem B w j + (s.gpr .r9).toNat ∧
      Keep opRegs s t := by
  have fj := h.arr_fit hj
  have nw := h.nowrap
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wpos
  have := h.wle
  rw [VG.Impl.Rsa.PPC64LE.RecoverDet.shlC, WP.seq_iff, ← List.append_nil (ptr .r5 j)]
  refine ptr_ok h (by decide) (by decide) (by decide) (show j < 2 ^ 15 by omega_arith) (WP.block_nil ?_)
  have k₀ : Keep opRegs s (s.write .r5 (off B (arr w j))) := (Keep.write _ _ _).mono
  have hu : Ws (s.write .r5 (off B (arr w j))) B Z w N := h.of_keep k₀
  have u5 : (s.write .r5 (off B (arr w j))).gpr .r5 = off B (arr w j) := rfl
  have u9 : (s.write .r5 (off B (arr w j))).gpr .r9 = s.gpr .r9 := rfl
  have um : (s.write .r5 (off B (arr w j))).mem = s.mem := rfl
  refine evenW_ok hu (fun hev x mx kx => ?_) (fun hodd x mx kx => ?_)
  · have hx := hu.of_keep kx
    rw [WP.seq_iff]
    refine WP.mono (WP.keep [.r8] (Q := fun y => y.gpr .r5 = off B (arr w j) ∧
      y.gpr .r8 = BitVec.ofNat 64 (w / 2) ∧ y.gpr .r9 = s.gpr .r9 ∧ y.mem = s.mem)
      (by prun [kx.gpr (r := .r5) (by decide), kx.gpr (r := .r9) (by decide), u5, u9, hx.r29, mx, um,
        lsr1_ofNat (show w < 2 ^ 64 by omega_arith)]) (by decide)) fun y ⟨⟨y5, y8, y9, ym⟩, ky⟩ => ?_
    have hy := hx.of_keep ky
    refine WP.mono (shlWLoop_ok hy.scr y5 y8 (by rw [y9]; exact c9) (by omega_arith) (by omega_arith)
      (by omega_arith)) fun t ⟨c9', vq, tout, kt, _⟩ => ⟨hy.of_keep kt, ?_, c9', ?_,
        Keep.mono (rs' := opRegs) (((k₀.trans kx).trans ky).trans kt) (by decide)⟩
    · rw [ym] at tout; simpa only [show 8 * (w / 2) = 4 * w by omega_arith] using tout
    · rw [ym, y9, show 64 * (w / 2) = 32 * w by omega_arith] at vq
      rw [num_words _ _ hev, num_words _ _ hev]; exact vq
  · have hx := hu.of_keep kx
    rw [WP.seq_iff]
    refine WP.mono (WP.keep [.r8] (Q := fun y => y.gpr .r5 = off B (arr w j) ∧
      y.gpr .r8 = BitVec.ofNat 64 w ∧ y.gpr .r9 = s.gpr .r9 ∧ y.mem = s.mem)
      (by prun [kx.gpr (r := .r5) (by decide), kx.gpr (r := .r9) (by decide), u5, u9, hx.r29, mx, um,
        BitVec.add_zero]) (by decide)) fun y ⟨⟨y5, y8, y9, ym⟩, ky⟩ => ?_
    have hy := hx.of_keep ky
    refine WP.mono (shlLoop_ok hy.scr y5 y8 (by rw [y9]; exact c9) (by omega_arith) (by omega_arith)
      (by omega_arith)) fun t ⟨c9', vq, tout, kt⟩ => ⟨hy.of_keep kt, by rw [ym] at tout; exact tout, c9', ?_,
        Keep.mono (rs' := opRegs) (((k₀.trans kx).trans ky).trans kt) (by decide)⟩
    rw [ym, y9] at vq; exact vq

/-- `copy o a`, with exactly the digits it writes. -/
theorem copyOut_ok {s : State} {B : Addr} {Z w N o a : Nat} (h : Ws s B Z w N)
    (ho : o < N) (ha : a < N) (hN : N ≤ 256) (hoa : o ≠ a) :
    WP isa (copy o a) s fun t => Ws t B Z w N ∧ Outside B (arr w o) (4 * w) s.mem t.mem ∧
      num t.mem B w o = num s.mem B w a ∧ Keep opRegs s t := by
  have fo := h.arr_fit ho
  have fa := h.arr_fit ha
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wle
  have := h.wpos
  have nw := h.nowrap
  rw [copy, WP.seq_iff, ← List.append_nil (ptr .r5 o ++ ptr .r6 a), List.append_assoc]
  refine ptr_ok h (by decide) (by decide) (by decide) (show o < 2 ^ 15 by omega_arith) ?_
  refine ptr_ok (h.of_keep (Keep.write _ _ _)) (by decide) (by decide) (by decide)
    (show a < 2 ^ 15 by omega_arith) (WP.block_nil ?_)
  let t : State := (s.write .r5 (off B (arr w o))).write .r6 (off B (arr w a))
  have kt : Keep [.r5, .r6] s t := (Keep.write _ _ _).trans (Keep.write _ _ _)
  have ht : Ws t B Z w N := h.of_keep kt
  have t5 : t.gpr .r5 = off B (arr w o) := rfl
  have t6 : t.gpr .r6 = off B (arr w a) := rfl
  refine evenW_ok ht (fun hev u mu ku => ?_) (fun hodd u mu ku => ?_)
  · have hu := ht.of_keep ku
    rw [WP.seq_iff]
    refine WP.mono (WP.keep [.r8] (Q := fun x => x.gpr .r5 = off B (arr w o) ∧ x.gpr .r6 = off B (arr w a) ∧
      x.gpr .r8 = BitVec.ofNat 64 (w / 2) ∧ x.mem = u.mem)
      (by prun [ku.gpr (r := .r5) (by decide), ku.gpr (r := .r6) (by decide), t5, t6, hu.r29,
        lsr1_ofNat (show w < 2 ^ 64 by omega_arith)]) (by decide)) fun x ⟨⟨x5, x6, x8, xm⟩, kx⟩ => ?_
    have hx := hu.of_keep kx
    refine WP.mono (copyWLoop_ok hx.scr x5 x6 x8 (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
      (aheadW hev (ahead_of_ne hoa))) fun t' ⟨v, out, kt'⟩ => ?_
    have mt : t.mem = s.mem := rfl
    rw [xm, mu, mt] at v out
    exact ⟨hx.of_keep kt', by simpa only [show 8 * (w / 2) = 4 * w by omega_arith] using out,
      by rw [num_words _ _ hev, num_words _ _ hev, v],
      Keep.mono (rs' := opRegs) (((kt.trans ku).trans kx).trans kt') (by decide)⟩
  · have hu := ht.of_keep ku
    rw [WP.seq_iff]
    refine WP.mono (WP.keep [.r8] (Q := fun x => x.gpr .r5 = off B (arr w o) ∧ x.gpr .r6 = off B (arr w a) ∧
      x.gpr .r8 = BitVec.ofNat 64 w ∧ x.mem = u.mem)
      (by prun [ku.gpr (r := .r5) (by decide), ku.gpr (r := .r6) (by decide), t5, t6, hu.r29, BitVec.add_zero])
      (by decide)) fun x ⟨⟨x5, x6, x8, xm⟩, kx⟩ => ?_
    have hx := hu.of_keep kx
    refine WP.mono (copyLoop_ok hx.scr x5 x6 x8 h.wpos (by omega_arith) (by omega_arith) (by omega_arith)
      (ahead_of_ne hoa)) fun t' ⟨v, out, kt'⟩ => ?_
    have mt : t.mem = s.mem := rfl
    rw [xm, mu, mt] at v out
    exact ⟨hx.of_keep kt', out, v, Keep.mono (rs' := opRegs) (((kt.trans ku).trans kx).trans kt') (by decide)⟩

/-! ## The two views -/

theorem arr_wide (w k : Nat) : arr (2 * w + 2) k = arr w (2 * k) := by
  simp only [arr, S]; rw [Nat.mul_comm 2 k, Nat.mul_assoc]; congr 2; omega

theorem S_wide (w : Nat) : S (2 * w + 2) = 2 * S w := by simp only [S]; omega

/-- A wide array is its two narrow arrays. -/
theorem num_wide (m : Mem) (B : Addr) (w k : Nat) :
    num m B (2 * w + 2) k = num m B w (2 * k) + 2 ^ (32 * w) * val32 m B (arr w (2 * k) + 4 * w) (w + 2) := by
  simp only [num]
  rw [arr_wide, show 2 * w + 2 = w + (w + 2) by omega, val32_append]

/-- The low half of a wide number. -/
theorem num_low (m : Mem) (B : Addr) (w k : Nat) :
    num m B w (2 * k) = num m B (2 * w + 2) k % 2 ^ (32 * w) := by
  rw [num_wide, Nat.mul_comm (2 ^ (32 * w)), Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (val32_lt _ _ _ _)]

/-- A wide frame is a narrow one on its two arrays. -/
theorem keep_W_w {B : Addr} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (h : KeyWorkspace.Keep B (2 * w + 2) js ds m m') :
    KeyWorkspace.Keep B w (js.flatMap fun o => [2 * o, 2 * o + 1]) ds m m' := by
  intro x hx
  apply h x
  intro r hr
  simp only [KeyWorkspace.ranges, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨j, hj, rfl⟩ | ⟨d, hd, rfl⟩
  · have h1 := hx (arr w (2 * j), S w) (by
      simp only [KeyWorkspace.ranges, List.mem_append, List.mem_map, List.mem_flatMap]
      exact .inl ⟨2 * j, ⟨j, hj, by simp⟩, rfl⟩)
    have h2 := hx (arr w (2 * j + 1), S w) (by
      simp only [KeyWorkspace.ranges, List.mem_append, List.mem_map, List.mem_flatMap]
      exact .inl ⟨2 * j + 1, ⟨j, hj, by simp⟩, rfl⟩)
    have e := KeyWorkspace.arr_succ w (2 * j)
    dsimp only at h1 h2 ⊢
    rw [arr_wide, S_wide]; omega
  · exact hx (d, 4) (by simp [KeyWorkspace.ranges, hd])

/-- A narrow frame is a wide one on the wide arrays holding it. -/
theorem keep_w_W {B : Addr} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (h : KeyWorkspace.Keep B w js ds m m') : KeyWorkspace.Keep B (2 * w + 2) (js.map (· / 2)) ds m m' := by
  refine Outs.cover h fun r hr => ?_
  simp only [KeyWorkspace.ranges, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨j, hj, rfl⟩ | ⟨d, hd, rfl⟩
  · refine ⟨(arr (2 * w + 2) (j / 2), S (2 * w + 2)), by
      simp only [KeyWorkspace.ranges, List.mem_append, List.mem_map]; exact .inl ⟨j / 2, ⟨j, hj, rfl⟩, rfl⟩, ?_, ?_⟩
    · dsimp only; rw [arr_wide]; exact KeyWorkspace.arr_mono (by omega)
    · dsimp only; rw [arr_wide, S_wide]
      rcases Nat.mod_two_eq_zero_or_one j with e | e
      · rw [show 2 * (j / 2) = j by omega]; omega
      · have := KeyWorkspace.arr_succ w (2 * (j / 2))
        rw [show 2 * (j / 2) + 1 = j by omega] at this; omega
  · exact ⟨(d, 4), by simp [KeyWorkspace.ranges, hd], Nat.le_refl _, Nat.le_refl _⟩

/-- A frame of slots alone is one of every view. -/
theorem keep_view {B : Addr} {w w' : Nat} {ds : List Nat} {m m' : Mem}
    (h : KeyWorkspace.Keep B w [] ds m m') : KeyWorkspace.Keep B w' [] ds m m' := by
  unfold KeyWorkspace.Keep KeyWorkspace.ranges at h ⊢
  simpa using h

/-! ## The state -/

/-- The digits of a view: `w` (narrow) or `W = 2 w + 2` (wide). -/
abbrev vw (s0 : State) (b : Bool) : Nat := cond b (wW (kK s0)) (ww (kK s0))

/-- The arrays of a view. -/
abbrev vN (b : Bool) : Nat := cond b 22 nArr

/-- Arrays apart: of the same view, distinct; a wide array `j` and a narrow
`i` with `i / 2 ≠ j`. -/
def Sep (e e' : Bool × Nat) : Prop :=
  if e.1 = e'.1 then e.2 ≠ e'.2 else if e.1 = true then e'.2 / 2 ≠ e.2 else e.2 / 2 ≠ e'.2

instance (e e' : Bool × Nat) : Decidable (Sep e e') := by unfold Sep; infer_instance

theorem sep_ne {e e' : Bool × Nat} (h : Sep e e') : e' ≠ e := by
  rintro rfl; unfold Sep at h; simp at h

/-- Array `o` of view `b` := `x`. -/
def upd (A : Bool → Nat → Nat) (b : Bool) (o x : Nat) : Bool → Nat → Nat :=
  fun b' j => if b' = b ∧ j = o then x else A b' j

/-- Slot `d` := `x`. -/
def updV (V : Nat → Nat) (d x : Nat) : Nat → Nat := fun e => if e = d then x else V e

@[simp] theorem upd_self (A : Bool → Nat → Nat) (b : Bool) (o x : Nat) : upd A b o x b o = x := by simp [upd]

theorem upd_ne (A : Bool → Nat → Nat) {b b' : Bool} {o j : Nat} (x : Nat) (h : ¬(b' = b ∧ j = o)) :
    upd A b o x b' j = A b' j := by simp only [upd, h, ↓reduceIte]

/-- After the loads, in view `b`: the arrays `live` hold `A`, the slots `ls` hold `V`. -/
structure DS (s0 : State) (b : Bool) (A : Bool → Nat → Nat) (live : List (Bool × Nat)) (V : Nat → Nat)
    (ls : List Nat) (s : State) : Prop where
  base : RBase s0 s
  ws : Ws s (rvB s0) (rvZ s0) (vw s0 b) (vN b)
  r21 : s.gpr .r21 = s0.gpr .r3
  r23 : s.gpr .r23 = s0.gpr .r5
  r25 : s.gpr .r25 = s0.gpr .r8
  arrs : ∀ e ∈ live, num s.mem (rvB s0) (vw s0 e.1) e.2 = A e.1 e.2
  live_lt : ∀ e ∈ live, e.2 < vN e.1
  sl : ∀ d ∈ ls, slot s.mem (rvB s0) d = V d
  ls_ok : ∀ d ∈ ls, d + 4 ≤ 160

section
variable {s0 s t : State} {b : Bool} {A : Bool → Nat → Nat} {live : List (Bool × Nat)} {V : Nat → Nat}
  {ls : List Nat}

theorem vw_wide (s0 : State) : vw s0 true = 2 * vw s0 false + 2 := rfl

theorem vw_false (s0 : State) : vw s0 false = ww (kK s0) := rfl

theorem vw_true (s0 : State) : vw s0 true = wW (kK s0) := rfl

/-- Every array of a view ends within the bytes the entry may change. -/
theorem fit_sv (s0 : State) (b : Bool) {j : Nat} (hj : j < vN b) : arr (vw s0 b) j + S (vw s0 b) ≤ sv (kK s0) := by
  cases b
  · exact KeyWorkspace.arr_end hj
  · have e : arr (vw s0 true) 22 = sv (kK s0) := by
      rw [vw_wide, arr_wide]; rfl
    rw [← e]; exact KeyWorkspace.arr_end hj

theorem DS.fit (h : DS s0 b A live V ls s) (b' : Bool) {j : Nat} (hj : j < vN b') :
    arr (vw s0 b') j + S (vw s0 b') ≤ 2 ^ 64 := by
  have := fit_sv s0 b' hj; have := h.base.svZ; have := h.base.nowrap; omega

/-- A write of view `b`'s arrays `js` keeps every array apart from them. -/
theorem keep_sep {B : Addr} {m m' : Mem} {js : List Nat} (s0 : State)
    (k : KeyWorkspace.Keep B (vw s0 b) js [] m m') {e : Bool × Nat} (he : ∀ j ∈ js, Sep (b, j) e)
    (fit : arr (vw s0 e.1) e.2 + S (vw s0 e.1) ≤ 2 ^ 64) :
    num m' B (vw s0 e.1) e.2 = num m B (vw s0 e.1) e.2 := by
  obtain ⟨b', j⟩ := e
  unfold Sep at he
  dsimp only at he fit ⊢
  by_cases hb : b = b'
  · subst hb
    simp only [↓reduceIte] at he
    exact k.num (fun k hk => he k hk) (by simp) fit
  · simp only [hb, ↓reduceIte] at he
    cases b <;> cases b' <;> simp only [Bool.false_eq_true, ↓reduceIte, not_true_eq_false] at hb he
    · have k' := keep_w_W k
      refine k'.num (fun k hk => ?_) (by simp) fit
      simp only [List.mem_map] at hk
      obtain ⟨i, hi, rfl⟩ := hk
      exact he i hi
    · have k' := keep_W_w k
      refine k'.num (fun k hk => ?_) (by simp) fit
      simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hk
      obtain ⟨i, hi, rfl | rfl⟩ := hk
      · have := he i hi; omega
      · have := he i hi; omega

/-- A write of several arrays of view `b`, keeping the arrays apart from them. -/
theorem DS.wrs (h : DS s0 b A live V ls s) (ws : Ws t (rvB s0) (rvZ s0) (vw s0 b) (vN b))
    {js : List Nat} (hjs : ∀ j ∈ js, j < vN b) (k : KeyWorkspace.Keep (rvB s0) (vw s0 b) js [] s.mem t.mem)
    {live' : List (Bool × Nat)} (hl : ∀ e ∈ live', e ∈ live ∧ ∀ j ∈ js, Sep (b, j) e)
    {rs : List Reg} (kr : Keep rs s t) (h21 : .r21 ∉ rs := by decide) (h23 : .r23 ∉ rs := by decide)
    (h25 : .r25 ∉ rs := by decide) (h31 : .r31 ∉ rs := by decide) : DS s0 b A live' V ls t := by
  have base := h.base.of_keep k (fun j hj => fit_sv s0 b (hjs j hj)) (by simp) kr h31
  refine ⟨base, ws, (kr.gpr _ h21).trans h.r21, (kr.gpr _ h23).trans h.r23, (kr.gpr _ h25).trans h.r25,
    fun e he => ?_, fun e he => h.live_lt e (hl e he).1, fun d hd => ?_, h.ls_ok⟩
  · obtain ⟨he', hsep⟩ := hl e he
    rw [← h.arrs e he']
    exact keep_sep s0 k hsep (h.fit e.1 (h.live_lt e he'))
  · rw [← h.sl d hd]
    exact k.slot (by have := h.ls_ok d hd; simp only [KeyWorkspace.hdr]; omega) (by simp)

/-- A new array of `live` (of either view). -/
theorem DS.add (h : DS s0 b A live V ls s) {b' : Bool} {o x : Nat} (ho : o < vN b')
    (v : num s.mem (rvB s0) (vw s0 b') o = x) (hl : ∀ e ∈ live, e ≠ (b', o)) :
    DS s0 b (upd A b' o x) ((b', o) :: live) V ls s := by
  refine ⟨h.base, h.ws, h.r21, h.r23, h.r25, fun e he => ?_, fun e he => ?_, h.sl, h.ls_ok⟩
  · simp only [List.mem_cons] at he
    rcases he with rfl | he
    · rw [upd_self]; exact v
    · have hs := hl e he
      rw [upd_ne _ _ (fun ⟨e1, e2⟩ => by
        obtain ⟨b'', j⟩ := e; dsimp only at e1 e2; subst e1 e2; exact hs rfl)]
      exact h.arrs e he
  · simp only [List.mem_cons] at he
    rcases he with rfl | he
    · exact ho
    · exact h.live_lt e he

/-- A write of view `b`'s array `o`, keeping the arrays apart from it. -/
theorem DS.wr (h : DS s0 b A live V ls s) (ws : Ws t (rvB s0) (rvZ s0) (vw s0 b) (vN b))
    {o x : Nat} (ho : o < vN b) (k : KeyWorkspace.Keep (rvB s0) (vw s0 b) [o] [] s.mem t.mem)
    (v : num t.mem (rvB s0) (vw s0 b) o = x)
    {live' : List (Bool × Nat)} (hl : ∀ e ∈ live', e ∈ live ∧ Sep (b, o) e)
    {rs : List Reg} (kr : Keep rs s t) (h21 : .r21 ∉ rs := by decide) (h23 : .r23 ∉ rs := by decide)
    (h25 : .r25 ∉ rs := by decide) (h31 : .r31 ∉ rs := by decide) :
    DS s0 b (upd A b o x) ((b, o) :: live') V ls t :=
  (h.wrs ws (by simpa using ho) k (fun e he => ⟨(hl e he).1, by simpa using (hl e he).2⟩) kr h21 h23 h25 h31).add
    ho v (fun e he => sep_ne (hl e he).2)

/-- A write of a slot. -/
theorem DS.wrS (h : DS s0 b A live V ls s) (ws : Ws t (rvB s0) (rvZ s0) (vw s0 b) (vN b))
    {d x : Nat} (hd : d + 4 ≤ 160) (k : KeyWorkspace.Keep (rvB s0) (vw s0 b) [] [d] s.mem t.mem)
    (v : slot t.mem (rvB s0) d = x) {ls' : List Nat} (hl : ∀ e ∈ ls', e ∈ ls ∧ (e + 4 ≤ d ∨ d + 4 ≤ e))
    {rs : List Reg} (kr : Keep rs s t) (h21 : .r21 ∉ rs := by decide) (h23 : .r23 ∉ rs := by decide)
    (h25 : .r25 ∉ rs := by decide) (h31 : .r31 ∉ rs := by decide) :
    DS s0 b A live (updV V d x) (d :: ls') t := by
  have hd' : ∀ e ∈ [d], e + 4 ≤ KeyWorkspace.hdr := fun e he => by
    simp only [List.mem_singleton] at he; subst he; simp only [KeyWorkspace.hdr]; omega
  have base := h.base.of_keep k (by simp) hd' kr h31
  refine ⟨base, ws, (kr.gpr _ h21).trans h.r21, (kr.gpr _ h23).trans h.r23, (kr.gpr _ h25).trans h.r25,
    fun e he => ?_, h.live_lt, fun e he => ?_, fun e he => ?_⟩
  · rw [← h.arrs e he]
    exact (keep_view (w' := vw s0 e.1) k).num (by simp) hd' (h.fit e.1 (h.live_lt e he))
  · simp only [List.mem_cons] at he
    rcases he with rfl | he
    · simp only [updV, ↓reduceIte]; exact v
    · obtain ⟨he', hs⟩ := hl e he
      have : e ≠ d := by omega
      simp only [updV, this, ↓reduceIte]
      rw [← h.sl e he']
      exact k.slot (by have := h.ls_ok e he'; simp only [KeyWorkspace.hdr]; omega)
        (fun e' he' => by simp only [List.mem_singleton] at he'; subst he'; omega)
  · simp only [List.mem_cons] at he
    rcases he with rfl | he
    · exact hd
    · exact h.ls_ok e (hl e he).1

/-- A step on registers only. -/
theorem DS.regs (h : DS s0 b A live V ls s) {rs : List Reg} (kr : Keep rs s t) (m : t.mem = s.mem)
    (h21 : .r21 ∉ rs := by decide) (h23 : .r23 ∉ rs := by decide) (h25 : .r25 ∉ rs := by decide)
    (h29 : .r29 ∉ rs := by decide) (h30 : .r30 ∉ rs := by decide) (h31 : .r31 ∉ rs := by decide) :
    DS s0 b A live V ls t :=
  ⟨h.base.of_regs kr m h31, h.ws.of_keep kr h29 h30 h31, (kr.gpr _ h21).trans h.r21,
    (kr.gpr _ h23).trans h.r23, (kr.gpr _ h25).trans h.r25, fun e he => by rw [m]; exact h.arrs e he,
    h.live_lt, fun d hd => by rw [m]; exact h.sl d hd, h.ls_ok⟩

/-- Fewer arrays and slots. -/
theorem DS.drop (h : DS s0 b A live V ls s) {live' : List (Bool × Nat)} {ls' : List Nat}
    (hl : ∀ e ∈ live', e ∈ live := by decide) (hs : ∀ d ∈ ls', d ∈ ls := by decide) : DS s0 b A live' V ls' s :=
  ⟨h.base, h.ws, h.r21, h.r23, h.r25, fun e he => h.arrs e (hl e he), fun e he => h.live_lt e (hl e he),
    fun d hd => h.sl d (hs d hd), fun d hd => h.ls_ok d (hs d hd)⟩

theorem DS.val (h : DS s0 b A live V ls s) {b' : Bool} {j : Nat} (he : (b', j) ∈ live) :
    num s.mem (rvB s0) (vw s0 b') j = A b' j :=
  h.arrs _ he

/-- A narrow array as its wide array's low half. -/
theorem DS.low (h : DS s0 b A live V ls s) {k : Nat} (hk : (true, k) ∈ live) :
    num s.mem (rvB s0) (ww (kK s0)) (2 * k) = A true k % 2 ^ (32 * ww (kK s0)) := by
  rw [num_low, ← h.val hk]; rfl

theorem DS.lt (h : DS s0 b A live V ls s) {b' : Bool} {j : Nat} (he : (b', j) ∈ live) :
    A b' j < 2 ^ (32 * vw s0 b') := by
  rw [← h.val he]; exact val32_lt _ _ _ _

theorem four_le_S (w : Nat) : 0 + 4 * w ≤ S w := by simp only [S]; omega

theorem DS.ix (h : DS s0 b A live V ls s) {b' : Bool} {j : Nat} (he : (b', j) ∈ live) : j < vN b' :=
  h.live_lt _ he

theorem vN_le (b : Bool) : vN b ≤ 256 := by cases b <;> decide

theorem ahead_any (w o a : Nat) : Ahead (arr w o) (arr w a) w := by
  by_cases e : o = a
  · subst e; exact .inl (Nat.le_refl _)
  · exact ahead_of_ne e

/-- A subtraction's difference and borrow. -/
theorem sub_arith {x a c P r : Nat} (hx : x < P) (ha : a < P) (hc : c < P) (hr : r ≤ 1)
    (e : x + c = a + P * r) : x = (a + P - c) % P ∧ r = if a < c then 1 else 0 := by
  rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
  · have : c ≤ a := by omega
    refine ⟨?_, by simp; omega⟩
    rw [show a + P - c = (a - c) + P by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega
  · have : a < c := by omega
    refine ⟨?_, by simp [this]⟩
    rw [Nat.mod_eq_of_lt (by omega)]; omega

/-- `copy o a`. -/
theorem DS.copy (h : DS s0 b A live V ls s) {o a : Nat} (ho : o < vN b) (ha : (b, a) ∈ live) (hoa : o ≠ a)
    {live' : List (Bool × Nat)} (hl : ∀ e ∈ live', e ∈ live ∧ Sep (b, o) e) :
    WP isa (copy o a) s fun t => DS s0 b (upd A b o (A b a)) ((b, o) :: live') V ls t ∧ Keep opRegs s t ∧
      Outside (rvB s0) (arr (vw s0 b) o) (4 * vw s0 b) s.mem t.mem :=
  WP.mono (copyOut_ok h.ws ho (h.ix ha) (vN_le b) hoa) fun t ⟨ws, out, v, kr⟩ =>
    ⟨h.wr ws ho (KeyWorkspace.Keep.of_arr (d := 0) (by simpa using out) (four_le_S _) (by simp))
      (by rw [v]; exact h.val ha) hl kr, kr, out⟩

/-- A narrow copy into the low half of a zero wide array: the wide array holds it. -/
theorem DS.widen (h : DS s0 false A live V ls s) {k a : Nat} (hk : k < 22) (hz : (true, k) ∈ live)
    (z : A true k = 0) (ha : (false, a) ∈ live) (hak : a ≠ 2 * k)
    {live' : List (Bool × Nat)} (hl : ∀ e ∈ live', e ∈ live ∧ Sep (false, 2 * k) e ∧ e ≠ (true, k)) :
    WP isa (VG.Impl.Rsa.PPC64LE.Keys.copy (2 * k) a) s fun t =>
      DS s0 false (upd (upd A false (2 * k) (A false a)) true k (A false a)) ((true, k) :: (false, 2 * k) :: live')
        V ls t ∧ Keep opRegs s t := by
  refine WP.mono (h.copy (o := 2 * k) (show 2 * k < 44 by omega) ha (Ne.symm hak)
    (live' := live') (fun e he => ⟨(hl e he).1, (hl e he).2.1⟩)) fun t ⟨ht, kr, out⟩ => ⟨?_, kr⟩
  refine ht.add (o := k) hk ?_ (fun e he => ?_)
  · -- The high part was zero, and the copy left it.
    have z0 : val32 s.mem (rvB s0) (arr (ww (kK s0)) (2 * k) + 4 * ww (kK s0)) (ww (kK s0) + 2) = 0 := by
      have e := num_wide s.mem (rvB s0) (ww (kK s0)) k
      have v := h.val hz
      rw [z] at v
      change num s.mem (rvB s0) (2 * ww (kK s0) + 2) k = 0 at v
      rw [v] at e
      have := Nat.two_pow_pos (32 * ww (kK s0))
      rcases Nat.eq_zero_or_pos (val32 s.mem (rvB s0) (arr (ww (kK s0)) (2 * k) + 4 * ww (kK s0)) (ww (kK s0) + 2)) with
        e' | e'
      · exact e'
      · have := Nat.mul_pos this e'; omega
    have f := h.fit true (j := k) hk
    rw [vw_wide, vw_false, arr_wide, S_wide] at f
    rw [vw_false] at out
    have hi : val32 t.mem (rvB s0) (arr (ww (kK s0)) (2 * k) + 4 * ww (kK s0)) (ww (kK s0) + 2) = 0 := by
      rw [out.val32 (by omega) (by simp only [S] at f; omega)]; exact z0
    have v := ht.arrs (false, 2 * k) (by simp)
    rw [vw_false] at v
    change num t.mem (rvB s0) (2 * ww (kK s0) + 2) k = _
    rw [num_wide, hi, Nat.mul_zero, Nat.add_zero, v, upd_self]
  · simp only [List.mem_cons] at he
    rcases he with rfl | he
    · simp
    · exact (hl e he).2.2

/-- `sub3 o a c`: `[o] := [a] - [c]` modulo `2^(32 v)`, the borrow in `r9`. -/
theorem DS.sub3 (h : DS s0 b A live V ls s) {o a c : Nat} (ho : o < vN b) (ha : (b, a) ∈ live)
    (hc : (b, c) ∈ live) {live' : List (Bool × Nat)} (hl : ∀ e ∈ live', e ∈ live ∧ Sep (b, o) e) :
    WP isa (VG.Impl.Rsa.PPC64LE.Keys.sub3 o a c) s fun t =>
      DS s0 b (upd A b o (VG.Proof.Rsa.RecoverDet.wsub (32 * vw s0 b) (A b a) (A b c))) ((b, o) :: live') V ls t ∧
      (t.gpr .r9).toNat = (if A b a < A b c then 1 else 0) ∧ Keep opRegs s t := by
  refine WP.mono (sub3_gen_ok h.ws ho (h.ix ha) (h.ix hc) (vN_le b) (ahead_any _ _ _) (ahead_any _ _ _))
    fun t ⟨ws, k, e, r9, kr⟩ => ?_
  rw [h.val ha, h.val hc] at e
  obtain ⟨xv, bv⟩ := sub_arith (val32_lt _ _ _ _) (h.lt ha) (h.lt hc) r9 e
  exact ⟨h.wr ws ho k xv hl kr, bv, kr⟩

/-- `sel o a c sl`: `[o] := [c]` if the slot `sl` holds 1, `[a]` if 0. -/
theorem DS.sel (h : DS s0 b A live V ls s) {o a c sl : Nat} (ho : o < vN b) (ha : (b, a) ∈ live)
    (hc : (b, c) ∈ live) (hsl : sl ∈ ls) (bit : V sl ≤ 1)
    {live' : List (Bool × Nat)} (hl : ∀ e ∈ live', e ∈ live ∧ Sep (b, o) e) :
    WP isa (VG.Impl.Rsa.PPC64LE.Keys.sel o a c sl) s fun t =>
      DS s0 b (upd A b o (if V sl = 0 then A b a else A b c)) ((b, o) :: live') V ls t ∧ Keep opRegs s t := by
  have hs := h.sl sl hsl
  refine WP.mono (sel_gen_ok h.ws ho (h.ix ha) (h.ix hc) (vN_le b) (ahead_any _ _ _) (ahead_any _ _ _)
    (by have := h.ls_ok sl hsl; simp only [KeyWorkspace.hdr]; omega) (by rw [hs]; exact bit))
    fun t ⟨ws, k, e, kr⟩ => ⟨h.wr ws ho k (by rw [e, hs, h.val ha, h.val hc]) hl kr, kr⟩

/-- `half j` with `r9 = 0`: `[j] := [j] / 2`. -/
theorem DS.half (h : DS s0 b A live V ls s) {j : Nat} (hj : (b, j) ∈ live) (z9 : s.gpr .r9 = 0)
    {live' : List (Bool × Nat)} (hl : ∀ e ∈ live', e ∈ live ∧ Sep (b, j) e) :
    WP isa (VG.Impl.Rsa.PPC64LE.Keys.half j) s fun t =>
      DS s0 b (upd A b j (A b j / 2)) ((b, j) :: live') V ls t ∧ Keep opRegs s t := by
  refine WP.mono (half_ok h.ws (h.ix hj) (vN_le b) (by rw [z9]; decide)) fun t ⟨ws, k, e, kr⟩ =>
    ⟨h.wr ws (h.ix hj) k (by rw [e, z9, h.val hj]; simp) hl kr, kr⟩

/-- `shlC j`: `[j] := 2 [j] + c` modulo `2^(32 v)`, for `r9 = c ≤ 1`, the bit out in `r9`. -/
theorem DS.shlC (h : DS s0 b A live V ls s) {j c : Nat} (hj : (b, j) ∈ live) (c9 : (s.gpr .r9).toNat = c)
    (hc : c ≤ 1) {live' : List (Bool × Nat)} (hl : ∀ e ∈ live', e ∈ live ∧ Sep (b, j) e) :
    WP isa (VG.Impl.Rsa.PPC64LE.RecoverDet.shlC j) s fun t =>
      DS s0 b (upd A b j ((2 * A b j + c) % 2 ^ (32 * vw s0 b))) ((b, j) :: live') V ls t ∧
      (t.gpr .r9).toNat = (2 * A b j + c) / 2 ^ (32 * vw s0 b) ∧ Keep opRegs s t := by
  refine WP.mono (shlC_ok h.ws (h.ix hj) (vN_le b) (by rw [c9]; exact hc)) fun t ⟨ws, out, r9, e, kr⟩ => ?_
  rw [h.val hj, c9] at e
  have lt := val32_lt t.mem (rvB s0) (arr (vw s0 b) j) (vw s0 b)
  have P := Nat.two_pow_pos (32 * vw s0 b)
  have xv : num t.mem (rvB s0) (vw s0 b) j = (2 * A b j + c) % 2 ^ (32 * vw s0 b) := by
    rw [← e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt lt]
  refine ⟨h.wr ws (h.ix hj) (KeyWorkspace.Keep.of_arr (d := 0) (by simpa using out)
    (four_le_S _) (by simp)) xv hl kr, ?_, kr⟩
  rw [← e, Nat.add_mul_div_left _ _ P, Nat.div_eq_of_lt lt, Nat.zero_add]

/-- `shl j`: `[j] := 2 [j]` modulo `2^(32 v)`, the bit out in `r9`. -/
theorem DS.shl (h : DS s0 b A live V ls s) {j : Nat} (hj : (b, j) ∈ live)
    {live' : List (Bool × Nat)} (hl : ∀ e ∈ live', e ∈ live ∧ Sep (b, j) e) :
    WP isa (VG.Impl.Rsa.PPC64LE.RecoverDet.shl j) s fun t =>
      DS s0 b (upd A b j (2 * A b j % 2 ^ (32 * vw s0 b))) ((b, j) :: live') V ls t ∧
      (t.gpr .r9).toNat = 2 * A b j / 2 ^ (32 * vw s0 b) ∧ Keep opRegs s t := by
  rw [VG.Impl.Rsa.PPC64LE.RecoverDet.shl, WP.seq_iff]
  refine WP.mono (WP.keep [.r9] (Q := fun u => u.gpr .r9 = 0 ∧ u.mem = s.mem) (by prun; rfl) (by decide))
    fun u ⟨⟨u9, um⟩, ku⟩ => ?_
  refine WP.mono ((h.regs ku um).shlC hj (c := 0) (by rw [u9]; rfl) (by omega) hl) fun t ⟨ht, r9, kt⟩ =>
    ⟨by simpa using ht, by simpa using r9, (ku.trans kt).mono⟩

/-- `bitOf sl j`: the slot `sl` := the low bit of `[j]`. -/
theorem DS.bitOf (h : DS s0 b A live V ls s) {j sl : Nat} (hj : (b, j) ∈ live) (hsl : sl + 4 ≤ 160)
    {ls' : List Nat} (hl : ∀ e ∈ ls', e ∈ ls ∧ (e + 4 ≤ sl ∨ sl + 4 ≤ e)) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, DS s0 b A live (updV V sl (A b j % 2)) (sl :: ls') t → Keep opRegs s t → WP isa (.block rest) t Q) :
    WP isa (.block (VG.Impl.Rsa.PPC64LE.Keys.bitOf sl j ++ rest)) s Q :=
  bitOf_ok h.ws (h.ix hj) (vN_le b) (by omega) fun t ws kk v kr =>
    k t (h.wrS ws hsl kk (by rw [v, h.val hj]) hl kr) kr

/-- `setOne j`: the low digit of `[j]` := 1. -/
theorem DS.setOne (h : DS s0 b A live V ls s) {j : Nat} (hj : (b, j) ∈ live)
    {live' : List (Bool × Nat)} (hl : ∀ e ∈ live', e ∈ live ∧ Sep (b, j) e) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, DS s0 b (upd A b j (1 + 2 ^ 32 * (A b j / 2 ^ 32))) ((b, j) :: live') V ls t → Keep opRegs s t →
      WP isa (.block rest) t Q) :
    WP isa (.block (VG.Impl.Rsa.PPC64LE.Keys.setOne j ++ rest)) s Q :=
  setOne_ok h.ws (h.ix hj) (vN_le b) fun t ws kk v kr =>
    k t (h.wr ws (h.ix hj) kk (by rw [v, h.val hj]) hl kr) kr

/-- `stBorrow sl`: the slot `sl` := `r9`. -/
theorem DS.stBorrow (h : DS s0 b A live V ls s) {sl c : Nat} (hsl : sl + 4 ≤ 160) (c9 : (s.gpr .r9).toNat = c)
    (hc : c ≤ 1) {ls' : List Nat} (hl : ∀ e ∈ ls', e ∈ ls ∧ (e + 4 ≤ sl ∨ sl + 4 ≤ e)) {rest : List Instr}
    {Q : State → Prop}
    (k : ∀ t, DS s0 b A live (updV V sl c) (sl :: ls') t → Keep opRegs s t → WP isa (.block rest) t Q) :
    WP isa (.block (VG.Impl.Rsa.PPC64LE.Keys.stBorrow sl ++ rest)) s Q :=
  stBorrow_ok h.ws (by omega) (by omega) fun t ws kk v kr => k t (h.wrS ws hsl kk (by rw [v, c9]) hl kr) kr

/-- `eqS d a c`: the slot `d` := whether `[a] = [c]`. -/
theorem DS.eqS (h : DS s0 b A live V ls s) {d a c : Nat} (ha : (b, a) ∈ live) (hc : (b, c) ∈ live)
    (hd : d + 4 ≤ 160) {ls' : List Nat} (hl : ∀ e ∈ ls', e ∈ ls ∧ (e + 4 ≤ d ∨ d + 4 ≤ e)) :
    WP isa (VG.Impl.Rsa.PPC64LE.Keys.eqS d a c) s fun t =>
      DS s0 b A live (updV V d (if A b a = A b c then 1 else 0)) (d :: ls') t ∧ Keep opRegs s t :=
  WP.mono (eqS_ok h.ws (h.ix ha) (h.ix hc) (vN_le b) (by omega)) fun t ⟨ws, kk, v, kr⟩ =>
    ⟨h.wrS ws hd kk (by rw [v, h.val ha, h.val hc]) hl kr, kr⟩

/-- `clrW j`: the digit after `[j]` := 0, `[j]` kept. -/
theorem DS.clrW (h : DS s0 b A live V ls s) {j : Nat} (hj : (b, j) ∈ live)
    {live' : List (Bool × Nat)} (hl : ∀ e ∈ live', e ∈ live ∧ Sep (b, j) e) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, DS s0 b (upd A b j (A b j)) ((b, j) :: live') V ls t →
      w32 t.mem (rvB s0) (arr (vw s0 b) j + 4 * vw s0 b) = 0 → Keep [.r0, .r5] s t → WP isa (.block rest) t Q) :
    WP isa (.block (VG.Impl.Rsa.PPC64LE.Recover.clrW j ++ rest)) s Q :=
  clrW_ok (j := j) h.ws (h.ix hj) (vN_le b) fun t ws kk out z kr => by
    have f := h.fit b (h.ix hj)
    refine k t (h.wr ws (h.ix hj) kk ?_ hl kr) z kr
    have e : num s.mem (rvB s0) (vw s0 b) j = A b j := h.val hj
    rw [← e]
    exact out.val32 (by omega) (by simp only [S] at f; omega)

/-- A number of `w + 1` digits below `2^(32 w)` is its `w` digits. -/
theorem num_of_num1 {m : Mem} {B : Addr} {w j : Nat} (h : num1 m B w j < 2 ^ (32 * w)) :
    num m B w j = num1 m B w j := by
  rw [num1_eq] at h ⊢
  have := Nat.two_pow_pos (32 * w)
  rcases Nat.eq_zero_or_pos (w32 m B (arr w j + 4 * w)) with e | e
  · rw [e, Nat.mul_zero, Nat.add_zero]
  · have := Nat.le_mul_of_pos_right (2 ^ (32 * w)) e; omega

/-- `div q r d t`, the digit after `[d]` zero: `[q] := [q] / [d]` and `[r] := [q] mod [d]`
for `[d] > 0`. -/
theorem DS.div (h : DS s0 b A live V ls s) {q r d t : Nat} (hq : (b, q) ∈ live) (hd : (b, d) ∈ live)
    (hr : r < vN b) (ht : t < vN b) (hqr : q ≠ r) (hqd : q ≠ d) (hqt : q ≠ t) (hrd : r ≠ d) (hrt : r ≠ t)
    (hdt : d ≠ t) (hdz : w32 s.mem (rvB s0) (arr (vw s0 b) d + 4 * vw s0 b) = 0)
    {live' : List (Bool × Nat)} (hl : ∀ e ∈ live', e ∈ live ∧ ∀ j ∈ [q, r, t], Sep (b, j) e) :
    WP isa (VG.Impl.Rsa.PPC64LE.Div.div q r d t) s fun u => ∃ Q R,
      DS s0 b (upd (upd A b q Q) b r R) ((b, r) :: (b, q) :: live') V ls u ∧
      (0 < A b d → Q = A b q / A b d ∧ R = A b q % A b d) ∧ Keep stepRegs s u := by
  refine WP.mono (div_ok h.ws (h.ix hq) hr (h.ix hd) ht (vN_le b) hqr hqd hqt hrd hrt hdt hdz)
    fun u ⟨ws, kk, kr, v⟩ => ?_
  have hu := h.wrs ws (js := [q, r, t]) (fun j hj => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl
    · exact h.ix hq
    · exact hr
    · exact ht) kk hl kr
  have hu2 := hu.add (o := q) (h.ix hq) rfl (fun e he => sep_ne ((hl e he).2 q (by simp)))
  refine ⟨_, _, hu2.add (o := r) hr rfl (fun e he => ?_), fun pos => ?_, kr⟩
  · simp only [List.mem_cons] at he
    rcases he with rfl | he
    · intro e; exact hqr (Prod.mk.inj e).2
    · exact sep_ne ((hl e he).2 r (by simp))
  · obtain ⟨vq, vr⟩ := v (by rw [h.val hd]; exact pos)
    rw [h.val hq, h.val hd] at vq vr
    refine ⟨vq, ?_⟩
    have lt : A b q % A b d < 2 ^ (32 * vw s0 b) := Nat.lt_trans (Nat.mod_lt _ pos) (h.lt hd)
    rw [← vr]
    exact num_of_num1 (by rw [vr]; exact lt)

/-- The batched inverse (narrow): array 1 := `gcd(x, m)` for `x` in array 0 and an odd `m > 1`
in array 8. -/
theorem DS.inv [VG.Proof.Rsa.PPC64LE.InvLaw] (h : DS s0 false A live V ls s)
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (ww (kK s0))) (hx : (false, 0) ∈ live) (hm : (false, 8) ∈ live)
    (hodd : A false 8 % 2 = 1) {live' : List (Bool × Nat)}
    (hl : ∀ e ∈ live', e ∈ live ∧ ∀ j ∈ VG.Proof.Rsa.PPC64LE.invBatchArrs, Sep (false, j) e) :
    WP isa VG.Impl.Rsa.PPC64LE.InvBatch.inverse s fun t => ∃ G,
      DS s0 false (upd A false 1 G) ((false, 1) :: live') V ls t ∧
      (1 < A false 8 → G = Nat.gcd (A false 0) (A false 8)) ∧ Keep VG.Proof.Rsa.PPC64LE.invBatchRegs s t := by
  have w1 := h.base.sz.w1
  have hws : Ws s (rvB s0) (rvZ s0) (ww (kK s0)) 44 := h.ws
  have ax := h.val hx
  have am := h.val hm
  have lx := h.lt hx
  have lm := h.lt hm
  rw [vw_false] at ax am lx lm
  have hw : 10 ≤ ww (kK s0) := by omega
  have inv := VG.Proof.Rsa.PPC64LE.InvLaw.inverse_ok (n := ww (kK s0)) hws (by decide) (by decide) hw
    h11 (by omega) (Nat.le_refl _) ax lx am lm hodd
  refine WP.mono inv fun t ⟨ws, kk, kr, v⟩ => ?_
  have hjs : ∀ j ∈ VG.Proof.Rsa.PPC64LE.invBatchArrs, j < vN false := by decide
  have ht : DS s0 false A live' V ls t := h.wrs ws hjs kk hl kr
  have h1 : (1 : Nat) ∈ VG.Proof.Rsa.PPC64LE.invBatchArrs := by decide
  exact ⟨_, ht.add (b' := false) (o := 1) (by decide) rfl (fun e he => sep_ne ((hl e he).2 1 h1)),
    fun h1 => (v h1).1, kr⟩

/-- `ctxw`: from the wide view to the narrow. -/
theorem DS.toN (h : DS s0 true A live V ls s) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, DS s0 false A live V ls t → Keep [.r29, .r30] s t → WP isa (.block rest) t Q) :
    WP isa (.block (VG.Impl.Rsa.PPC64LE.Recover.ctxw ++ rest)) s Q := by
  have z := h.base.sz
  have := z.w1
  refine ctxw_ok (w := ww (kK s0)) (N' := nArr) h.ws (by omega) (by rw [← z.svw]; have := z.svZ; omega)
    fun t ws m kr => k t ⟨h.base.of_regs kr m, ws, (kr.gpr _ (by decide)).trans h.r21,
      (kr.gpr _ (by decide)).trans h.r23, (kr.gpr _ (by decide)).trans h.r25,
      fun e he => by rw [m]; exact h.arrs e he, h.live_lt, fun d hd => by rw [m]; exact h.sl d hd, h.ls_ok⟩ kr

/-- `ctxW`: from the narrow view to the wide. -/
theorem DS.toW (h : DS s0 false A live V ls s) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, DS s0 true A live V ls t → Keep [.r29, .r30] s t → WP isa (.block rest) t Q) :
    WP isa (.block (VG.Impl.Rsa.PPC64LE.Recover.ctxW ++ rest)) s Q := by
  have z := h.base.sz
  have e : arr (vw s0 true) 22 = sv (kK s0) := by rw [vw_wide, arr_wide]; rfl
  refine ctxW_ok (N' := 22) h.ws (by have := z.w2; show 2 * ww (kK s0) + 2 ≤ 1024; omega)
    (by show arr (vw s0 true) 22 ≤ _; rw [e]; have := z.svZ; omega)
    fun t ws m kr => k t ⟨h.base.of_regs kr m, ws, (kr.gpr _ (by decide)).trans h.r21,
      (kr.gpr _ (by decide)).trans h.r23, (kr.gpr _ (by decide)).trans h.r25,
      fun e he => by rw [m]; exact h.arrs e he, h.live_lt, fun d hd => by rw [m]; exact h.sl d hd, h.ls_ok⟩ kr

end

end VG.Proof.Rsa.PPC64LE.RecDet
