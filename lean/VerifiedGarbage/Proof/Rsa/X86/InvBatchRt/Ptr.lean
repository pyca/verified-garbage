module

public import VerifiedGarbage.Impl.Rsa.X86.InvBatchRt
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Base
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Weierstrass.MontContract

/-! # Pointers and counts of the run-time-width batch

`Slots`: the header words `init` fills, the cached arrays' addresses and the
bytes of `n` words. `ptr_ok`: a pointer at a `Ref`,
`offset w arr + 4 n · half + byte` for arrays of `w` words and halves of `n` (by
default `w / 2`, the modulus's primes; prime recovery's GCD takes `n = w / 2 + 1`);
`nBytes_ok`, `nBytesLess_ok` and `wBytes_ok`: the bytes of `n + e`, `n - 1` and
`2 n` words.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Rsa.X86.KeyRt
open VG.Proof.Rsa.X86.Keys (arr)

/-- A `Ref`'s offset in the working space, for arrays of `w` words and halves of `n`. -/
def rv (w : Nat) (x : Ref) (n : Nat := w / 2) : Nat :=
  VG.Impl.Rsa.X86.InvBatchRt.offset w x.arr + x.half * (4 * n) + x.byte

/-- A `Ref` in an array's first half does not depend on the halves' size. -/
theorem rv_h0 {w : Nat} {x : Ref} (hx : x.half = 0) (n n' : Nat) : rv w x n = rv w x n' := by
  simp only [rv, hx, Nat.zero_mul]

theorem offset_eq (w j : Nat) : VG.Impl.Rsa.X86.InvBatchRt.offset w j = arr w j := by
  simp only [VG.Impl.Rsa.X86.InvBatchRt.offset, arr, VG.Proof.Rsa.X86.Keys.S, VG.Impl.Rsa.X86.Keys.hdr]
  rw [show 4 * (w + 2) = 4 * w + 8 by omega]

/-- The header words `init` fills: each cached array's address, and `4 n`. -/
structure Slots (m : Mem) (B : Addr) (w : Nat) (n : Nat := w / 2) : Prop where
  addr : ∀ j d, slot j = some d → w32 m B d = (B.toNat + VG.Impl.Rsa.X86.InvBatchRt.offset w j) % 2 ^ 32
  half : w32 m B halfSlot = 4 * n
  small : 4 * n < 2 ^ 32
  pos : 0 < n

theorem Slots.halfW {m : Mem} {B : Addr} {w n : Nat} (h : Slots m B w n) :
    m.readW (off B halfSlot) 32 = BitVec.ofNat 32 (4 * n) :=
  BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h.small]; exact h.half)

theorem slot_le {j d : Nat} (h : slot j = some d) : slotBase ≤ d ∧ d + 4 ≤ halfSlot := by
  simp only [slot, Option.map_eq_some_iff] at h
  obtain ⟨i, hi, rfl⟩ := h
  have := List.idxOf?_eq_some_iff.mp hi
  have hl : i < 11 := by simpa [cached] using this.1
  simp only [slotBase, halfSlot]; omega

variable {L : Lay} {B : Addr} {Z len N w n : Nat} {is : List Instr} {s : State} {Q : State → Prop}

/-- `r += t`, `j` times. -/
theorem addsReg_ok {r t : Reg} (hrt : r ≠ t) (j : Nat) :
    ∀ {s : State}, (∀ u, Keeps [r] s u → u.mem = s.mem → u.gpr r = s.gpr r + BitVec.ofNat 32 (j * (s.gpr t).toNat) →
      WP isa (.block is) u Q) →
    WP isa (.block (List.replicate j (.alu .add r (.reg t)) ++ is)) s Q := by
  induction j with
  | zero => intro s k; exact k s (Keeps.refl _ _) rfl (by simp)
  | succ j ih =>
    intro s k
    rw [List.replicate_succ, List.cons_append]
    refine wp_addS rfl fun s₁ U₁ _ => ?_
    have et : s₁.gpr t = s.gpr t := U₁.other _ (Ne.symm hrt)
    refine ih fun u K m e => k u (U₁.keeps.trans K) (m.trans U₁.mem) ?_
    rw [e, U₁.gpr, et, BitVec.add_assoc]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.succ_mul]
    generalize j * (s.gpr t).toNat = J
    omega

/-- `ptr r x t`: `r` at `x` (`r` may be `edi` only for a `Ref` with no `n`-word steps). -/
theorem ptr_ok {r t : Reg} {x : Ref} (h : RtWs L s B Z len N) (hsl : Slots s.mem B (kw len) n)
    (hz : halfSlot + 4 ≤ Z) (hrt : r ≠ t) (hte : t ≠ .edi) (hrs : r ≠ .esp) (hts : t ≠ .esp)
    (hre : r = .edi → x.half = 0)
    (hb : rv (kw len) x n < 2 ^ 32)
    (k : ∀ u, Keeps [r, t] s u → u.mem = s.mem → PtrAt u B r (rv (kw len) x n) → WP isa (.block is) u Q) :
    WP isa (.block (ptr L r x t ++ is)) s Q := by
  have hw := kw_bound h.lenLe
  have hs := h.ws.workspace
  have nw := hs.nowrap
  have ha : arr (kw len) x.arr < 2 ^ 32 := by
    have := offset_eq (kw len) x.arr; simp only [rv] at hb; omega
  simp only [ptr, List.append_assoc]
  -- The array's address.
  have base : ∀ {is' : List Instr} {Q' : State → Prop}, (∀ v, Keeps [r, t] s v → v.mem = s.mem →
      PtrAt v B r (arr (kw len) x.arr) → WP isa (.block is') v Q') →
      WP isa (.block ((match slot x.arr with
        | some d => [.mov r (.mem (sc d))]
        | none => arrPtr L r x.arr t) ++ is')) s Q' := by
    intro is' Q' k'
    split
    · next d hd =>
      have := slot_le hd
      rw [List.cons_append, List.nil_append]
      refine wp_movS (readSrc_sc hs (d := d) (by omega)) fun v V _ => k' v (V.keeps.mono (by simp)) V.mem ?_
      rw [PtrAt, V.gpr, ← offset_eq]; exact hsl.addr _ _ hd
    · exact arrPtr_ok (lenSrc h) h.lenLe h.edi hrt hte ha fun v V m p _ => k' v V m p
  refine base fun v V mv pv => ?_
  -- The `n`-word steps.
  have half : ∀ {is' : List Instr} {Q' : State → Prop}, (∀ u, Keeps [r, t] s u → u.mem = s.mem →
      PtrAt u B r (arr (kw len) x.arr + x.half * (4 * n)) → WP isa (.block is') u Q') →
      WP isa (.block ((if x.half = 0 then [] else .mov t (.mem (sc halfSlot)) ::
        List.replicate x.half (.alu .add r (.reg t))) ++ is')) v Q' := by
    intro is' Q' k'
    by_cases h0 : x.half = 0
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h0), List.nil_append]
      exact k' v V mv (by rw [h0, Nat.zero_mul, Nat.add_zero]; exact pv)
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h0), List.cons_append]
      have hsv : Scr v B Z := hs.of_keeps V
        (by simp only [List.mem_cons, List.not_mem_nil, or_false]
            exact fun e => e.elim (fun e => (fun e' => h0 (hre e')) e.symm) (fun e => hte e.symm))
        (by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact fun e => e.elim (fun e => hrs e.symm) (fun e => hts e.symm))
      refine wp_movS (readSrc_sc hsv hz) fun v₁ V₁ _ => ?_
      have tv : (v₁.gpr t).toNat = 4 * n := by
        rw [V₁.gpr, mv, hsl.halfW, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsl.small]
      have pv₁ : PtrAt v₁ B r (arr (kw len) x.arr) := by rw [PtrAt, V₁.other _ hrt]; exact pv
      refine addsReg_ok hrt x.half fun u U mu eu =>
        k' u (V.trans ((V₁.keeps.mono (by simp)).trans (U.mono (by simp)))) (by rw [mu, V₁.mem, mv]) ?_
      rw [PtrAt, eu, BitVec.toNat_add, pv₁, BitVec.toNat_ofNat, tv]
      generalize x.half * (4 * n) = H
      omega
  refine half fun u U mu pu => ?_
  split
  · next hb0 =>
    rw [List.nil_append]
    refine k u U mu ?_
    rw [show rv (kw len) x n = arr (kw len) x.arr + x.half * (4 * n) by
      simp only [rv, offset_eq, hb0, Nat.add_zero]]
    exact pu
  · next hb0 =>
    rw [List.cons_append, List.nil_append]
    refine wp_addS rfl fun z Z' _ => k z (U.trans (Z'.keeps.mono (by simp))) (by rw [Z'.mem, mu]) ?_
    rw [PtrAt, Z'.gpr, BitVec.toNat_add, pu, rv, offset_eq, BitVec.toNat_ofNat]
    generalize x.half * (4 * n) = H at *
    omega

/-- `nBytes r e`: `r = 4 n + 4 e`, the bytes of `n + e` words. -/
theorem nBytes_ok {r : Reg} {e : Nat} (hs : Scr s B Z) (hsl : Slots s.mem B w n) (hz : halfSlot + 4 ≤ Z)
    (hw : 4 * n + 16 < 2 ^ 32) (he : e ≤ 4)
    (k : ∀ u, Keeps [r] s u → u.mem = s.mem → (u.gpr r).toNat = 4 * n + 4 * e → WP isa (.block is) u Q) :
    WP isa (.block (nBytes r e ++ is)) s Q := by
  simp only [nBytes, List.cons_append, List.nil_append]
  refine wp_movS (readSrc_sc hs hz) fun u U _ => wp_addS rfl fun z Z' _ => ?_
  refine k z (U.keeps.trans Z'.keeps) (by rw [Z'.mem, U.mem]) ?_
  rw [Z'.gpr, BitVec.toNat_add, U.gpr, show (s.mem.readW (off B halfSlot) 32).toNat = 4 * n from hsl.half,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 4 * e) (by omega)]
  omega

/-- `nBytesLess r`: `r = 4 n - 4`, the bytes of `n - 1` words. -/
theorem nBytesLess_ok {r : Reg} (hs : Scr s B Z) (hsl : Slots s.mem B w n) (hz : halfSlot + 4 ≤ Z)
    (hw : 4 * n < 2 ^ 32) (h2 : 1 ≤ n)
    (k : ∀ u, Keeps [r] s u → u.mem = s.mem → (u.gpr r).toNat = 4 * n - 4 → WP isa (.block is) u Q) :
    WP isa (.block (nBytesLess r ++ is)) s Q := by
  simp only [nBytesLess, List.cons_append, List.nil_append]
  refine wp_movS (readSrc_sc hs hz) fun u U _ => wp_subS rfl fun z Z' _ => ?_
  refine k z (U.keeps.trans Z'.keeps) (by rw [Z'.mem, U.mem]) ?_
  rw [Z'.gpr, BitVec.toNat_sub, U.gpr, show (s.mem.readW (off B halfSlot) 32).toNat = 4 * n from hsl.half]
  simp only [show (4 : BitVec 32).toNat = 4 from rfl]
  omega

/-- `wBytes r`: `r = 8 n`, the bytes of `2 n` words. -/
theorem wBytes_ok {r : Reg} (hs : Scr s B Z) (hsl : Slots s.mem B w n) (hz : halfSlot + 4 ≤ Z)
    (hw : 8 * n < 2 ^ 32)
    (k : ∀ u, Keeps [r] s u → u.mem = s.mem → (u.gpr r).toNat = 8 * n → WP isa (.block is) u Q) :
    WP isa (.block (wBytes r ++ is)) s Q := by
  simp only [wBytes, List.cons_append, List.nil_append]
  refine wp_movS (readSrc_sc hs hz) fun u U _ => wp_addS rfl fun z Z' _ => ?_
  refine k z (U.keeps.trans Z'.keeps) (by rw [Z'.mem, U.mem]) ?_
  rw [Z'.gpr, BitVec.toNat_add, U.gpr, show (s.mem.readW (off B halfSlot) 32).toNat = 4 * n from hsl.half]
  omega

end VG.Proof.Rsa.X86.InvBatchRt
