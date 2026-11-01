module

public import VerifiedGarbage.Impl.Rsa.X86.InvBatchRt
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Base
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Weierstrass.MontContract

/-! # Pointers and counts of the run-time-width batch

`Slots`: the header words `init` fills, the cached arrays' addresses and the
bytes of `n` words. `ptr_ok`: a pointer at a `Ref`,
`offset w arr + 2 w · half + byte` for the modulus's `w` words (`4 n` bytes
with `n = w / 2`); `nBytes_ok`, `nBytesLess_ok` and `wBytes_ok`: the bytes of
`n + e`, `n - 1` and `w` words.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Rsa.X86.KeyRt
open VG.Proof.Rsa.X86.Keys (arr)

/-- A `Ref`'s offset in the working space, for arrays of `w` words. -/
def rv (w : Nat) (x : Ref) : Nat := VG.Impl.Rsa.X86.InvBatchRt.offset w x.arr + x.half * (2 * w) + x.byte

theorem offset_eq (w j : Nat) : VG.Impl.Rsa.X86.InvBatchRt.offset w j = arr w j := by
  simp only [VG.Impl.Rsa.X86.InvBatchRt.offset, arr, VG.Proof.Rsa.X86.Keys.S, VG.Impl.Rsa.X86.Keys.hdr]
  rw [show 4 * (w + 2) = 4 * w + 8 by omega]

/-- The header words `init` fills: each cached array's address, and `2 w`. -/
structure Slots (m : Mem) (B : Addr) (w : Nat) : Prop where
  addr : ∀ j d, slot j = some d → w32 m B d = (B.toNat + VG.Impl.Rsa.X86.InvBatchRt.offset w j) % 2 ^ 32
  half : w32 m B halfSlot = 2 * w
  small : 2 * w < 2 ^ 32

theorem Slots.halfW {m : Mem} {B : Addr} {w : Nat} (h : Slots m B w) :
    m.readW (off B halfSlot) 32 = BitVec.ofNat 32 (2 * w) :=
  BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h.small]; exact h.half)

theorem slot_le {j d : Nat} (h : slot j = some d) : slotBase ≤ d ∧ d + 4 ≤ halfSlot := by
  simp only [slot, Option.map_eq_some_iff] at h
  obtain ⟨i, hi, rfl⟩ := h
  have := List.idxOf?_eq_some_iff.mp hi
  have hl : i < 11 := by simpa [cached] using this.1
  simp only [slotBase, halfSlot]; omega

variable {L : Lay} {B : Addr} {Z len N w : Nat} {is : List Instr} {s : State} {Q : State → Prop}

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
theorem ptr_ok {r t : Reg} {x : Ref} (h : RtWs L s B Z len N) (hsl : Slots s.mem B (kw len))
    (hz : halfSlot + 4 ≤ Z) (hrt : r ≠ t) (hte : t ≠ .edi) (hrs : r ≠ .esp) (hts : t ≠ .esp)
    (hre : r = .edi → x.half = 0)
    (hb : rv (kw len) x < 2 ^ 32)
    (k : ∀ u, Keeps [r, t] s u → u.mem = s.mem → PtrAt u B r (rv (kw len) x) → WP isa (.block is) u Q) :
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
      PtrAt u B r (arr (kw len) x.arr + x.half * (2 * kw len)) → WP isa (.block is') u Q') →
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
      have tv : (v₁.gpr t).toNat = 2 * kw len := by
        rw [V₁.gpr, mv, hsl.halfW, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsl.small]
      have pv₁ : PtrAt v₁ B r (arr (kw len) x.arr) := by rw [PtrAt, V₁.other _ hrt]; exact pv
      refine addsReg_ok hrt x.half fun u U mu eu =>
        k' u (V.trans ((V₁.keeps.mono (by simp)).trans (U.mono (by simp)))) (by rw [mu, V₁.mem, mv]) ?_
      rw [PtrAt, eu, BitVec.toNat_add, pv₁, BitVec.toNat_ofNat, tv]
      generalize x.half * (2 * kw len) = H
      omega
  refine half fun u U mu pu => ?_
  split
  · next hb0 =>
    rw [List.nil_append]
    refine k u U mu ?_
    rw [show rv (kw len) x = arr (kw len) x.arr + x.half * (2 * kw len) by
      simp only [rv, offset_eq, hb0, Nat.add_zero]]
    exact pu
  · next hb0 =>
    rw [List.cons_append, List.nil_append]
    refine wp_addS rfl fun z Z' _ => k z (U.trans (Z'.keeps.mono (by simp))) (by rw [Z'.mem, mu]) ?_
    rw [PtrAt, Z'.gpr, BitVec.toNat_add, pu, rv, offset_eq, BitVec.toNat_ofNat]
    generalize x.half * (2 * kw len) = H at *
    omega

/-- `nBytes r e`: `r = 2 w + 4 e`, the bytes of `n + e` words. -/
theorem nBytes_ok {r : Reg} {e : Nat} (hs : Scr s B Z) (hsl : Slots s.mem B w) (hz : halfSlot + 4 ≤ Z)
    (hw : 2 * w ≤ 4104) (he : e ≤ 4)
    (k : ∀ u, Keeps [r] s u → u.mem = s.mem → (u.gpr r).toNat = 2 * w + 4 * e → WP isa (.block is) u Q) :
    WP isa (.block (nBytes r e ++ is)) s Q := by
  simp only [nBytes, List.cons_append, List.nil_append]
  refine wp_movS (readSrc_sc hs hz) fun u U _ => wp_addS rfl fun z Z' _ => ?_
  refine k z (U.keeps.trans Z'.keeps) (by rw [Z'.mem, U.mem]) ?_
  rw [Z'.gpr, BitVec.toNat_add, U.gpr, show (s.mem.readW (off B halfSlot) 32).toNat = 2 * w from hsl.half,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 4 * e) (by omega)]
  omega

/-- `nBytesLess r`: `r = 2 w - 4`, the bytes of `n - 1` words. -/
theorem nBytesLess_ok {r : Reg} (hs : Scr s B Z) (hsl : Slots s.mem B w) (hz : halfSlot + 4 ≤ Z)
    (hw : 2 * w ≤ 4104) (h2 : 2 ≤ w)
    (k : ∀ u, Keeps [r] s u → u.mem = s.mem → (u.gpr r).toNat = 2 * w - 4 → WP isa (.block is) u Q) :
    WP isa (.block (nBytesLess r ++ is)) s Q := by
  simp only [nBytesLess, List.cons_append, List.nil_append]
  refine wp_movS (readSrc_sc hs hz) fun u U _ => wp_subS rfl fun z Z' _ => ?_
  refine k z (U.keeps.trans Z'.keeps) (by rw [Z'.mem, U.mem]) ?_
  rw [Z'.gpr, BitVec.toNat_sub, U.gpr, show (s.mem.readW (off B halfSlot) 32).toNat = 2 * w from hsl.half]
  simp only [show (4 : BitVec 32).toNat = 4 from rfl]
  omega

/-- `wBytes r`: `r = 4 w`, the bytes of `w` words. -/
theorem wBytes_ok {r : Reg} (hs : Scr s B Z) (hsl : Slots s.mem B w) (hz : halfSlot + 4 ≤ Z)
    (hw : 2 * w ≤ 4104)
    (k : ∀ u, Keeps [r] s u → u.mem = s.mem → (u.gpr r).toNat = 4 * w → WP isa (.block is) u Q) :
    WP isa (.block (wBytes r ++ is)) s Q := by
  simp only [wBytes, List.cons_append, List.nil_append]
  refine wp_movS (readSrc_sc hs hz) fun u U _ => wp_addS rfl fun z Z' _ => ?_
  refine k z (U.keeps.trans Z'.keeps) (by rw [Z'.mem, U.mem]) ?_
  rw [Z'.gpr, BitVec.toNat_add, U.gpr, show (s.mem.readW (off B halfSlot) 32).toNat = 2 * w from hsl.half]
  omega

end VG.Proof.Rsa.X86.InvBatchRt
