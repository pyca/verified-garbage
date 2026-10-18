module

public import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16W.Grp
public import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Rc4.AArch64.Vec

/-! # `vg_mlkem16_cbd2` on AArch64: eight iterations of 32 coefficients -/

@[expose] public section

namespace VG.Proof.MlKem

open VG VG.AArch64 VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- AArch64 contract for `vg_mlkem16_cbd2(b = x0, f = x1)`: writes
`SamplePolyCBD₂` of the 128 bytes at `b` to `f` with 16-bit coefficients,
reduced. The code may read `b` and write `f`, which do not overlap. -/
def cbd2_16AArch64 : Contract AArch64.isa where
  pre s :=
    s.rd = [⟨s.gpr .x0, 128⟩] ∧ s.wr = [⟨s.gpr .x1, 512⟩] ∧
    Region.Disjoint ⟨s.gpr .x0, 128⟩ ⟨s.gpr .x1, 512⟩
  post s s' := PolyIsW 16 s'.mem (s.gpr .x1) (samplePolyCBD 2 (bytesAt s.mem (s.gpr .x0) 128))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.sp = s₂.sp

end VG.Proof.MlKem

namespace VG.Proof.MlKem.AArch64.Cbd16W

open VG VG.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Spec.MlKem
open VG.Proof.MlKem.AArch64.Cbd16
open VG.Proof.Rc4.AArch64
open VG.Impl.MlKem.AArch64.Cbd16 (grp16 half16 body16 code16 tables constant prepare)
open VG.Spec.Sha3 (bytesAt)

section
variable (s₀ : State)

/-- The output. -/
abbrev fR : Region := ⟨Cbd2.fP s₀, 512⟩
/-- Coefficient `i` of the output. -/
abbrev coef (i : Nat) : Nat := ((samplePolyCBD 2 (Cbd2.B s₀))[i]!).val
/-- Byte `j` of the output: byte `j % 2` of coefficient `j / 2`. -/
def L (j : Nat) : Byte := BitVec.ofNat 8 (coef s₀ (j / 2) / 256 ^ (j % 2))
/-- The nibble of coefficient `32 k + i`. -/
abbrev nib (k i : Nat) : Nat :=
  (Cbd16.nibble (BitVec.ofNat 8 (Cbd2.byte s₀ (16 * k + i / 2))) (i % 2 != 0)).toNat

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [Cbd2.bR s₀]
  wr : s₀.wr = [fR s₀]
  disj : (Cbd2.bR s₀).Disjoint (fR s₀)

theorem Pre.byte_eq {s₀ : State} (hp : Pre s₀) {m : Mem} (hf : Frame [fR s₀] s₀.mem m)
    {j : Nat} (hj : j < 128) : (m (Cbd2.bP s₀ + BitVec.ofNat 64 j)).toNat = Cbd2.byte s₀ j := by
  rw [byte_frame (len := 128) hf (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.disj)
    (by decide) hj]
  show _ = ((bytesAt s₀.mem (Cbd2.bP s₀) 128).getD j 0).toNat
  rw [bytesAt_getD _ _ hj]

theorem nib_le (s₀ : State) (k i : Nat) : nib s₀ k i ≤ 4 :=
  (nibble_values _ (byte_lt _) _).1

/-- The bytes of the output, from the nibbles. -/
theorem L_nib (s₀ : State) {k i b : Nat} (hk : k < 8) (hi : i < 32) (hb : b < 2) :
    (L s₀ (64 * k + 2 * i + b)).toNat = (nib s₀ k i + 3327) % 3329 / 256 ^ b % 256 := by
  have hc : coef s₀ (32 * k + i) = (nib s₀ k i + 3327) % 3329 := by
    have h := G_nibble s₀ (i := 32 * k + i) (by omega)
    rw [Cbd2.G, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans (Fin.isLt _) (by decide)),
      show (32 * k + i) / 2 = 16 * k + i / 2 by omega, show (32 * k + i) % 2 = i % 2 by omega] at h
    exact h
  rw [L, BitVec.toNat_ofNat, show (64 * k + 2 * i + b) / 2 = 32 * k + i by omega,
    show (64 * k + 2 * i + b) % 2 = b by omega, hc]

/-- `n` bytes `x` stored at byte `t` of the output. -/
theorem bytes_write {m : Mem} {p : Addr} {N t n : Nat} {L old : Nat → Byte}
    (h : BytesUpTo m p N t L old) (hN : N < 2 ^ 32) (hn : t + n ≤ N) {x : BitVec (8 * n)}
    (hx : ∀ i < n, x.extractLsb' (8 * i) 8 = L (t + i)) :
    BytesUpTo (m.write (p + BitVec.ofNat 64 t) n x) p N (t + n) L old := by
  intro j hj
  have d : ((p + BitVec.ofNat 64 j) - (p + BitVec.ofNat 64 t)).toNat =
      if t ≤ j then j - t else 2 ^ 64 + j - t :=
    Offset.sub_toNat' p (by omega) (by omega)
  rw [Mem.write, d]
  by_cases ht : t ≤ j
  · rw [ite_eq_left ht]
    by_cases hnj : j - t < n
    · rw [ite_eq_left hnj, ite_eq_left (by omega), hx _ hnj]
      congr 1; omega
    · rw [ite_eq_right hnj, h j hj, ite_eq_right (by omega), ite_eq_right (by omega)]
  · rw [ite_eq_right ht, ite_eq_right (by omega), h j hj, ite_eq_left (by omega), ite_eq_left (by omega)]

/-- The constants of the loop. -/
structure Consts (s : State) : Prop where
  lo : s.v .v16 = loV
  hi : s.v .v17 = hiV
  c18 : s.v .v18 = broadcast 0x55
  c19 : s.v .v19 = broadcast 0x33
  c20 : s.v .v20 = broadcast 0x22
  c21 : s.v .v21 = broadcast 15

theorem Consts.of {s t : State} (h : Consts s) (hv : ∀ r, r ≠ .v0 → r ≠ .v1 → r ≠ .v2 → r ≠ .v3 →
    r ≠ .v4 → r ≠ .v5 → r ≠ .v6 → r ≠ .v7 → t.v r = s.v r) : Consts t :=
  ⟨by rw [hv _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact h.lo,
   by rw [hv _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact h.hi,
   by rw [hv _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact h.c18,
   by rw [hv _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact h.c19,
   by rw [hv _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact h.c20,
   by rw [hv _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact h.c21⟩

/-- The bytes of the output before the loop. -/
abbrev old (s₀ : State) (j : Nat) : Byte := s₀.mem (Cbd2.fP s₀ + BitVec.ofNat 64 j)

structure Inv (s₀ : State) (k : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x0 : s.gpr .x0 = Cbd2.bP s₀ + BitVec.ofNat 64 (16 * k)
  x1 : s.gpr .x1 = Cbd2.fP s₀ + BitVec.ofNat 64 (64 * k)
  count : (s.gpr .x10).toNat = 8 - k
  consts : Consts s
  out : BytesUpTo s.mem (Cbd2.fP s₀) 512 (64 * k) (L s₀) (old s₀)
  frame : Frame [fR s₀] s₀.mem s.mem

section
variable {rest : List Instr} {Q : State → Prop}

/-- Half an iteration: the 16 coefficients `32 k + 16 c + e`. -/
theorem half_ok {s₀ s : State} {k c off : Nat} (hk : k < 8) (hc : c < 2) (hoff : off = 32 * c)
    {part : VPermOp}
    (hw : s.wr = [fR s₀]) (hx1 : s.gpr .x1 = Cbd2.fP s₀ + BitVec.ofNat 64 (64 * k))
    (hcs : Consts s)
    (hv : ∀ e < 16, (vbyte (VPermOp.eval part .b16 (s.v .v2) (s.v .v3)) e).toNat = nib s₀ k (16 * c + e))
    (hout : BytesUpTo s.mem (Cbd2.fP s₀) 512 (64 * k + 32 * c) (L s₀) (old s₀))
    (hfr : Frame [fR s₀] s₀.mem s.mem)
    (k' : ∀ t, t.gpr = s.gpr → t.rd = s.rd → t.wr = s.wr → t.sp = s.sp →
      (∀ r, r ≠ .v4 → r ≠ .v5 → r ≠ .v6 → r ≠ .v7 → t.v r = s.v r) →
      BytesUpTo t.mem (Cbd2.fP s₀) 512 (64 * k + 32 * c + 32) (L s₀) (old s₀) →
      Frame [fR s₀] s₀.mem t.mem → WP isa (.block rest) t Q) :
    WP isa (.block (half16 off part ++ rest)) s Q := by
  subst hoff
  unfold half16
  simp only [List.cons_append, List.nil_append]
  refine wp_vop rfl fun s1 h1 => ?_
  have ea : Cbd2.fP s₀ + BitVec.ofNat 64 (64 * k) + BitVec.ofNat 64 (32 * c) =
      Cbd2.fP s₀ + BitVec.ofNat 64 (64 * k + 32 * c) := ptr_add _ _ _
  refine grp16_ok (F := fun e => nib s₀ k (16 * c + e)) (a := Cbd2.fP s₀ + BitVec.ofNat 64 (64 * k + 32 * c))
    (by omega)
    (by rw [h1.gpr, hx1]; exact ea)
    (by rw [h1.wr, hw]; exact in_regions (List.mem_singleton_self _) (contains_off (by omega) (by decide)))
    (by rw [h1.wr, hw, ptr_add]
        exact in_regions (List.mem_singleton_self _) (contains_off (by omega) (by decide)))
    (by rw [h1.get .v16]; exact hcs.lo) (by rw [h1.get .v17]; exact hcs.hi)
    (by rw [h1.v]; exact hv) (fun e _ => nib_le _ _ _) fun t x y g rd wr sp tv tm hx hy => ?_
  have o1 := bytes_write (n := 16) hout (by decide) (by omega) (x := x) fun b hb => by
    apply BitVec.eq_of_toNat_eq
    rw [show 64 * k + 32 * c + b = 64 * k + 2 * (16 * c + b / 2) + b % 2 by omega,
      L_nib s₀ hk (by omega) (Nat.mod_lt _ (by decide))]
    exact hx b hb
  have o2 := bytes_write (n := 16) o1 (by decide) (by omega) (x := y) fun b hb => by
    apply BitVec.eq_of_toNat_eq
    rw [show 64 * k + 32 * c + 16 + b = 64 * k + 2 * (16 * c + (8 + b / 2)) + b % 2 by omega,
      L_nib s₀ hk (by omega) (Nat.mod_lt _ (by decide))]
    exact hy b hb
  refine k' t (g.trans h1.gpr) (rd.trans h1.rd) (wr.trans h1.wr) (sp.trans h1.sp)
    (fun r r4 r5 r6 r7 => by rw [tv r r5 r6 r7, h1.get r r4]) ?_ ?_
  · rw [tm, h1.mem, ptr_add, show 64 * k + 32 * c + 32 = 64 * k + 32 * c + 16 + 16 by omega]
    exact o2
  · rw [tm, h1.mem]
    exact (hfr.write (n := 16) (List.mem_singleton_self _) _ (contains_off (by omega) (by decide))).write
      (n := 16) (List.mem_singleton_self _) _ (by rw [ptr_add]; exact contains_off (by omega) (by decide))

end

end VG.Proof.MlKem.AArch64.Cbd16W
