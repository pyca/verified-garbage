module

import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.EncLoop
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Mem
import VerifiedGarbage.Proof.MlKem.AArch64.Coeff16
public import VerifiedGarbage.Impl.MlKem.AArch64.Codec12W
public import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.Lanes
public import VerifiedGarbage.Proof.MlKem.AArch64.Common
public import VerifiedGarbage.Proof.MlKem.Kpke16Contract
import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.EncMath
import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.Bytes
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# ByteEncode₁₂ of a polynomial stored with 16 bits, on AArch64

`Impl.MlKem.AArch64.Codec12W.encW` writes `ByteEncode₁₂(P)` to the 384 bytes
at `x1`, for the polynomial `P` stored with 16 bits at `x0` (`encW_ok`): each
iteration widens eight coefficients to words (`vword_zip_zero`) and packs
them as `Codec16.math_ok` does.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Codec12W

open VG VG.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Spec.MlKem
open VG.Proof.MlKem.AArch64.Codec16
open VG.Impl.MlKem.AArch64.Codec12W (encBodyW encW)
open VG.Impl.MlKem.AArch64.Codec16 (maskVec)
open VG.Proof.Rc4.AArch64

/-- Code that writes none of `preservedV` keeps their low halves. -/
theorem WP.vcs {c : Prog isa} {s : State} {Q : State → Prop}
    (hc : (instrs c).all (fun i => preservedV.all fun r => vdstOf i != some r) = true)
    (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ ∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64 := by
  obtain ⟨t, s', he, hq⟩ := h
  refine ⟨t, s', he, hq, fun r hr => ?_⟩
  rw [Exec.vec (r := r) (fun i hi h' => ?_) he]
  have := List.all_eq_true.mp hc i hi
  have := List.all_eq_true.mp this r hr
  simp [h'] at this

/-- Code that writes no lane of `r` keeps it. -/
theorem WP.keepVR {c : Prog isa} {s : State} {Q : State → Prop} {r : VReg}
    (hc : ∀ i ∈ instrs c, vdstOf i ≠ some r) (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ s'.v r = s.v r := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, Exec.vec hc he⟩

/-- The registers `encW` writes. -/
abbrev encClob : List Reg := [.x0, .x1, .x9, .x10, .x11]

/-- What `encW` needs: the polynomial `P` stored with 16 bits at `p`, readable, and 384 writable
bytes at `o` apart from it. -/
structure EncData (s₀ : State) (p o : Addr) (P : Poly) : Prop where
  poly : PolyIsW 16 s₀.mem p P
  read : ∀ j, j + 16 ≤ 512 → InRegions (s₀.rd ++ s₀.wr) (p + BitVec.ofNat 64 j) 16
  write : ∀ j n, j + n ≤ 384 → InRegions s₀.wr (o + BitVec.ofNat 64 j) n
  apart : (⟨p, 512⟩ : Region).Disjoint ⟨o, 384⟩

/-- After `k` iterations. -/
structure EncInv (s₀ : State) (p o : Addr) (P : Poly) (k : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ encClob → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x0 : s.gpr .x0 = p + BitVec.ofNat 64 (16 * k)
  x1 : s.gpr .x1 = o + BitVec.ofNat 64 (12 * k)
  count : (s.gpr .x11).toNat = 32 - k
  mask : s.v .v16 = encMask
  zero : s.v .v17 = 0
  out : BytesUpTo s.mem o 384 (12 * k) (fun j => (encode12 P)[j]!) (fun j => s₀.mem (o + BitVec.ofNat 64 j))
  frame : Frame [⟨o, 384⟩] s₀.mem s.mem

/-- Four words of the coefficients `j … j + 3` of `P`, from halfwords widened by `zip1` or
`zip2` with zero. -/
theorem zip_lanes {m : Mem} {p : Addr} {P : Poly} (hp : PolyIsW 16 m p P) {j : Nat} (hj : j + 8 ≤ 256)
    {z : BitVec 128} (hz : z = 0) :
    Lanes (VPermOp.eval .zip1 .h8 (m.read (p + BitVec.ofNat 64 (2 * j)) 16) z) (fun e => (P[j + e]!).val) ∧
    Lanes (VPermOp.eval .zip2 .h8 (m.read (p + BitVec.ofNat 64 (2 * j)) 16) z)
      (fun e => (P[j + (4 + e)]!).val) := by
  have hz' : ∀ e < 8, vhalf z e = 0 := fun e _ => by subst hz; simp [vhalf]
  refine ⟨fun e he => ?_, fun e he => ?_⟩
  · rw [(Ntt16.vword_zip_zero hz' he).1, vhalf_read_coeff _ _ _ (by omega_arith), polyIsW16_toNat hp (by omega_arith)]
  · rw [(Ntt16.vword_zip_zero hz' he).2, vhalf_read_coeff _ _ _ (by omega_arith), polyIsW16_toNat hp (by omega_arith)]

theorem enc_step {s₀ : State} {p o : Addr} {P : Poly} (hd : EncData s₀ p o P) {k : Nat} (hk : k < 32)
    {s : State} (h : EncInv s₀ p o P k s) : WP isa (.block encBodyW) s fun t =>
      EncInv s₀ p o P (k + 1) t ∧ ((t.gpr .x11).toNat ≠ 0 ↔ k + 1 ≠ 32) := by
  have hpoly : PolyIsW 16 s.mem p P := by
    refine ⟨fun i hi => ?_, Vector.ext fun i hi => ?_⟩
    · have hi' : i < 256 := hi
      rw [coeffAtW, h.frame.readW (r := ⟨p, 512⟩) (contains_off (by omega_arith) (by decide))
        (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd.apart) (by decide)]
      exact hd.poly.1 i hi
    · rw [← hd.poly.2]
      simp only [polyAtW, Vector.getElem_ofFn, coeffAtW]
      have hi' : i < 256 := hi
      rw [h.frame.readW (r := ⟨p, 512⟩) (contains_off (by omega_arith) (by decide))
        (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd.apart) (by decide)]
  unfold encBodyW
  simp only [List.cons_append, List.nil_append]
  refine wp_ldrq (a := p + BitVec.ofNat 64 (2 * (8 * k))) (by decide)
    (by rw [h.x0, BitVec.add_zero]; congr 2; omega_arith)
    (by rw [h.rd, h.wr]; exact hd.read _ (by omega_arith)) fun s₁ h₁ => ?_
  refine wp_vop (d := .v0) rfl fun s₂ h₂ => wp_vop (d := .v1) rfl fun s₃ h₃ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keepVR (r := .v17) (by decide)
    (math_ok s₃ (by rw [h₃.get .v16, h₂.get .v16, h₁.get .v16]; exact h.mask))) ?_
  intro s₄ ⟨⟨x9, x10, m₄, rd₄, wr₄, sp₄, g₄, v₄⟩, v17₄⟩
  have z₁ : s₁.v .v17 = 0 := by rw [h₁.get .v17]; exact h.zero
  have L := zip_lanes (j := 8 * k) hpoly (by omega_arith) z₁
  let v := tbl (packed (s₃.v .v0) (s₃.v .v1)) encMask
  have bytes : ∀ j < 12, vbyte v j = (encode12 P)[12 * k + j]! := by
    intro j hj
    apply enc_spec P hk (j := j) _ _ hj
    · rw [h₃.get .v0, h₂.v, h₁.v]; exact L.1
    · rw [h₃.v, h₂.get .v4, h₂.get .v17, h₁.v]; exact L.2
  have g₃ : s₃.gpr = s.gpr := by rw [h₃.gpr, h₂.gpr, h₁.gpr]
  have g40 : s₄.gpr .x0 = s.gpr .x0 := by rw [g₄ .x0 (by decide) (by decide), g₃]
  have g41 : s₄.gpr .x1 = s.gpr .x1 := by rw [g₄ .x1 (by decide) (by decide), g₃]
  have g411 : s₄.gpr .x11 = s.gpr .x11 := by rw [g₄ .x11 (by decide) (by decide), g₃]
  have mem₄ : s₄.mem = s.mem := by rw [m₄, h₃.mem, h₂.mem, h₁.mem]
  have wrs₄ : s₄.wr = s.wr := by rw [wr₄, h₃.wr, h₂.wr, h₁.wr]
  have scalar : WP isa (.block [.str .x .x9 .x1 0, .str .w .x10 .x1 8,
      .addImm .x .x0 .x0 16, .addImm .x .x1 .x1 12, .subImm .x .x11 .x11 1]) s₄ fun t =>
      (∀ r, r ∉ [Reg.x0, .x1, .x11] → t.gpr r = s₄.gpr r) ∧ t.rd = s₄.rd ∧ t.wr = s₄.wr ∧ t.sp = s₄.sp ∧
      t.gpr .x0 = s₄.gpr .x0 + 16 ∧ t.gpr .x1 = s₄.gpr .x1 + 12 ∧
      (t.gpr .x11).toNat = 32 - (k + 1) ∧
      t.mem = (s₄.mem.write (o + BitVec.ofNat 64 (12 * k)) 8 (v.extractLsb' 0 64)).write
        (o + BitVec.ofNat 64 (12 * k + 8)) 4 ((v.extractLsb' 64 64).setWidth 32) := by
    refine wp_strx (a := o + BitVec.ofNat 64 (12 * k)) (by decide)
      (by rw [g41, h.x1, BitVec.add_zero]) ?_ fun s₅ h₅ => ?_
    · rw [wrs₄, h.wr]; exact hd.write _ _ (by omega_arith)
    refine wp_strw (a := o + BitVec.ofNat 64 (12 * k + 8)) (by decide)
      (by rw [h₅.gpr, g41, h.x1, ptr_add]) ?_ fun s₆ h₆ => ?_
    · rw [h₅.wr, wrs₄, h.wr]; exact hd.write _ _ (by omega_arith)
    refine wp_addImm (by decide) fun s₇ h₇ e₇ => wp_addImm (by decide) fun s₈ h₈ e₈ =>
      wp_subImm (by decide) fun s₉ h₉ e₉ => wp_nil ?_
    refine ⟨fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [h₉.get r (by simpa using hr.2.2), h₈.get r (by simpa using hr.2.1), h₇.get r (by simpa using hr.1),
        h₆.gpr, h₅.gpr]
    · rw [h₉.rd, h₈.rd, h₇.rd, h₆.rd, h₅.rd]
    · rw [h₉.wr, h₈.wr, h₇.wr, h₆.wr, h₅.wr]
    · rw [h₉.sp, h₈.sp, h₇.sp, h₆.sp, h₅.sp]
    · rw [h₉.get .x0, h₈.get .x0, e₇, h₆.gpr, h₅.gpr]; rfl
    · rw [h₉.get .x1, e₈, h₇.get .x1, h₆.gpr, h₅.gpr]; rfl
    · have c : (s₈.gpr .x11).toNat = 32 - k := by
        rw [h₈.get .x11, h₇.get .x11, h₆.gpr, h₅.gpr, g411, h.count]
      rw [e₉, toNat_sub_n (by rw [c]; simp; omega_arith), c]; simp; omega_arith
    · rw [h₉.mem, h₈.mem, h₇.mem, h₆.mem, h₅.mem, h₅.gpr, x9, x10]; rfl
  refine WP.mono (WP.keepV (by decide) scalar) ?_
  intro t ⟨⟨og, ord, owr, osp, p0, p1, ct, mt⟩, vt⟩
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ct, ?_, ?_, ?_, ?_⟩, by rw [ct]; omega_arith⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [og r (by simp [hr.1, hr.2.1, hr.2.2.2.2]),
      g₄ r hr.2.2.1 hr.2.2.2.1, g₃, h.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2])]
  · rw [ord, rd₄, h₃.rd, h₂.rd, h₁.rd, h.rd]
  · rw [owr, wrs₄, h.wr]
  · rw [osp, sp₄, h₃.sp, h₂.sp, h₁.sp, h.sp]
  · rw [p0, g40, h.x0, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, ptr_add]; congr 2
  · rw [p1, g41, h.x1, show (12 : BitVec 64) = BitVec.ofNat 64 12 from rfl, ptr_add]; congr 2
  · rw [vt, v₄, h₃.get .v16, h₂.get .v16, h₁.get .v16, h.mask]
  · rw [vt, v17₄, h₃.get .v17, h₂.get .v17, z₁]
  · rw [mt, mem₄, show 12 * (k + 1) = 12 * k + 8 + 4 by omega_arith]
    refine bytes_write (bytes_write h.out (by omega_arith) ?_) (by omega_arith) ?_
    · intro j hj; rw [low_byte _ hj]; exact bytes j (by omega_arith)
    · intro j hj; rw [high_byte _ hj]
      simpa only [Nat.add_assoc] using bytes (8 + j) (by omega_arith)
  · rw [mt, mem₄]
    exact (h.frame.write (n := 8) (List.mem_singleton_self _) _ (contains_off (by omega_arith) (by decide))).write
      (n := 4) (List.mem_singleton_self _) _ (contains_off (by omega_arith) (by decide))

theorem enc_init {s : State} {p o : Addr} (P : Poly) (h0 : s.gpr .x0 = p) (h1 : s.gpr .x1 = o) :
    WP isa (.block (maskVec .v16 [0,1,2,4,5,6,8,9,10,12,13,14] ++
      ([.vop (.movi0 .v17), .movz .x .x11 32 0] : List Instr))) s (EncInv s p o P 0) := by
  dsimp [maskVec, VG.Impl.MlKem.AArch64.movImm]
  rrun [RegUpd.sp_write, RegUpd.sp_setV]
  refine ⟨fun r hr => ?_, rfl, rfl, rfl, ?_, ?_, rfl, ?_, rfl, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setV, RegUpd.gpr_write, hr.2.2.1, hr.2.2.2.2, ite_false]
  · change s.gpr .x0 = p + BitVec.ofNat 64 (16 * 0); rw [h0]; exact (BitVec.add_zero _).symm
  · change s.gpr .x1 = o + BitVec.ofNat 64 (12 * 0); rw [h1]; exact (BitVec.add_zero _).symm
  · rw [encMask_value]; rfl
  · exact BytesUpTo.zero _
  · exact Frame.refl _ _

theorem encW_ok {s : State} {p o : Addr} {P : Poly} (h0 : s.gpr .x0 = p) (h1 : s.gpr .x1 = o)
    (hd : EncData s p o P) :
    WP isa encW s fun s' => Keep encClob s s' ∧ Frame [⟨o, 384⟩] s.mem s'.mem ∧
      Spec.Sha3.bytesAt s'.mem o 384 = encode12 P := by
  refine WP.mono (WP.vcs (by decide +kernel) (WP.seq (WP.mono (enc_init P h0 h1) fun s₁ h₁ =>
    count_loop (by decide) (EncInv s p o P) (fun k hk t ht => enc_step hd hk ht) h₁)))
    fun s' ⟨h', vcs⟩ => ⟨⟨h'.gpr, h'.rd, h'.wr, h'.sp, vcs⟩, h'.frame,
      (show BytesUpTo s'.mem o 384 384 _ _ from h'.out).eq (encode12_length _) fun _ _ => rfl⟩

end VG.Proof.MlKem.AArch64.Codec12W
