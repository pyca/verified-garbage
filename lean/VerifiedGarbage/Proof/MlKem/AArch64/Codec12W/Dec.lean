module
public import VerifiedGarbage.Proof.MlKem.AArch64.Coeff16
public import VerifiedGarbage.Impl.MlKem.AArch64.Codec12W
public import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.DecBase
public import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.DecLanes

import VerifiedGarbage.Proof.MlKem.AArch64.Codec12W.Enc
import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.DecLoop
import VerifiedGarbage.Proof.MlKem.AArch64.DotW.Store
import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.DecInput
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
import VerifiedGarbage.Proof.Sha3.AArch64.Sums
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# ByteDecode₁₂ to a polynomial stored with 16 bits, on AArch64

`Impl.MlKem.AArch64.Codec12W.decW` writes `ByteDecode₁₂` of the 384 bytes at
`x0` to `x1` with 16-bit coefficients (`decW_ok`): each iteration decodes
eight coefficients into words as `Codec16.dec_math_ok` does, and narrows
them to halfwords (`DotW.narrow_lanes`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Codec12W

open VG VG.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Spec.MlKem
open VG.Proof.MlKem.AArch64.Codec16
open VG.Impl.MlKem.AArch64.Codec12W (decBodyW decW)
open VG.Impl.MlKem.AArch64.Codec16 (maskVec)
open VG.Proof.Rc4.AArch64

/-- The registers `decW` writes. -/
abbrev decClob : List Reg := [.x0, .x1, .x9, .x10, .x11]

/-- What `decW` needs of the state `s₀` it starts in: 384 readable bytes at `x0`, and 512
writable bytes at `x1` apart from them. -/
structure DecData (s₀ : State) : Prop where
  read : ∀ j n, j + n ≤ 384 → InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x0 + BitVec.ofNat 64 j) n
  write : ∀ j, j + 16 ≤ 512 → InRegions s₀.wr (s₀.gpr .x1 + BitVec.ofNat 64 j) 16
  apart : (⟨s₀.gpr .x0, 384⟩ : Region).Disjoint ⟨s₀.gpr .x1, 512⟩

/-- Coefficient `i` of the output, with 16 bits. -/
def GW (s₀ : State) (i : Nat) : BitVec 16 := BitVec.ofNat 16 ((decode12 (Decode12.B s₀))[i]!).val

/-- After `k` iterations. -/
structure DecInv (s₀ : State) (k : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ decClob → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x0 : s.gpr .x0 = s₀.gpr .x0 + BitVec.ofNat 64 (12 * k)
  x1 : s.gpr .x1 = s₀.gpr .x1 + BitVec.ofNat 64 (16 * k)
  count : (s.gpr .x11).toNat = 32 - k
  mask : s.v .v16 = decMask
  bits : s.v .v17 = mask12
  q : s.v .v18 = qvec
  out : CoeffsInW s.mem (s₀.gpr .x1) (· < 8 * k) (GW s₀) fun i => coeffAtW 16 s₀.mem (s₀.gpr .x1) i
  frame : Frame [⟨s₀.gpr .x1, 512⟩] s₀.mem s.mem

theorem dec_step {s₀ : State} (hd : DecData s₀) {k : Nat} (hk : k < 32) {s : State} (h : DecInv s₀ k s) :
    WP isa (.block decBodyW) s fun t => DecInv s₀ (k + 1) t ∧ ((t.gpr .x11).toNat ≠ 0 ↔ k + 1 ≠ 32) := by
  have load : WP isa (.block [.ldr .x .x9 .x0 0, .ldr .w .x10 .x0 8]) s fun t =>
      Only [.x9, .x10] s t ∧ t.gpr .x9 = s.mem.readW (s.gpr .x0) 64 ∧
      t.gpr .x10 = (s.mem.readW (s.gpr .x0 + 8) 32).setWidth 64 := by
    refine wp_ldrx (a := s.gpr .x0) (by decide) (by simp) ?_ fun s1 h1 e1 => ?_
    · rw [h.rd, h.wr, h.x0]; exact hd.read _ _ (by omega)
    refine wp_ldrw (a := s.gpr .x0 + 8) (by decide) (by rw [h1.get .x0]; rfl) ?_ fun s2 h2 e2 => wp_nil ?_
    · rw [h1.rd, h1.wr, h.rd, h.wr, h.x0, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, ptr_add]
      exact hd.read _ _ (by omega)
    refine ⟨h1.trans h2, by rw [h2.get .x9, e1], ?_⟩
    rw [e2, h1.mem]
  unfold decBodyW
  rw [List.append_assoc]
  refine wp_scalar (by decide) load ?_
  intro s2 ⟨hl, x9, x10⟩ vl
  rw [WP.block_append_iff]
  refine WP.mono (dec_math_ok s2 (by rw [vl, h.mask]) (by rw [vl, h.bits]) (by rw [vl, h.q])) ?_
  intro s3 ⟨v0, v1, g3, m3, rd3, wr3, sp3, hv3⟩
  let x := ofVDwords (s2.gpr .x9) (s2.gpr .x10)
  have xb : ∀ j < 12, (vbyte x j).toNat = Decode12.byte s₀ (12 * k + j) := by
    intro j hj
    rw [show x = ofVDwords (s.mem.readW (s.gpr .x0) 64)
      ((s.mem.readW (s.gpr .x0 + 8) 32).setWidth 64) by dsimp only [x]; rw [x9, x10], input_byte _ _ hj,
      h.x0, ptr_add, byte_frame (len := 384) h.frame
        (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd.apart) (by decide) (by omega)]
    show _ = ((Spec.Sha3.bytesAt s₀.mem (s₀.gpr .x0) 384).getD _ 0).toNat
    rw [bytesAt_getD _ _ (by omega)]
  have vals : ∀ e < 4, vword (s3.v .v0) e = Decode12.G s₀ (8 * k + e) ∧
      vword (s3.v .v1) e = Decode12.G s₀ (8 * k + 4 + e) := by
    intro e he; rw [v0, v1]; exact decoded_spec s₀ hk xb he
  have gv : ∀ i, (Decode12.G s₀ i).toNat = ((decode12 (Decode12.B s₀))[i]!).val := fun i => by
    have : ((decode12 (Decode12.B s₀))[i]!).val < 3329 := Fin.isLt _
    rw [Decode12.G, BitVec.toNat_ofNat]; omega
  have N := DotW.narrow_lanes (x := s3.v .v0) (y := s3.v .v1)
    (A := fun e => ((decode12 (Decode12.B s₀))[8 * k + e]!).val)
    (B := fun e => ((decode12 (Decode12.B s₀))[8 * k + 4 + e]!).val)
    (fun e he => by rw [(vals e he).1, gv]) (fun e he => by rw [(vals e he).2, gv])
    (fun e _ => by have : ((decode12 (Decode12.B s₀))[8 * k + e]!).val < 3329 := Fin.isLt _; omega)
    (fun e _ => by have : ((decode12 (Decode12.B s₀))[8 * k + 4 + e]!).val < 3329 := Fin.isLt _; omega)
  have gp (r : Reg) (hr : r ∉ [.x9, .x10]) : s3.gpr r = s.gpr r := by rw [g3, hl.gpr _ hr]
  have mm3 : s3.mem = s.mem := m3.trans hl.mem
  refine wp_vop (d := .v0) rfl fun s4 h4 => ?_
  refine wp_strq (a := s₀.gpr .x1 + BitVec.ofNat 64 (2 * (8 * k))) (by decide)
    (by rw [h4.gpr, gp .x1 (by decide), h.x1, BitVec.add_zero]; congr 2; omega) ?_ fun s5 h5 => ?_
  · rw [h4.wr, wr3, hl.wr, h.wr]; exact hd.write _ (by omega)
  have scalar : WP isa (.block [.addImm .x .x0 .x0 12, .addImm .x .x1 .x1 16, .subImm .x .x11 .x11 1]) s5
      fun t => Only [.x0, .x1, .x11] s5 t ∧ t.gpr .x0 = s5.gpr .x0 + 12 ∧
        t.gpr .x1 = s5.gpr .x1 + 16 ∧ (t.gpr .x11).toNat = 32 - (k + 1) := by
    refine wp_addImm (by decide) fun s6 h6 e6 => wp_addImm (by decide) fun s7 h7 e7 =>
      wp_subImm (by decide) fun s8 h8 e8 => wp_nil ?_
    refine ⟨((h6.trans h7).trans h8).mono (by decide), ?_, ?_, ?_⟩
    · rw [h8.get .x0, h7.get .x0, e6]; rfl
    · rw [h8.get .x1, e7, h6.get .x1]; rfl
    · have cnt : (s7.gpr .x11).toNat = 32 - k := by
        rw [h7.get .x11, h6.get .x11, h5.gpr, h4.gpr, gp .x11 (by decide), h.count]
      rw [e8, toNat_sub_n (by rw [cnt]; simp; omega), cnt]; simp; omega
  refine WP.mono (WP.keepV (by decide) scalar) ?_
  intro t ⟨⟨ht, p0, p1, cnt⟩, vt⟩
  have mt : t.mem = s.mem.write (s₀.gpr .x1 + BitVec.ofNat 64 (2 * (8 * k))) 16 (s4.v .v0) := by
    rw [ht.mem, h5.mem, h4.mem, mm3]
  have keepv (r : VReg) (r0 : r ≠ .v0) (r1 : r ≠ .v1) (r2 : r ≠ .v2)
      (r3 : r ≠ .v3) (r4 : r ≠ .v4) : t.v r = s.v r := by
    rw [vt, h5.v, h4.get r r0, hv3 r r0 r1 r2 r3 r4, vl]
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, cnt, ?_, ?_, ?_, ?_, ?_⟩, by rw [cnt]; omega⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [ht.gpr r (by simp [hr.1, hr.2.1, hr.2.2.2.2]), h5.gpr, h4.gpr, gp r (by simp [hr.2.2.1, hr.2.2.2.1]),
      h.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2])]
  · rw [ht.rd, h5.rd, h4.rd, rd3, hl.rd, h.rd]
  · rw [ht.wr, h5.wr, h4.wr, wr3, hl.wr, h.wr]
  · rw [ht.sp, h5.sp, h4.sp, sp3, hl.sp, h.sp]
  · rw [p0, h5.gpr, h4.gpr, gp .x0 (by decide), h.x0, show (12 : BitVec 64) = BitVec.ofNat 64 12 from rfl,
      ptr_add]; congr 2
  · rw [p1, h5.gpr, h4.gpr, gp .x1 (by decide), h.x1, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl,
      ptr_add]; congr 2
  · rw [keepv .v16 (by decide) (by decide) (by decide) (by decide) (by decide), h.mask]
  · rw [keepv .v17 (by decide) (by decide) (by decide) (by decide) (by decide), h.bits]
  · rw [keepv .v18 (by decide) (by decide) (by decide) (by decide) (by decide), h.q]
  · rw [mt]
    refine h.out.write16 (by omega) (fun e he => ?_) (fun i _ => by omega)
    apply BitVec.eq_of_toNat_eq
    rw [h4.v, N e he, GW, BitVec.toNat_ofNat]
    have : ((decode12 (Decode12.B s₀))[8 * k + e]!).val < 3329 := Fin.isLt _
    dsimp only
    by_cases c : e < 4
    · rw [ite_eq_left c, Nat.mod_eq_of_lt (by omega)]
    · rw [ite_eq_right c, show 8 * k + 4 + (e - 4) = 8 * k + e by omega, Nat.mod_eq_of_lt (by omega)]
  · rw [mt]; exact h.frame.write (List.mem_singleton_self _) _ (contains_off (by omega) (by decide))

theorem dec_init (s : State) : WP isa (.block (maskVec .v16 [0,1,2,255,3,4,5,255,6,7,8,255,9,10,11,255] ++
    ([.movz .x .x9 4095 0, .vop (.dup .s4 .v17 .x9), .movz .x .x9 3329 0,
      .vop (.dup .s4 .v18 .x9), .movz .x .x11 32 0] : List Instr))) s (DecInv s 0) := by
  dsimp [maskVec, VG.Impl.MlKem.AArch64.movImm]
  rrun [RegUpd.sp_write, RegUpd.sp_setV]
  refine ⟨fun r hr => ?_, rfl, rfl, rfl, ?_, ?_, rfl, ?_, rfl, rfl, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setV, RegUpd.gpr_write, hr.2.2.1, hr.2.2.2.2, ite_false]
  · change s.gpr .x0 = s.gpr .x0 + BitVec.ofNat 64 (12 * 0); exact (BitVec.add_zero _).symm
  · change s.gpr .x1 = s.gpr .x1 + BitVec.ofNat 64 (16 * 0); exact (BitVec.add_zero _).symm
  · rw [decMask_value]; rfl
  · intro i _; rw [ite_eq_right (by omega)]; simp only [RegUpd.mem_write, RegUpd.mem_setV]
  · exact Frame.refl _ _

theorem decW_ok {s : State} (hd : DecData s) :
    WP isa decW s fun s' => Keep decClob s s' ∧ Frame [⟨s.gpr .x1, 512⟩] s.mem s'.mem ∧
      PolyIsW 16 s'.mem (s.gpr .x1) (decode12 (Decode12.B s)) := by
  refine WP.mono (WP.vcs (by decide +kernel) (WP.seq (WP.mono (dec_init s) fun s₁ h₁ =>
    count_loop (by decide) (DecInv s) (fun k hk t ht => dec_step hd hk ht) h₁)))
    fun s' ⟨h', vcs⟩ => ⟨⟨h'.gpr, h'.rd, h'.wr, h'.sp, vcs⟩, h'.frame,
      h'.out.polyIs (fun i hi => by omega) fun i _ => ?_⟩
  have : ((decode12 (Decode12.B s))[i]!).val < 3329 := Fin.isLt _
  rw [GW, BitVec.toNat_ofNat]; omega

end VG.Proof.MlKem.AArch64.Codec12W
