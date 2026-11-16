module

import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.DotReady
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.W.Call
import VerifiedGarbage.Proof.MlKem.AArch64.AddSubW
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
public import VerifiedGarbage.Impl.MlKem.AArch64.Widen16
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
public import VerifiedGarbage.Proof.MlKem.Kpke16Contract
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Mem
import VerifiedGarbage.Proof.MlKem.PolyW
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.Arith
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
public import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.Impl.MlKem.AArch64.Narrow16
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Vec
import VerifiedGarbage.Impl.MlKem.AArch64.Kem16
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TransformTables
public import VerifiedGarbage.Proof.MlKem.AArch64.KemOps
public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Result
public import VerifiedGarbage.Proof.MlKem.AArch64.DotW.Loop
import VerifiedGarbage.Proof.MlKem.AArch64.KemEnc
import VerifiedGarbage.Proof.MlKem.AArch64.DotW
public import VerifiedGarbage.Impl.MlKem.AArch64.Hybrid
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.ReadonlyCalls
public import VerifiedGarbage.Impl.MlKem.AArch64.Ops16

/-! ### `MlKem.AArch64.Codec12W.Dec`, which only this module used -/

section

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
  obtain load : WP isa (.block [.ldr .x .x9 .x0 0, .ldr .w .x10 .x0 8]) s fun t =>
      Only [.x9, .x10] s t ∧ t.gpr .x9 = s.mem.readW (s.gpr .x0) 64 ∧
      t.gpr .x10 = (s.mem.readW (s.gpr .x0 + 8) 32).setWidth 64 := by
    refine wp_ldrx (a := s.gpr .x0) (by decide) (by simp) ?_ fun s1 h1 e1 => ?_
    · rw [h.rd, h.wr, h.x0]; exact hd.read _ _ (by omega_arith)
    refine wp_ldrw (a := s.gpr .x0 + 8) (by decide) (by rw [h1.get .x0]; rfl) ?_ fun s2 h2 e2 => wp_nil ?_
    · rw [h1.rd, h1.wr, h.rd, h.wr, h.x0, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, ptr_add]
      exact hd.read _ _ (by omega_arith)
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
  obtain xb : ∀ j < 12, (vbyte x j).toNat = Decode12.byte s₀ (12 * k + j) := by
    intro j hj
    rw [show x = ofVDwords (s.mem.readW (s.gpr .x0) 64)
      ((s.mem.readW (s.gpr .x0 + 8) 32).setWidth 64) by dsimp only [x]; rw [x9, x10], input_byte _ _ hj,
      h.x0, ptr_add, byte_frame (len := 384) h.frame
        (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd.apart) (by decide) (by omega_arith)]
    show _ = ((Spec.Sha3.bytesAt s₀.mem (s₀.gpr .x0) 384).getD _ 0).toNat
    rw [bytesAt_getD _ _ (by omega_arith)]
  obtain vals : ∀ e < 4, vword (s3.v .v0) e = Decode12.G s₀ (8 * k + e) ∧
      vword (s3.v .v1) e = Decode12.G s₀ (8 * k + 4 + e) := by
    intro e he; rw [v0, v1]; exact decoded_spec s₀ hk xb he
  obtain gv : ∀ i, (Decode12.G s₀ i).toNat = ((decode12 (Decode12.B s₀))[i]!).val := fun i => by
    have : ((decode12 (Decode12.B s₀))[i]!).val < 3329 := Fin.isLt _
    rw [Decode12.G, BitVec.toNat_ofNat]; omega_arith
  obtain N := DotW.narrow_lanes (x := s3.v .v0) (y := s3.v .v1)
    (A := fun e => ((decode12 (Decode12.B s₀))[8 * k + e]!).val)
    (B := fun e => ((decode12 (Decode12.B s₀))[8 * k + 4 + e]!).val)
    (fun e he => by rw [(vals e he).1, gv]) (fun e he => by rw [(vals e he).2, gv])
    (fun e _ => by have : ((decode12 (Decode12.B s₀))[8 * k + e]!).val < 3329 := Fin.isLt _; omega_arith)
    (fun e _ => by have : ((decode12 (Decode12.B s₀))[8 * k + 4 + e]!).val < 3329 := Fin.isLt _; omega_arith)
  have gp (r : Reg) (hr : r ∉ [.x9, .x10]) : s3.gpr r = s.gpr r := by rw [g3, hl.gpr _ hr]
  obtain mm3 : s3.mem = s.mem := m3.trans hl.mem
  refine wp_vop (d := .v0) rfl fun s4 h4 => ?_
  refine wp_strq (a := s₀.gpr .x1 + BitVec.ofNat 64 (2 * (8 * k))) (by decide)
    (by rw [h4.gpr, gp .x1 (by decide), h.x1, BitVec.add_zero]; congr 2; omega_arith) ?_ fun s5 h5 => ?_
  · rw [h4.wr, wr3, hl.wr, h.wr]; exact hd.write _ (by omega_arith)
  obtain scalar : WP isa (.block [.addImm .x .x0 .x0 12, .addImm .x .x1 .x1 16, .subImm .x .x11 .x11 1]) s5
      fun t => Only [.x0, .x1, .x11] s5 t ∧ t.gpr .x0 = s5.gpr .x0 + 12 ∧
        t.gpr .x1 = s5.gpr .x1 + 16 ∧ (t.gpr .x11).toNat = 32 - (k + 1) := by
    refine wp_addImm (by decide) fun s6 h6 e6 => wp_addImm (by decide) fun s7 h7 e7 =>
      wp_subImm (by decide) fun s8 h8 e8 => wp_nil ?_
    refine ⟨((h6.trans h7).trans h8).mono (by decide), ?_, ?_, ?_⟩
    · rw [h8.get .x0, h7.get .x0, e6]; rfl
    · rw [h8.get .x1, e7, h6.get .x1]; rfl
    · have cnt : (s7.gpr .x11).toNat = 32 - k := by
        rw [h7.get .x11, h6.get .x11, h5.gpr, h4.gpr, gp .x11 (by decide), h.count]
      rw [e8, toNat_sub_n (by rw [cnt]; simp; omega_arith), cnt]; simp; omega_arith
  refine WP.mono (WP.keepV (by decide) scalar) ?_
  intro t ⟨⟨ht, p0, p1, cnt⟩, vt⟩
  obtain mt : t.mem = s.mem.write (s₀.gpr .x1 + BitVec.ofNat 64 (2 * (8 * k))) 16 (s4.v .v0) := by
    rw [ht.mem, h5.mem, h4.mem, mm3]
  have keepv (r : VReg) (r0 : r ≠ .v0) (r1 : r ≠ .v1) (r2 : r ≠ .v2)
      (r3 : r ≠ .v3) (r4 : r ≠ .v4) : t.v r = s.v r := by
    rw [vt, h5.v, h4.get r r0, hv3 r r0 r1 r2 r3 r4, vl]
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, cnt, ?_, ?_, ?_, ?_, ?_⟩, by rw [cnt]; omega_arith⟩
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
    refine h.out.write16 (by omega_arith) (fun e he => ?_) (fun i _ => by omega_arith)
    apply BitVec.eq_of_toNat_eq
    rw [h4.v, N e he, GW, BitVec.toNat_ofNat]
    have : ((decode12 (Decode12.B s₀))[8 * k + e]!).val < 3329 := Fin.isLt _
    dsimp only
    by_cases c : e < 4
    · rw [ite_eq_left c, Nat.mod_eq_of_lt (by omega_arith)]
    · rw [ite_eq_right c, show 8 * k + 4 + (e - 4) = 8 * k + e by omega_arith, Nat.mod_eq_of_lt (by omega_arith)]
  · rw [mt]; exact h.frame.write (List.mem_singleton_self _) _ (contains_off (by omega_arith) (by decide))

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
  · intro i _; rw [ite_eq_right (by omega_arith)]; simp only [RegUpd.mem_write, RegUpd.mem_setV]
  · exact Frame.refl _ _

theorem decW_ok {s : State} (hd : DecData s) :
    WP isa decW s fun s' => Keep decClob s s' ∧ Frame [⟨s.gpr .x1, 512⟩] s.mem s'.mem ∧
      PolyIsW 16 s'.mem (s.gpr .x1) (decode12 (Decode12.B s)) := by
  refine WP.mono (WP.vcs (by decide +kernel) (WP.seq (WP.mono (dec_init s) fun s₁ h₁ =>
    count_loop (by decide) (DecInv s) (fun k hk t ht => dec_step hd hk ht) h₁)))
    fun s' ⟨h', vcs⟩ => ⟨⟨h'.gpr, h'.rd, h'.wr, h'.sp, vcs⟩, h'.frame,
      h'.out.polyIs (fun i hi => by omega_arith) fun i _ => ?_⟩
  have : ((decode12 (Decode12.B s))[i]!).val < 3329 := Fin.isLt _
  rw [GW, BitVec.toNat_ofNat]; omega_arith

end VG.Proof.MlKem.AArch64.Codec12W

end

end

/-! ### `MlKem.AArch64.Widen16`, which only this module used -/

section

/-!
# ML-KEM on AArch64: a polynomial from 16-bit to 32-bit coefficients

`widen_ok`: `Impl.MlKem.AArch64.Widen16.widen` stores the polynomial at `x0`, with 16-bit
coefficients, at `x1` with 32-bit ones. Each iteration loads eight coefficients, which `zip1`
and `zip2` with zero (`v29`) widen into two vectors of four (`Ntt16.vword_zip_zero`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Widen16

open VG VG.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Spec.MlKem
open VG.Proof.MlKem.AArch64.Ntt16 (vword_zip_zero)
open VG.Impl.MlKem.AArch64.Widen16 (widenBody widen)

/-- The coefficients `i ∈ S` of the polynomial at `p` are `G i`, the others `old i`. -/
def CoeffsIn (m : Mem) (p : Addr) (S : Nat → Prop) [DecidablePred S] (G old : Nat → BitVec 32) :
    Prop :=
  ∀ i < 256, coeffAt m p i = if S i then G i else old i

/-- Storing four coefficients `t, …, t + 3`. -/
theorem CoeffsIn.write16 {m : Mem} {p : Addr} {S S' : Nat → Prop} [DecidablePred S]
    [DecidablePred S'] {G old : Nat → BitVec 32} (h : CoeffsIn m p S G old) {t : Nat} (ht : t + 4 ≤ 256)
    {x : BitVec 128} (hx : ∀ e < 4, vword x e = G (t + e))
    (hS : ∀ i < 256, (S' i ↔ S i ∨ (t ≤ i ∧ i < t + 4))) :
    CoeffsIn (m.write (coeffAddr p t) 16 x) p S' G old := fun i hi => by
  rw [coeffAt_write16 _ _ ht _ hi, h i hi]
  by_cases c : t ≤ i ∧ i < t + 4
  · rw [ite_eq_left c, ite_eq_left ((hS i hi).2 (Or.inr c)), hx _ (by omega_using [c]),
      show t + (i - t) = i by omega_using [c]]
  · rw [ite_eq_right c]
    by_cases c' : S i
    · rw [ite_eq_left c', ite_eq_left ((hS i hi).2 (Or.inl c'))]
    · rw [ite_eq_right c', ite_eq_right (fun h' => ((hS i hi).1 h').elim c' c)]

/-- The registers `widen` writes. -/
abbrev clob : List Reg := [.x0, .x1, .x10]

/-- What `widen` needs: the polynomial `F` with 16-bit coefficients at `x0`, readable, and 1024
writable bytes at `x1` apart from it. -/
structure WidenData (s₀ : State) (F : Poly) : Prop where
  src : PolyIsW 16 s₀.mem (s₀.gpr .x0) F
  read : ∀ j, j + 16 ≤ 512 → InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x0 + BitVec.ofNat 64 j) 16
  write : ∀ j, j + 16 ≤ 1024 → InRegions s₀.wr (s₀.gpr .x1 + BitVec.ofNat 64 j) 16
  apart : (⟨s₀.gpr .x0, 512⟩ : Region).Disjoint ⟨s₀.gpr .x1, 1024⟩

/-- Coefficient `i` of the output. -/
def G (F : Poly) (i : Nat) : BitVec 32 := BitVec.ofNat 32 (F[i]!).val

/-- After `k` iterations. -/
structure Inv (s₀ : State) (F : Poly) (k : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ clob → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x0 : s.gpr .x0 = s₀.gpr .x0 + BitVec.ofNat 64 (16 * k)
  x1 : s.gpr .x1 = s₀.gpr .x1 + BitVec.ofNat 64 (32 * k)
  count : (s.gpr .x10).toNat = 32 - k
  zero : ∀ e < 8, vhalf (s.v .v29) e = 0
  vcs : ∀ r ∈ VG.AArch64.preservedV, (s.v r).extractLsb' 0 64 = (s₀.v r).extractLsb' 0 64
  out : CoeffsIn s.mem (s₀.gpr .x1) (· < 8 * k) (G F) fun i => coeffAt s₀.mem (s₀.gpr .x1) i
  frame : Frame [⟨s₀.gpr .x1, 1024⟩] s₀.mem s.mem

theorem G_toNat (F : Poly) (i : Nat) : (G F i).toNat = (F[i]!).val := by
  rw [G, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := val_lt F[i]!; omega)]

theorem step {s₀ : State} {F : Poly} (hd : WidenData s₀ F) {k : Nat} (hk : k < 32) {s : State}
    (h : Inv s₀ F k s) :
    WP isa (.block widenBody) s fun t => Inv s₀ F (k + 1) t ∧ ((t.gpr .x10).toNat ≠ 0 ↔ k + 1 ≠ 32) := by
  obtain srcAt : s.gpr .x0 + BitVec.ofNat 64 0 = s₀.gpr .x0 + BitVec.ofNat 64 (2 * (8 * k)) := by
    rw [h.x0, BitVec.add_zero]; congr 2; omega_using []
  refine wp_ldrq (a := s₀.gpr .x0 + BitVec.ofNat 64 (2 * (8 * k))) (by decide) srcAt ?_ fun s1 h1 => ?_
  · rw [h.rd, h.wr]; exact hd.read _ (by omega_using [hk])
  obtain ld : ∀ e < 8, (vhalf (s1.v .v0) e).toNat = (F[8 * k + e]!).val := fun e he => by
    rw [h1.v, vhalf_read_coeff _ _ _ he]
    obtain hf : coeffAtW 16 s.mem (s₀.gpr .x0) (8 * k + e) = coeffAtW 16 s₀.mem (s₀.gpr .x0) (8 * k + e) :=
      coeffAtW16_congr (bytes_frame h.frame (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact hd.apart) (by decide)) (by rw [n_eq]; omega_using [hk, he])
    rw [hf, polyIsW_toNat hd.src (by rw [n_eq]; omega_using [hk, he])]
  obtain z1 : ∀ e < 8, vhalf (s1.v .v29) e = 0 := fun e he => by rw [h1.other _ (by decide)]; exact h.zero e he
  refine wp_vop (d := .v1) rfl fun s2 h2 => ?_
  refine wp_vop (d := .v2) rfl fun s3 h3 => ?_
  obtain w1 : ∀ e < 4, vword (s3.v .v1) e = G F (8 * k + e) := fun e he => BitVec.eq_of_toNat_eq (by
    rw [h3.other _ (by decide), h2.v, G_toNat, (vword_zip_zero z1 he).1]
    exact ld e (by omega_using [he]))
  obtain w2 : ∀ e < 4, vword (s3.v .v2) e = G F (8 * k + 4 + e) := fun e he => BitVec.eq_of_toNat_eq (by
    rw [h3.v, G_toNat, show 8 * k + 4 + e = 8 * k + (4 + e) by omega_using [],
      h2.other .v0 (by decide), h2.other .v29 (by decide), (vword_zip_zero z1 he).2]
    exact ld _ (by omega_using [he]))
  obtain g3 : s3.gpr = s.gpr := by rw [h3.gpr, h2.gpr, h1.gpr]
  obtain dst0 : s3.gpr .x1 + BitVec.ofNat 64 0 = coeffAddr (s₀.gpr .x1) (8 * k) := by
    rw [g3, h.x1, BitVec.add_zero, coeffAddr]; congr 2; omega_using []
  refine wp_strq (a := coeffAddr (s₀.gpr .x1) (8 * k)) (by decide) dst0 ?_ fun s4 h4 => ?_
  · rw [h3.wr, h2.wr, h1.wr, h.wr, coeffAddr]
    exact hd.write _ (by omega_using [hk])
  obtain dst1 : s4.gpr .x1 + BitVec.ofNat 64 16 = coeffAddr (s₀.gpr .x1) (8 * k + 4) := by
    rw [h4.gpr, g3, h.x1, coeffAddr, ptr_add]; congr 2; omega_using []
  refine wp_strq (a := coeffAddr (s₀.gpr .x1) (8 * k + 4)) (by decide) dst1 ?_ fun s5 h5 => ?_
  · rw [h4.wr, h3.wr, h2.wr, h1.wr, h.wr, coeffAddr]
    exact hd.write _ (by omega_using [hk])
  obtain scalar : WP isa (.block [.addImm .x .x0 .x0 16, .addImm .x .x1 .x1 32, .subImm .x .x10 .x10 1]) s5
      fun t => Only [.x0, .x1, .x10] s5 t ∧ t.gpr .x0 = s5.gpr .x0 + 16 ∧
        t.gpr .x1 = s5.gpr .x1 + 32 ∧ (t.gpr .x10).toNat = 32 - (k + 1) := by
    refine wp_addImm (by decide) fun s6 h6 e6 => wp_addImm (by decide) fun s7 h7 e7 =>
      wp_subImm (by decide) fun s8 h8 e8 => wp_nil ?_
    refine ⟨((h6.trans h7).trans h8).mono (by decide), ?_, ?_, ?_⟩
    · rw [h8.get .x0, h7.get .x0, e6]; rfl
    · rw [h8.get .x1, e7, h6.get .x1]; rfl
    · have cnt : (s7.gpr .x10).toNat = 32 - k := by
        rw [h7.get .x10, h6.get .x10, h5.gpr, h4.gpr, g3, h.count]
      rw [e8, toNat_sub_n (by rw [cnt]; simp; omega_using [hk]), cnt]; simp; omega_using []
  refine WP.mono (WP.keepV (by decide) scalar) ?_
  intro t ⟨⟨ht, p0, p1, cnt⟩, vt⟩
  obtain g5 : s5.gpr = s.gpr := by rw [h5.gpr, h4.gpr, g3]
  have vv (r : VReg) (r0 : r ≠ .v0) (r1 : r ≠ .v1) (r2 : r ≠ .v2) : t.v r = s.v r := by
    rw [vt, h5.v, h4.v, h3.other _ r2, h2.other _ r1, h1.other _ r0]
  obtain mt : t.mem = (s.mem.write (coeffAddr (s₀.gpr .x1) (8 * k)) 16 (s3.v .v1)).write
      (coeffAddr (s₀.gpr .x1) (8 * k + 4)) 16 (s3.v .v2) := by
    rw [ht.mem, h5.mem, h4.mem, h4.v, h3.mem, h2.mem, h1.mem]
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, cnt, ?_, fun r hr => ?_, ?_, ?_⟩, by rw [cnt]; omega_using [hk]⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [ht.gpr r (by simp [hr.1, hr.2.1, hr.2.2]), g5, h.gpr r (by simp [hr.1, hr.2.1, hr.2.2])]
  · rw [ht.rd, h5.rd, h4.rd, h3.rd, h2.rd, h1.rd, h.rd]
  · rw [ht.wr, h5.wr, h4.wr, h3.wr, h2.wr, h1.wr, h.wr]
  · rw [ht.sp, h5.sp, h4.sp, h3.sp, h2.sp, h1.sp, h.sp]
  · rw [p0, g5, h.x0, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, ptr_add]; congr 2
  · rw [p1, g5, h.x1, show (32 : BitVec 64) = BitVec.ofNat 64 32 from rfl, ptr_add]; congr 2
  · intro e he; rw [vv .v29 (by decide) (by decide) (by decide)]; exact h.zero e he
  · have hr0 : r ≠ .v0 := by revert r hr; decide
    obtain hr1 : r ≠ .v1 := by revert r hr; decide
    obtain hr2 : r ≠ .v2 := by revert r hr; decide
    rw [vv r hr0 hr1 hr2]; exact h.vcs r hr
  · rw [mt]
    refine (h.out.write16 (S' := fun i => i < 8 * k + 4) (t := 8 * k) (by omega_using [hk]) w1
      (fun i _ => by omega_using [])).write16 (by omega_using [hk]) w2 (fun i _ => by omega_using [])
  · rw [mt]
    obtain c0 := Offset.contains_base (s₀.gpr .x1) (d := 32 * k) (n := 16) (k := 1024) (by omega_using [hk]) (by omega_using [hk])
    obtain c1 := Offset.contains_base (s₀.gpr .x1) (d := 32 * k + 16) (n := 16) (k := 1024) (by omega_using [hk]) (by omega_using [hk])
    refine (h.frame.write (List.mem_singleton_self _) _ ?_).write (List.mem_singleton_self _) _ ?_
    · rw [coeffAddr, show 4 * (8 * k) = 32 * k by omega_using []]; exact c0
    · rw [coeffAddr, show 4 * (8 * k + 4) = 32 * k + 16 by omega_using []]; exact c1

theorem init (s : State) : WP isa (.block [.movz .x .x10 32 0, .vop (.movi0 .v29)]) s fun t =>
    ∀ F, Inv s F 0 t := by
  refine wp_movz fun s1 h1 e1 => wp_vop (d := .v29) rfl fun s2 h2 => wp_nil fun F => ?_
  refine ⟨fun r hr => ?_, by rw [h2.rd, h1.rd], by rw [h2.wr, h1.wr], by rw [h2.sp, h1.sp], ?_, ?_,
    by rw [h2.gpr, e1]; rfl, fun e he => ?_, fun r hr => ?_, fun i _ => ?_, ?_⟩
  · rw [h2.gpr, h1.get r (by simp at hr ⊢; exact hr.2.2)]
  · rw [h2.gpr, h1.get .x0 (by decide)]; exact (BitVec.add_zero _).symm
  · rw [h2.gpr, h1.get .x1 (by decide)]; exact (BitVec.add_zero _).symm
  · rw [h2.v]; simp [vhalf]
  · rw [h2.other _ (by revert r hr; decide)]; exact h1.vcs r hr
  · rw [ite_eq_right (by omega_using []), h2.mem, h1.mem]
  · rw [h2.mem, h1.mem]; exact Frame.refl _ _

theorem widen_ok {s : State} {F : Poly} (hd : WidenData s F) :
    WP isa widen s fun s' => Keep clob s s' ∧ Frame [⟨s.gpr .x1, 1024⟩] s.mem s'.mem ∧
      PolyIs s'.mem (s.gpr .x1) F := by
  refine WP.seq (WP.mono (init s) fun s₁ h₁ =>
    WP.mono (count_loop (by decide) (Inv s F) (fun k hk t ht => step hd hk ht) (h₁ F)) fun s' h' => ?_)
  refine ⟨⟨h'.gpr, h'.rd, h'.wr, h'.sp, h'.vcs⟩, h'.frame, polyIs_of_toNat fun i hi => ?_⟩
  rw [n_eq] at hi
  rw [h'.out i hi, ite_eq_left (by omega), G_toNat]

end VG.Proof.MlKem.AArch64.Widen16

end

end

/-! ### `MlKem.AArch64.Narrow16`, which only this module used -/

section

/-!
# ML-KEM on AArch64: a polynomial from 32-bit to 16-bit coefficients

`narrow_ok`: `Impl.MlKem.AArch64.Narrow16.narrow` stores the polynomial at `x0`, with 32-bit
coefficients, at `x1` with 16-bit ones. Each iteration loads eight coefficients in two vectors,
whose low halfwords `uzp1` takes (`vhalf_perm_h8`), and stores them as one.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Narrow16

open VG VG.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Spec.MlKem
open VG.Proof.MlKem.AArch64.Ntt16 (vhalf_perm_h8 vword_lo)
open VG.Impl.MlKem.AArch64.Narrow16 (narrowBody narrow)

/-- The registers `narrow` writes. -/
abbrev clob : List Reg := [.x0, .x1, .x10]

/-- What `narrow` needs: the polynomial `F` with 32-bit coefficients at `x0`, readable, and 512
writable bytes at `x1` apart from it. -/
structure NarrowData (s₀ : State) (F : Poly) : Prop where
  src : PolyIs s₀.mem (s₀.gpr .x0) F
  read : ∀ j, j + 16 ≤ 1024 → InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x0 + BitVec.ofNat 64 j) 16
  write : ∀ j, j + 16 ≤ 512 → InRegions s₀.wr (s₀.gpr .x1 + BitVec.ofNat 64 j) 16
  apart : (polyRegion (s₀.gpr .x0)).Disjoint ⟨s₀.gpr .x1, 512⟩

/-- Coefficient `i` of the output. -/
def G (F : Poly) (i : Nat) : BitVec 16 := BitVec.ofNat 16 (F[i]!).val

theorem G_toNat (F : Poly) (i : Nat) : (G F i).toNat = (F[i]!).val := by
  rw [G, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := val_lt F[i]!; omega)]

/-- After `k` iterations. -/
structure Inv (s₀ : State) (F : Poly) (k : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ clob → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x0 : s.gpr .x0 = s₀.gpr .x0 + BitVec.ofNat 64 (32 * k)
  x1 : s.gpr .x1 = s₀.gpr .x1 + BitVec.ofNat 64 (16 * k)
  count : (s.gpr .x10).toNat = 32 - k
  vcs : ∀ r ∈ VG.AArch64.preservedV, (s.v r).extractLsb' 0 64 = (s₀.v r).extractLsb' 0 64
  out : CoeffsInW s.mem (s₀.gpr .x1) (· < 8 * k) (G F) fun i => coeffAtW 16 s₀.mem (s₀.gpr .x1) i
  frame : Frame [⟨s₀.gpr .x1, 512⟩] s₀.mem s.mem

theorem step {s₀ : State} {F : Poly} (hd : NarrowData s₀ F) {k : Nat} (hk : k < 32) {s : State}
    (h : Inv s₀ F k s) :
    WP isa (.block narrowBody) s fun t => Inv s₀ F (k + 1) t ∧ ((t.gpr .x10).toNat ≠ 0 ↔ k + 1 ≠ 32) := by
  obtain src := polyIs_frame h.frame (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd.apart) hd.src
  obtain a0 : s.gpr .x0 + BitVec.ofNat 64 0 = coeffAddr (s₀.gpr .x0) (8 * k) := by
    rw [h.x0, BitVec.add_zero, coeffAddr]; congr 2; omega_using []
  refine wp_ldrq (a := coeffAddr (s₀.gpr .x0) (8 * k)) (by decide) a0 ?_ fun s1 h1 => ?_
  · rw [h.rd, h.wr, coeffAddr, show 4 * (8 * k) = 32 * k by omega_using []]; exact hd.read _ (by omega_using [hk])
  obtain a1 : s1.gpr .x0 + BitVec.ofNat 64 16 = coeffAddr (s₀.gpr .x0) (8 * k + 4) := by
    rw [h1.gpr, h.x0, coeffAddr, ptr_add]; congr 2; omega_using []
  refine wp_ldrq (a := coeffAddr (s₀.gpr .x0) (8 * k + 4)) (by decide) a1 ?_ fun s2 h2 => ?_
  · rw [h1.rd, h1.wr, h.rd, h.wr, coeffAddr, show 4 * (8 * k + 4) = 32 * k + 16 by omega_using []]
    exact hd.read _ (by omega_using [hk])
  refine wp_vop (d := .v2) rfl fun s3 h3 => ?_
  obtain key : ∀ (x : BitVec 128) (c e : Nat), (vword x c).toNat = (F[8 * k + e]!).val →
      vhalf x (2 * c) = G F (8 * k + e) := fun x c e hx => BitVec.eq_of_toNat_eq (by
    rw [← vword_lo, BitVec.extractLsb'_toNat, Nat.shiftRight_zero, hx, G_toNat,
      Nat.mod_eq_of_lt (by have := val_lt F[8 * k + e]!; omega_using [this])])
  obtain hv : ∀ e < 8, vhalf (s3.v .v2) e = G F (8 * k + e) := fun e he => by
    rw [h3.v, h2.other .v0 (by decide), h2.v, h1.v, h1.mem, vhalf_perm_h8 _ _ _ he]
    by_cases c : e < 4
    · rw [ite_eq_left c]; exact key _ e e (lanes_load src (j := 8 * k) (by omega_using [hk]) e c)
    · rw [ite_eq_right c, show 2 * e - 8 = 2 * (e - 4) by omega_using []]
      have := lanes_load src (j := 8 * k + 4) (by omega_using [hk]) (e - 4) (by omega_using [he])
      simp only [show 8 * k + 4 + (e - 4) = 8 * k + e by omega_using [c]] at this
      exact key _ _ e this
  obtain g3 : s3.gpr = s.gpr := by rw [h3.gpr, h2.gpr, h1.gpr]
  obtain dst : s3.gpr .x1 + BitVec.ofNat 64 0 = s₀.gpr .x1 + BitVec.ofNat 64 (2 * (8 * k)) := by
    rw [g3, h.x1, BitVec.add_zero]; congr 2; omega_using []
  refine wp_strq (a := s₀.gpr .x1 + BitVec.ofNat 64 (2 * (8 * k))) (by decide) dst ?_ fun s4 h4 => ?_
  · rw [h3.wr, h2.wr, h1.wr, h.wr, show 2 * (8 * k) = 16 * k by omega_using []]
    exact hd.write _ (by omega_using [hk])
  obtain scalar : WP isa (.block [.addImm .x .x0 .x0 32, .addImm .x .x1 .x1 16, .subImm .x .x10 .x10 1]) s4
      fun t => Only [.x0, .x1, .x10] s4 t ∧ t.gpr .x0 = s4.gpr .x0 + 32 ∧
        t.gpr .x1 = s4.gpr .x1 + 16 ∧ (t.gpr .x10).toNat = 32 - (k + 1) := by
    refine wp_addImm (by decide) fun s6 h6 e6 => wp_addImm (by decide) fun s7 h7 e7 =>
      wp_subImm (by decide) fun s8 h8 e8 => wp_nil ?_
    refine ⟨((h6.trans h7).trans h8).mono (by decide), ?_, ?_, ?_⟩
    · rw [h8.get .x0, h7.get .x0, e6]; rfl
    · rw [h8.get .x1, e7, h6.get .x1]; rfl
    · have cnt : (s7.gpr .x10).toNat = 32 - k := by
        rw [h7.get .x10, h6.get .x10, h4.gpr, g3, h.count]
      rw [e8, toNat_sub_n (by rw [cnt]; simp; omega_using [hk]), cnt]; simp; omega_using []
  refine WP.mono (WP.keepV (by decide) scalar) ?_
  intro t ⟨⟨ht, p0, p1, cnt⟩, vt⟩
  obtain g4 : s4.gpr = s.gpr := by rw [h4.gpr, g3]
  have vv (r : VReg) (r0 : r ≠ .v0) (r1 : r ≠ .v1) (r2 : r ≠ .v2) : t.v r = s.v r := by
    rw [vt, h4.v, h3.other _ r2, h2.other _ r1, h1.other _ r0]
  obtain mt : t.mem = s.mem.write (s₀.gpr .x1 + BitVec.ofNat 64 (2 * (8 * k))) 16 (s3.v .v2) := by
    rw [ht.mem, h4.mem, h3.mem, h2.mem, h1.mem]
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, cnt, fun r hr => ?_, ?_, ?_⟩, by rw [cnt]; omega_using [hk]⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [ht.gpr r (by simp [hr.1, hr.2.1, hr.2.2]), g4, h.gpr r (by simp [hr.1, hr.2.1, hr.2.2])]
  · rw [ht.rd, h4.rd, h3.rd, h2.rd, h1.rd, h.rd]
  · rw [ht.wr, h4.wr, h3.wr, h2.wr, h1.wr, h.wr]
  · rw [ht.sp, h4.sp, h3.sp, h2.sp, h1.sp, h.sp]
  · rw [p0, g4, h.x0, show (32 : BitVec 64) = BitVec.ofNat 64 32 from rfl, ptr_add]; congr 2
  · rw [p1, g4, h.x1, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, ptr_add]; congr 2
  · have hr0 : r ≠ .v0 := by revert r hr; decide
    obtain hr1 : r ≠ .v1 := by revert r hr; decide
    obtain hr2 : r ≠ .v2 := by revert r hr; decide
    rw [vv r hr0 hr1 hr2]; exact h.vcs r hr
  · rw [mt]
    exact h.out.write16 (by omega_using [hk]) hv (fun i _ => by omega_using [])
  · rw [mt]
    refine h.frame.write (List.mem_singleton_self _) _ ?_
    rw [show 2 * (8 * k) = 16 * k by omega_using []]
    exact Offset.contains_base (s₀.gpr .x1) (d := 16 * k) (n := 16) (k := 512) (by omega_using [hk]) (by omega_using [hk])

theorem init (s : State) : WP isa (.block [.movz .x .x10 32 0]) s fun t => ∀ F, Inv s F 0 t := by
  refine wp_movz fun s1 h1 e1 => wp_nil fun F => ?_
  refine ⟨fun r hr => ?_, h1.rd, h1.wr, h1.sp, ?_, ?_, by rw [e1]; rfl, fun r hr => h1.vcs r hr,
    fun i _ => ?_, ?_⟩
  · rw [h1.get r (by simp at hr ⊢; exact hr.2.2)]
  · rw [h1.get .x0 (by decide)]; exact (BitVec.add_zero _).symm
  · rw [h1.get .x1 (by decide)]; exact (BitVec.add_zero _).symm
  · rw [ite_eq_right (by omega_using []), h1.mem]
  · rw [h1.mem]; exact Frame.refl _ _

theorem narrow_ok {s : State} {F : Poly} (hd : NarrowData s F) :
    WP isa narrow s fun s' => Keep clob s s' ∧ Frame [⟨s.gpr .x1, 512⟩] s.mem s'.mem ∧
      PolyIsW 16 s'.mem (s.gpr .x1) F := by
  refine WP.seq (WP.mono (init s) fun s₁ h₁ =>
    WP.mono (count_loop (by decide) (Inv s F) (fun k hk t ht => step hd hk ht) (h₁ F)) fun s' h' => ?_)
  exact ⟨⟨h'.gpr, h'.rd, h'.wr, h'.sp, h'.vcs⟩, h'.frame,
    h'.out.polyIs (fun i hi => by omega_using [hi]) fun i _ => G_toNat F i⟩

end VG.Proof.MlKem.AArch64.Narrow16

end

end


/-! # The building blocks of the 16-bit `encaps` and `decaps`

As `KemOps.lean`, for the blocks of `Impl.MlKem.AArch64.Kem16` on polynomials
stored with 16 bits in the first half of a buffer of `scratch`: the fused dot
product (`fusedW_ok`), the transforms (`nttW_ok`, `invW_ok`), the sum (`addW_read_ok`),
the widening (`widenW_ok`), the narrowing (`narrowW_ok`) and `ByteDecode₁₂` (`dec12W_ok`). Each keeps `KB` and
`x24` and changes only its whole 1024-byte buffers. -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Kem

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.AArch64.DotW (half_sub)

variable {P : KemLay} {L : Layout}

theorem fusedW_ok {s₀ s : State} (hp : Pre P L s₀) {off : Nat} (ho : PO P off)
    (hk : KB P L s₀ s) (terms : List (Nat × Nat)) {F G : (Nat × Nat) → Poly}
    (hd : DotW.LoopDataW s .x28 .x28 (s.gpr .x28+BitVec.ofNat 64 off) (s.syms "VG_MLKEM_GAMMA") terms
      (Dot.polyValues F) (Dot.polyValues G) Dot.gammaValues) :
    WP isa (Kem16.dotAt off terms) s fun t =>
      KB P L s₀ t ∧ Frame [R (kA s₀) L.sc off 1024] s.mem t.mem ∧
      PolyIsW 16 t.mem (sA L s₀ off) (Dot.polySum terms F G) ∧ t.gpr .x24 = s.gpr .x24 := by
  have hw := hp.wf
  have hoff := ho.le
  refine WP.mono (DotW.dotW_ok (by decide) (by kom) terms hd) fun t ⟨kt,ft,pt⟩ => ?_
  rw [e28 hk] at ft pt
  obtain ft' : Frame [R (kA s₀) L.sc off 1024] s.mem t.mem :=
    ft.sub fun r hr => ⟨_, List.mem_singleton_self _, by rw [List.mem_singleton.mp hr]; exact half_sub _⟩
  exact ⟨hk.frame kt ft' (by decide) (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ho.safe hp),ft',pt,kt.get .x24 (by decide)⟩

theorem nttW_ok {s₀ s : State} (hp : Pre P L s₀) {off : Nat} (ho : PO P off)
    (hk : KB P L s₀ s) {F : Poly} (pf : PolyIsW 16 s.mem (sA L s₀ off) F) (ht : Optimized.TransformTables s) :
    WP isa (Ntt16.Readonly.nttAtWithW off NS) s fun t =>
      KB P L s₀ t ∧ Frame [R (kA s₀) L.sc off 1024,R (kA s₀) L.sc NS 1024] s.mem t.mem ∧
      PolyIsW 16 t.mem (sA L s₀ off) (ntt F) ∧ t.gpr .x24 = s.gpr .x24 := by
  have hw := hp.wf
  obtain hc := covers_cons (cov_s hp hk ho.le) (cov_s hp hk (o:=NS) (l:=1024) (by kom))
  obtain hc' := covers_cons (cov_s hp hk (o:=off) (l:=512) (by have := ho.le; omega_using [this]))
    (cov_s hp hk (o:=NS) (l:=512) (by kom))
  refine WP.mono (Ntt16.W.nttAtWithW_ok (by obtain ⟨_,hh⟩:=ho; kom) (by decide)
    (by rw [e28 hk]) (by rw [e28 hk]) (((ho.ns hp).sub_left (half_sub _)).sub_right (half_sub _))
    pf hc' (ht.fast.ready hc)) fun t ⟨kt,pt⟩ => ?_
  obtain kt' : Kept [R (kA s₀) L.sc off 1024,R (kA s₀) L.sc NS 1024] s t := kt.sub fun r hh => by
    rcases mem2' hh with rfl|rfl
    · exact ⟨_, List.mem_cons_self .., half_sub _⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), half_sub _⟩
  refine ⟨hk.call kt' ?_,kt'.frame,pt,kt.cs _ (by decide) (by decide)⟩
  intro r hh
  rcases mem2' hh with rfl|rfl
  · exact ho.safe hp
  · exact safe_scr hp (by kom)

theorem invW_ok {s₀ s : State} (hp : Pre P L s₀) {off : Nat} (ho : PO P off)
    (hk : KB P L s₀ s) (hr : ReducedW 16 s.mem (sA L s₀ off)) (ht : Optimized.TransformTables s) :
    WP isa (Ntt16.Readonly.nttInvAtWithW off NS) s fun t =>
      KB P L s₀ t ∧ Frame [R (kA s₀) L.sc off 1024,R (kA s₀) L.sc NS 1024] s.mem t.mem ∧
      PolyIsW 16 t.mem (sA L s₀ off) (nttInv (polyAtW 16 s.mem (sA L s₀ off))) ∧
      t.gpr .x24 = s.gpr .x24 := by
  have hw := hp.wf
  obtain hc := covers_cons (cov_s hp hk ho.le) (cov_s hp hk (o:=NS) (l:=1024) (by kom))
  obtain hc' := covers_cons (cov_s hp hk (o:=off) (l:=512) (by have := ho.le; omega_using [this]))
    (cov_s hp hk (o:=NS) (l:=512) (by kom))
  refine WP.mono (Ntt16.W.nttInvAtWithW_ok (by obtain ⟨_,hh⟩:=ho; kom) (by decide)
    (by rw [e28 hk]) (by rw [e28 hk]) (((ho.ns hp).sub_left (half_sub _)).sub_right (half_sub _))
    ⟨hr,rfl⟩ hc' (ht.inverse.ready hc)) fun t ⟨kt,pt⟩ => ?_
  obtain kt' : Kept [R (kA s₀) L.sc off 1024,R (kA s₀) L.sc NS 1024] s t := kt.sub fun r hh => by
    rcases mem2' hh with rfl|rfl
    · exact ⟨_, List.mem_cons_self .., half_sub _⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), half_sub _⟩
  refine ⟨hk.call kt' ?_,kt'.frame,pt,kt.cs _ (by decide) (by decide)⟩
  intro r hh
  rcases mem2' hh with rfl|rfl
  · exact ho.safe hp
  · exact safe_scr hp (by kom)

theorem addW_read_ok {s₀ : State} (hp : Pre P L s₀) {f g : Nat} (hf : PO P f) (hg : g+1024 ≤ P.scl)
    (d : f + 1024 ≤ g ∨ g + 1024 ≤ f) {s : State} (hk : KB P L s₀ s)
    (rf : ReducedW 16 s.mem (sA L s₀ f)) (rg : ReducedW 16 s.mem (sA L s₀ g)) :
    WP isa (Kem16.addWAt f g) s fun s' => KB P L s₀ s' ∧ Frame [R (kA s₀) L.sc f 1024] s.mem s'.mem ∧
      PolyIsW 16 s'.mem (sA L s₀ f) (add (polyAtW 16 s.mem (sA L s₀ f)) (polyAtW 16 s.mem (sA L s₀ g))) ∧
      s'.gpr .x24 = s.gpr .x24 := by
  have ff := hf.le
  obtain fg : g+1024 ≤ L.len L.sc := by rw [hp.scl]; exact hg
  refine WP.seq (wp_ptrTo (by decide) (by kom) fun s₁ h₁ e₁ => wp_ptrTo' (by decide) (by kom)
    fun s₂ h₂ e₂ => ?_)
  obtain kb₂ := hk.block (h₁.trans h₂).keep (by rw [h₂.mem, h₁.mem]) (by decide)
  obtain m₂ : s₂.mem = s.mem := by rw [h₂.mem, h₁.mem]
  obtain x0 : s₂.gpr .x0 = sA L s₀ f := by rw [h₂.get .x0, e₁, e28 hk]
  obtain x1 : s₂.gpr .x1 = sA L s₀ g := by rw [e₂, h₁.get .x28, e28 hk]
  obtain cw := cov_s hp kb₂ ff
  obtain cr := cov_r hp kb₂ hp.scb fg
  refine WP.mono (AddSubW.addW_ok ⟨fun j hj => ?_, fun j hj => ?_, ?_, ?_, ?_⟩) fun s₃ ⟨k₃,f₃,p₃⟩ => ?_
  · rw [x0]; exact cw _ _ (in_regions (List.mem_singleton_self _) (contains_off (by omega_using [hj]) (by decide)))
  · rw [x1]; exact cr _ _ (in_regions (List.mem_singleton_self _) (contains_off (by omega_using [hj]) (by decide)))
  · rw [x0, x1]
    exact ((hp.args.rdisj hp.scb hp.scb (hp.fs ff) fg (.inl rfl) (.inr d)).sub_left (half_sub _)).sub_right
      (half_sub _)
  · rw [x0, m₂]; exact rf
  · rw [x1, m₂]; exact rg
  rw [x0, x1, m₂] at p₃
  rw [x0] at f₃
  obtain f₃' : Frame [R (kA s₀) L.sc f 1024] s₂.mem s₃.mem :=
    f₃.sub fun r hr => ⟨_, List.mem_singleton_self _, by rw [List.mem_singleton.mp hr]; exact half_sub _⟩
  refine ⟨kb₂.frame k₃ f₃' (by decide) fun r hr => by rw [List.mem_singleton.mp hr]; exact hf.safe hp,
    by rw [← m₂]; exact f₃', p₃, by rw [k₃.get .x24 (by decide), h₂.get .x24, h₁.get .x24]⟩

theorem widenW_ok {s₀ : State} (hp : Pre P L s₀) {f g : Nat} (hf : PO P f) (hg : PO P g)
    (d : f + 1024 ≤ g ∨ g + 1024 ≤ f) {s : State} (hk : KB P L s₀ s) {F : Poly}
    (pf : PolyIsW 16 s.mem (sA L s₀ f) F) :
    WP isa (Kem16.widenAt f g) s fun s' => KB P L s₀ s' ∧ Frame [R (kA s₀) L.sc g 1024] s.mem s'.mem ∧
      PolyIs s'.mem (sA L s₀ g) F ∧ s'.gpr .x24 = s.gpr .x24 := by
  have ff := hf.le
  have fg := hg.le
  refine WP.seq (wp_ptrTo (by decide) (by kom) fun s₁ h₁ e₁ => wp_ptrTo' (by decide) (by kom)
    fun s₂ h₂ e₂ => ?_)
  obtain kb₂ := hk.block (h₁.trans h₂).keep (by rw [h₂.mem, h₁.mem]) (by decide)
  obtain m₂ : s₂.mem = s.mem := by rw [h₂.mem, h₁.mem]
  obtain x0 : s₂.gpr .x0 = sA L s₀ f := by rw [h₂.get .x0, e₁, e28 hk]
  obtain x1 : s₂.gpr .x1 = sA L s₀ g := by rw [e₂, h₁.get .x28, e28 hk]
  obtain cw := cov_s hp kb₂ fg
  obtain cr := cov_sr hp kb₂ ff
  refine WP.mono (Widen16.widen_ok (F := F) ⟨?_, fun j hj => ?_, fun j hj => ?_, ?_⟩) fun s₃ ⟨k₃,f₃,p₃⟩ => ?_
  · rw [x0, m₂]; exact pf
  · rw [x0]; exact cr _ _ (in_regions (List.mem_singleton_self _) (contains_off (by omega_using [hj]) (by decide)))
  · rw [x1]; exact cw _ _ (in_regions (List.mem_singleton_self _) (contains_off (by omega_using [hj]) (by decide)))
  · rw [x0, x1]; exact (papart hp hf hg d).sub_left (half_sub _)
  rw [x1] at f₃ p₃
  refine ⟨kb₂.frame k₃ f₃ (by decide) fun r hr => by rw [List.mem_singleton.mp hr]; exact hg.safe hp,
    by rw [← m₂]; exact f₃, p₃, by rw [k₃.get .x24 (by decide), h₂.get .x24, h₁.get .x24]⟩

theorem narrowW_ok {s₀ : State} (hp : Pre P L s₀) {f g : Nat} (hf : PO P f) (hg : PO P g)
    (d : f + 1024 ≤ g ∨ g + 1024 ≤ f) {s : State} (hk : KB P L s₀ s) {F : Poly}
    (pf : PolyIs s.mem (sA L s₀ f) F) :
    WP isa (Kem16.narrowAt f g) s fun s' => KB P L s₀ s' ∧ Frame [R (kA s₀) L.sc g 1024] s.mem s'.mem ∧
      PolyIsW 16 s'.mem (sA L s₀ g) F ∧ s'.gpr .x24 = s.gpr .x24 := by
  have ff := hf.le
  have fg := hg.le
  refine WP.seq (wp_ptrTo (by decide) (by kom) fun s₁ h₁ e₁ => wp_ptrTo' (by decide) (by kom)
    fun s₂ h₂ e₂ => ?_)
  obtain kb₂ := hk.block (h₁.trans h₂).keep (by rw [h₂.mem, h₁.mem]) (by decide)
  obtain m₂ : s₂.mem = s.mem := by rw [h₂.mem, h₁.mem]
  obtain x0 : s₂.gpr .x0 = sA L s₀ f := by rw [h₂.get .x0, e₁, e28 hk]
  obtain x1 : s₂.gpr .x1 = sA L s₀ g := by rw [e₂, h₁.get .x28, e28 hk]
  obtain cw := cov_s hp kb₂ fg
  obtain cr := cov_sr hp kb₂ ff
  refine WP.mono (Narrow16.narrow_ok (F := F) ⟨?_, fun j hj => ?_, fun j hj => ?_, ?_⟩) fun s₃ ⟨k₃,f₃,p₃⟩ => ?_
  · rw [x0, m₂]; exact pf
  · rw [x0]; exact cr _ _ (in_regions (List.mem_singleton_self _) (contains_off (by omega_using [hj]) (by decide)))
  · rw [x1]; exact cw _ _ (in_regions (List.mem_singleton_self _) (contains_off (by omega_using [hj]) (by decide)))
  · rw [x0, x1]; exact (papart hp hf hg d).sub_right (half_sub _)
  rw [x1] at f₃ p₃
  obtain f₃' : Frame [R (kA s₀) L.sc g 1024] s₂.mem s₃.mem :=
    f₃.sub fun r hr => ⟨_, List.mem_singleton_self _, by rw [List.mem_singleton.mp hr]; exact half_sub _⟩
  refine ⟨kb₂.frame k₃ f₃' (by decide) fun r hr => by rw [List.mem_singleton.mp hr]; exact hg.safe hp,
    by rw [← m₂]; exact f₃', p₃, by rw [k₃.get .x24 (by decide), h₂.get .x24, h₁.get .x24]⟩

theorem dec12W_ok {s₀ : State} (hp : Pre P L s₀) {k o off : Nat} (hk4 : k < 4)
    (f : o + 384 ≤ L.len (L.slot k)) (ho : PO P off) (hs : L.slot k ≠ L.sc ∨ o + 384 ≤ off ∨ off + 1024 ≤ o)
    {s : State} (hk : KB P L s₀ s) :
    WP isa (Kem16.dec12WAt (slotReg k) o off) s fun s' =>
      KB P L s₀ s' ∧ Frame [R (kA s₀) L.sc off 1024] s.mem s'.mem ∧
      PolyIsW 16 s'.mem (sA L s₀ off) (decode12 (bytesAt s.mem (kA s₀ (L.slot k) + BitVec.ofNat 64 o) 384)) ∧
      s'.gpr .x24 = s.gpr .x24 := by
  have fo := ho.le
  obtain hb := hp.lt hk4
  refine WP.seq (wp_ptrTo (slot_ne hk4 .x0 (by decide)) (slot_off hp hk4 f) fun s₁ h₁ e₁ =>
    wp_ptrTo' (by decide) (by obtain ⟨-, h⟩ := ho; kom) fun s₂ h₂ e₂ => ?_)
  obtain kb₂ := hk.block (h₁.trans h₂).keep (by rw [h₂.mem, h₁.mem]) (by decide)
  obtain m₂ : s₂.mem = s.mem := by rw [h₂.mem, h₁.mem]
  obtain x0 : s₂.gpr .x0 = kA s₀ (L.slot k) + BitVec.ofNat 64 o := by rw [h₂.get .x0, e₁, hk.ptr k hk4]
  obtain x1 : s₂.gpr .x1 = sA L s₀ off := by rw [e₂, h₁.get .x28, e28 hk]
  obtain cw := cov_s hp kb₂ fo
  obtain cr := cov_r hp kb₂ hb f
  refine WP.mono (Codec12W.decW_ok ⟨fun j n hj => ?_, fun j hj => ?_, ?_⟩) fun s₃ ⟨k₃,f₃,p₃⟩ => ?_
  · rw [x0]; exact cr _ _ (in_regions (List.mem_singleton_self _) (contains_off (by omega_using [hj]) (by decide)))
  · rw [x1]; exact cw _ _ (in_regions (List.mem_singleton_self _) (contains_off (by omega_using [hj]) (by decide)))
  · rw [x0, x1]
    exact (hp.args.rdisj hb hp.scb f (hp.fs fo) (.inr (.inr hp.scw)) hs).sub_right (half_sub _)
  rw [x1] at f₃ p₃
  rw [Decode12.B, Decode12.bP, x0, m₂] at p₃
  obtain f₃' : Frame [R (kA s₀) L.sc off 1024] s₂.mem s₃.mem :=
    f₃.sub fun r hr => ⟨_, List.mem_singleton_self _, by rw [List.mem_singleton.mp hr]; exact half_sub _⟩
  refine ⟨kb₂.frame k₃ f₃' (by decide) fun r hr => by rw [List.mem_singleton.mp hr]; exact ho.safe hp,
    by rw [← m₂]; exact f₃', p₃, by rw [k₃.get .x24 (by decide), h₂.get .x24, h₁.get .x24]⟩

end VG.Proof.MlKem.AArch64.Kem
