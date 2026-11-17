module

public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.PrfUsing
public import VerifiedGarbage.Impl.MlKem.AArch64.Kem16
public import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.DotReady
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TransformTables
import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Layout
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.DotSpec
public import VerifiedGarbage.Proof.MlKem.AArch64.KemEnc
public import VerifiedGarbage.Impl.MlKem.AArch64.NoiseWith
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.ReadonlyCalls
public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Table
public import VerifiedGarbage.Impl.MlKem.AArch64.Noise
public import VerifiedGarbage.Proof.MlKem.AArch64.Lay
import VerifiedGarbage.Proof.MlKem.AArch64.KemCommon
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.W.Call
import VerifiedGarbage.Proof.MlKem.AArch64.AddSubW
public import VerifiedGarbage.Proof.MlKem.AArch64.Coeff16
public import VerifiedGarbage.Impl.MlKem.AArch64.Codec12W
public import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.DecBase
public import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.DecLanes
import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.DecLoop
public import VerifiedGarbage.Proof.MlKem.AArch64.DotW.Loop
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
public import VerifiedGarbage.Proof.MlKem.AArch64.KemOps
public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Result
import VerifiedGarbage.Proof.MlKem.AArch64.DotW
public import VerifiedGarbage.Impl.MlKem.AArch64.Hybrid
public import VerifiedGarbage.Impl.MlKem.AArch64.Ops16
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
public import Init.Data.List.Basic
public import VerifiedGarbage.Impl.MlKem.AArch64.Kem
public import VerifiedGarbage.Proof.MlKem.KPke
public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Field

/-! ### `MlKem.AArch64.Optimized.Lists`, which this module and modules that import it used -/

section

/-! # Symbol preservation through lists of sequential operations -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.WPs
open VG VG.AArch64

theorem mono_syms : ∀{cs : List (Prog isa)} {s : State} {Q R : State → Prop},
    WPs cs s Q → (∀t, Q t → t.syms=s.syms → R t) → WPs cs s R
  | [],s,_,_,h,k => k s h rfl
  | _::_,_,_,_,h,k => WP.mono_syms h fun _ ht hs =>
      mono_syms ht (fun u hu hu' => k u hu (hu'.trans hs))

end VG.Proof.MlKem.AArch64.WPs

end

end

/-! ### `MlKem.AArch64.Optimized.KemReady`, which this module and modules that import it used -/

section

/-! # The terms of the fused dot product of `ŝ` and `û'` and their sum -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Kem
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
variable {P : KemLay} {L : Layout}

def decodedTerms (P : KemLay) : List (Nat × Nat) :=
  (List.range P.k).map fun j => (aOff P 0 j,yOff P j)

def decodedF (T : Nat → Poly) (fg : Nat × Nat) : Poly := T ((fg.1-AH)/1024)
def decodedG (P : KemLay) (Y : Nat → Poly) (fg : Nat × Nat) : Poly := Y ((fg.2-YH P)/1024)

theorem decoded_sum (T Y : Nat → Poly) :
    Dot.polySum (decodedTerms P) (decodedF T) (decodedG P Y)=KPke.dotK T Y P.k := by
  apply Optimized.polySum_dotK
  · intro j hj; simp [decodedF,aOff]
  · intro j hj; simp [decodedG,yOff]

end VG.Proof.MlKem.AArch64.Kem

end

end

/-! ### `MlKem.AArch64.Optimized.KemVDecode`, which this module and modules that import it used -/

section

/-! ### `MlKem.AArch64.Optimized.KemVInv`, which this module and modules that import it used -/

section

/-! # Encryption after the consumed matrix may be reused for decoded keys -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Kem
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
variable {P : KemLay} {L : Layout}

/-- A region apart from what `VInv` describes. -/
def VFar (P : KemLay) (L : Layout) (s₀ : State) (kC co nY nU : Nat) (r : Region) : Prop :=
  (R (kA s₀) L.sc RB 32).Disjoint r ∧ (R (kA s₀) L.sc MB 32).Disjoint r ∧
    (R (kA s₀) L.sc (YH P) (1024 * nY)).Disjoint r ∧
    (R (kA s₀) (L.slot kC) co (32 * P.du * nU)).Disjoint r ∧ ∃ r' ∈ encW P L s₀ kC co, Region.Sub r r'

theorem Far.vfar {s₀ : State} {kC co nY nU : Nat} {r : Region}
    (h : Far P L s₀ kC co nY nU r) : VFar P L s₀ kC co nY nU r :=
  ⟨h.1,h.2.1,h.2.2.2⟩

end VG.Proof.MlKem.AArch64.Kem

end

end

/-! # Decode the public vector after the matrix has been consumed -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Kem
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
variable {P : KemLay} {L : Layout}

theorem firstRow_vfar {s₀ : State} (hp : Pre P L s₀) {kE eo kC co : Nat}
    (A : EncArgs P L kE eo kC co) :
    VFar P L s₀ kC co P.k P.k (R (kA s₀) L.sc AH (1024*P.k)) := by
  have hw := hp.wf
  have hkk := Nat.mul_le_mul_right P.k hw.facts.1
  simp only [Nat.one_mul] at hkk
  have fit : AH+1024*P.k≤SV P+48 := by lom
  refine ⟨sdisj hp (by lom) fit (.inl (by lom)),sdisj hp (by lom) fit (.inl (by lom)),
    sdisj hp (by lom) fit (.inr (by lom)),?_,?_⟩
  · have fc : co+32*P.du*P.k≤L.len (L.slot kC) := by
      have := A.fC; have := Nat.mul_assoc 32 P.du P.k; lom
    refine hp.args.rdisj (hp.lt A.hkC) hp.scb fc (hp.fs fit) (.inr (.inr hp.scw)) ?_
    rcases A.sC with hh | hh
    · exact .inl hh
    · exact .inr (.inr (by rw [hh]; lom))
  · exact ⟨R (kA s₀) L.sc PB (SV P-PB),by simp [encW],R.sub2 (by lom) (by lom)⟩

end VG.Proof.MlKem.AArch64.Kem

end

end

/-! ### `MlKem.AArch64.Kem16.URow`, which this module and modules that import it used -/

section

/-! ### `MlKem.AArch64.Kem16.Ops`, which this module and modules that import it used -/

section

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

end

end

/-! ### `MlKem.AArch64.Optimized.KemTransformFrames`, which this module and modules that import it used -/

section

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Kem
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open Optimized
variable {P : KemLay} {L : Layout}

theorem transform_enc_far {s₀ s : State} (hp : Pre P L s₀) {kE eo kC co : Nat}
    (A : EncArgs P L kE eo kC co) (hk : KB P L s₀ s) (ht : TransformTables s) :
    ∀r∈encW P L s₀ kC co,
      (Region.mk (s.syms "VG_MLKEM_NTT16_ZETAS") 512).Disjoint r ∧
      (NttR.fastInvRegion s).Disjoint r ∧ (NttR.fastRegion s).Disjoint r := by
  have hw := hp.wf
  have cover {o n : Nat} (h : o+n≤SV P+48) : Covers [R (kA s₀) L.sc o n] s.wr :=
    cov_w hp hk ⟨hp.scw,hp.scb⟩ (hp.fs h)
  have far {r : Region} (hc : Covers [r] s.wr) :=
    And.intro (ht.forward.apart hc) (And.intro (ht.inverse.apart hc) (ht.fast.apart hc))
  intro r hr
  simp only [encW,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl
  · exact far (cover (by lom))
  · exact far (cover (by lom))
  · exact far (cover (by lom))
  · simpa only [hk.sp] using And.intro ht.forwardStack (And.intro ht.inverseStack ht.fastStack)
  · exact far (cov_w hp hk ⟨A.wC,hp.slots _ A.hkC⟩ A.fC)

theorem transform_enc_frame {s₀ s t : State} (hp : Pre P L s₀) {kE eo kC co : Nat}
    (A : EncArgs P L kE eo kC co) (hk : KB P L s₀ s) (hk' : KB P L s₀ t)
    (ht : TransformTables s) (hs : t.syms=s.syms)
    (hf : Frame (encW P L s₀ kC co) s.mem t.mem) : TransformTables t :=
  ht.frameFar hs (hk'.rd.trans hk.rd.symm) (hk'.wr.trans hk.wr.symm)
    (hk'.sp.trans hk.sp.symm) hf (transform_enc_far hp A hk ht)
end VG.Proof.MlKem.AArch64.Kem

end

end

/-! ### `MlKem.AArch64.Optimized.KemURow`, which this module and modules that import it used -/

section

/-! # One fused ciphertext row using retained noise -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Kem
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Impl.MlKem.AArch64.Noise (noiseOff)
variable {P : KemLay} {L : Layout}

def uTerms (P : KemLay) (i : Nat) : List (Nat × Nat) :=
  (List.range P.k).map fun j => (aOff P j i,yOff P j)

end VG.Proof.MlKem.AArch64.Kem

end

end

/-! ### `MlKem.AArch64.Optimized.KemUContext`, which this module and modules that import it used -/

section

/-! # Readonly data and retained errors survive ciphertext rows -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Kem
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Impl.MlKem.AArch64.Noise (noiseOff)
variable {P : KemLay} {L : Layout}

theorem encW_noise_far {s₀ : State} (hp : Pre P L s₀) (hr : Noise.Room P)
    {kE eo kC co : Nat} (A : EncArgs P L kE eo kC co) {j : Nat} (hj : j<P.k) :
    ∀r∈encW P L s₀ kC co, (polyRegion (sA L s₀ (noiseOff P j))).Disjoint r := by
  have hw := hp.wf
  have hn := Noise.noise_past_kem hr j
  have fits : noiseOff P j+1024≤L.len L.sc := by rw [hp.scl]; exact Noise.noise_fits hr hj
  intro r hh
  rcases mem5 hh with rfl | rfl | rfl | rfl | rfl
  · exact hp.args.rdisj hp.scb hp.scb fits (hp.fs (by lom)) (.inl rfl) (.inr (.inr (by lom)))
  · exact hp.args.rdisj hp.scb hp.scb fits (hp.fs (by lom)) (.inl rfl) (.inr (.inr (by lom)))
  · exact hp.args.rdisj hp.scb hp.scb fits (hp.fs (by lom)) (.inl rfl) (.inr (.inr (by lom)))
  · exact below_R hp hp.scb fits
  · apply hp.args.rdisj hp.scb (hp.lt A.hkC) fits A.fC (.inr (.inl hp.scw))
    rcases A.sC with hc | hc
    · exact .inl (Ne.symm hc)
    · have bound := hp.scl
      have hcfit := A.fC
      have hct : CB P+P.ctLen≤SV P := by lom
      exact .inr (.inr (by rw [hc]; omega_using [hn, hct]))

theorem gamma_frame {m m' : Mem} {p : Addr} {W : List Region}
    (h : Dot.GammaArtifact m p) (hf : Frame W m m')
    (hd : ∀r∈W, (⟨p,512⟩ : Region).Disjoint r) : Dot.GammaArtifact m' p := by
  intro j hj
  rw [←h j hj]
  exact hf.readW (r := ⟨p,512⟩) (contains_off (by omega_using [hj]) (by decide)) hd (by decide)

end VG.Proof.MlKem.AArch64.Kem

end

end

/-! ### `MlKem.AArch64.Kem16.Noise`, which this module and modules that import it used -/

section

/-! # The 16-bit encryption noise

The noise of the 16-bit encryption, stored with 16 bits:
`ŷ` into `YH`, and `e₁` and `e₂` past the KEM's buffers (`ErrorsW`). -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Kem
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
variable {P : KemLay} {L : Layout}

/-- `e₁` and `e₂`, stored with 16 bits past the KEM's buffers. -/
def ErrorsW (P : KemLay) (L : Layout) (s₀ : State) (rv : List Byte) (s : State) : Prop :=
  ∀j<P.k, PolyIsW 16 s.mem (sA L s₀ (Impl.MlKem.AArch64.Noise.noiseOff P j)) (cbd rv (P.k+j))

end VG.Proof.MlKem.AArch64.Kem

end

end

/-! # The 16-bit ciphertext rows

`u_rowsW`: the rows of `u` of the 16-bit encryption, from `Â` and `ŷ` stored with
16 bits (`EInvW true`) and the errors `e₁` (`ErrorsW`): each row is the fused
dot product, the inverse transform and the sum in 16 bits, widened into `PP`
for the compression. -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Kem
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Impl.MlKem.AArch64.Noise (noiseOff)
variable {P : KemLay} {L : Layout}

theorem fused_readyW {s₀ s : State} (hp : Pre P L s₀) (hk : KB P L s₀ s)
    {off : Nat} (ho : PO P off) {terms : List (Nat × Nat)} {F G : (Nat × Nat) → Poly}
    (hn : terms.length≤4)
    (hf : ∀ fg∈terms, PO P fg.1) (hg : ∀ fg∈terms, PO P fg.2)
    (hF : ∀ fg∈terms, PolyIsW 16 s.mem (sA L s₀ fg.1) (F fg))
    (hG : ∀ fg∈terms, PolyIsW 16 s.mem (sA L s₀ fg.2) (G fg))
    (df : ∀ fg∈terms, off+1024≤fg.1 ∨ fg.1+1024≤off)
    (dg : ∀ fg∈terms, off+1024≤fg.2 ∨ fg.2+1024≤off)
    (ht : Dot.GammaArtifact s.mem (s.syms "VG_MLKEM_GAMMA"))
    (hc : Covers [⟨s.syms "VG_MLKEM_GAMMA",512⟩] (s.rd++s.wr))
    (ha : (polyRegion (sA L s₀ off)).Disjoint ⟨s.syms "VG_MLKEM_GAMMA",512⟩) :
    DotW.ReadyW s (s.gpr .x28+BitVec.ofNat 64 off) (s.syms "VG_MLKEM_GAMMA") terms F G := by
  refine ⟨hn,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,hc,ht⟩
  · intro fg hh; have := (hf fg hh).le; kom
  · intro fg hh; have := (hg fg hh).le; kom
  · intro fg hh; rw [e28 hk]; exact hF fg hh
  · intro fg hh; rw [e28 hk]; exact hG fg hh
  · intro fg hh; rw [e28 hk,e28 hk]; exact papart hp ho (hf fg hh) (df fg hh)
  · intro fg hh; rw [e28 hk,e28 hk]; exact papart hp ho (hg fg hh) (dg fg hh)
  · intro fg hh; rw [e28 hk]; exact cov_sr hp hk (hf fg hh).le
  · intro fg hh; rw [e28 hk]; exact cov_sr hp hk (hg fg hh).le
  · rw [e28 hk]; exact cov_s hp hk ho.le
  · rwa [e28 hk]

def uFW (L : Layout) (s₀ s : State) (fg : Nat × Nat) : Poly := polyAtW 16 s.mem (sA L s₀ fg.1)
def uGW (L : Layout) (s₀ s : State) (fg : Nat × Nat) : Poly := polyAtW 16 s.mem (sA L s₀ fg.2)

theorem u_sumW {s₀ s : State} {kC co : Nat} {mE mB : Mem} {v : BitVec 64}
    {rv mv : List Byte} {i : Nat} (hi : i<P.k)
    (h : EInvW true P L s₀ kC co mE mB v rv mv P.k i s) :
    Dot.polySum (uTerms P i) (uFW L s₀ s) (uGW L s₀ s)=
      KPke.dotK (fun j => aMW true P L s₀ mB j i) (encY rv) P.k := by
  apply Optimized.polySum_dotK
  · intro j hj; exact (h.a j hj i hi).2
  · intro j hj; exact (h.y j hj).2

theorem u_readyW {s₀ s : State} (hp : Pre P L s₀)
    {kC co : Nat} {mE mB : Mem} {v : BitVec 64} {rv mv : List Byte} {i : Nat} (hi : i<P.k)
    (h : EInvW true P L s₀ kC co mE mB v rv mv P.k i s)
    (ht : Dot.GammaArtifact s.mem (s.syms "VG_MLKEM_GAMMA"))
    (hc : Covers [⟨s.syms "VG_MLKEM_GAMMA",512⟩] (s.rd++s.wr))
    (ha : (polyRegion (sA L s₀ (TP P))).Disjoint ⟨s.syms "VG_MLKEM_GAMMA",512⟩) :
    DotW.ReadyW s (s.gpr .x28+BitVec.ofNat 64 (TP P)) (s.syms "VG_MLKEM_GAMMA")
      (uTerms P i) (uFW L s₀ s) (uGW L s₀ s) := by
  have hw := hp.wf
  have term : ∀fg∈uTerms P i, ∃j<P.k, fg=(aOff P j i,yOff P j) := by
    intro fg hh
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hh
    exact ⟨j,List.mem_range.mp hj,rfl⟩
  refine fused_readyW hp h.kb (po_TP hw) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ht hc ha
  · simpa only [uTerms,List.length_map,List.length_range] using hw.facts.2.1
  · intro fg hh; obtain ⟨j,hj,rfl⟩ := term fg hh; exact po_a hw hj hi
  · intro fg hh; obtain ⟨j,hj,rfl⟩ := term fg hh; exact po_y hw hj
  · intro fg hh; obtain ⟨j,hj,rfl⟩ := term fg hh; exact ⟨(h.a j hj i hi).1,rfl⟩
  · intro fg hh; obtain ⟨j,hj,rfl⟩ := term fg hh; exact ⟨(h.y j hj).1,rfl⟩
  · intro fg hh; obtain ⟨j,hj,rfl⟩ := term fg hh
    have := ij_lt hj hi
    exact .inr (by lom)
  · intro fg hh; obtain ⟨j,hj,rfl⟩ := term fg hh
    exact .inr (by lom)

theorem fused_u_rowW {s₀ s : State} (hp : Pre P L s₀) (hr : Noise.Room P) (hc : Calls P)
    {kE eo kC co : Nat} (A : EncArgs P L kE eo kC co)
    {mE mB : Mem} {v : BitVec 64} {rv mv : List Byte} {i : Nat} (hi : i<P.k)
    (h : EInvW true P L s₀ kC co mE mB v rv mv P.k i s)
    {F G : (Nat × Nat) → Poly}
    (hd : DotW.LoopDataW s .x28 .x28 (s.gpr .x28+BitVec.ofNat 64 (TP P)) (s.syms "VG_MLKEM_GAMMA")
      (uTerms P i) (Dot.polyValues F) (Dot.polyValues G) Dot.gammaValues)
    (hsum : Dot.polySum (uTerms P i) F G = KPke.dotK (fun j => aMW true P L s₀ mB j i) (encY rv) P.k)
    (ht : Optimized.TransformTables s)
    (he : PolyIsW 16 s.mem (sA L s₀ (noiseOff P i)) (cbd rv (P.k+i))) :
    WP isa (Kem16.uRow P (slotReg kC) co i) s
      (EInvW true P L s₀ kC co mE mB v rv mv P.k (i+1)) := by
  have hw := hp.wf
  have hn : i≤P.k := Nat.le_of_lt hi
  have ef : noiseOff P i+1024≤L.len L.sc := by rw [hp.scl]; exact Noise.noise_fits hr hi
  have ep := Noise.noise_past_kem hr i
  have far : ∀r∈[R (kA s₀) L.sc (TP P) 1024,R (kA s₀) L.sc NS 1024],
      (polyRegion (sA L s₀ (noiseOff P i))).Disjoint r := by
    intro r hh
    rcases mem2' hh with rfl | rfl <;>
      exact hp.args.rdisj hp.scb hp.scb ef (hp.fs (by lom)) (.inl rfl) (.inr (.inr (by lom)))
  simp only [Kem16.uRow, seqs]
  refine WP.seq (WP.mono_syms (WP.mono (fusedW_ok hp (po_TP hw) h.kb (uTerms P i) hd)
    fun t ⟨kt,ft,pt,xt⟩ => (⟨h.frame hp kt xt ft (far_one hp A (Nat.le_refl _) hn (by lom) (by lom)),ft,pt⟩ :
      EInvW true P L s₀ kC co mE mB v rv mv P.k i t ∧ _ ∧ _)) fun s₁ ⟨e₁,f₁,t₁⟩ sy₁ => ?_)
  have p₁ : PolyIsW 16 s₁.mem _ _ := polyIsW_frame_poly (w16 := true) f₁
    (fun r hh => far r (by rw [List.mem_singleton.mp hh]; exact List.mem_cons_self ..)) he
  rw [hsum] at t₁
  have ht₁ := ht.frame sy₁ (e₁.kb.rd.trans h.kb.rd.symm) (e₁.kb.wr.trans h.kb.wr.symm) (e₁.kb.sp.trans h.kb.sp.symm)
    f₁ (cov_w hp h.kb ⟨hp.scw,hp.scb⟩ (o:=TP P) (l:=1024) (hp.fs (by lom)))
  refine WP.seq (WP.mono (invW_ok hp (po_TP hw) e₁.kb t₁.1 ht₁) fun s₂ ⟨kb₂,f₂,t₂,x₂⟩ => ?_)
  have e₂ := e₁.frame hp kb₂ x₂ f₂ (far_mul hp A (Nat.le_refl _) hn (by lom) (by lom))
  have p₂ : PolyIsW 16 s₂.mem _ _ := polyIsW_frame_poly (w16 := true) f₂ far p₁
  rw [t₁.2] at t₂
  refine WP.seq (WP.mono (addW_read_ok hp (po_TP hw) (Noise.noise_fits hr hi)
    (.inl (by lom)) e₂.kb t₂.1 p₂.1) fun s₃ ⟨kb₃,f₃,t₃,x₃⟩ => ?_)
  have e₃ := e₂.frame hp kb₃ x₃ f₃ (far_one hp A (Nat.le_refl _) hn (by lom) (by lom))
  rw [t₂.2,p₂.2] at t₃
  refine WP.seq (WP.mono (widenW_ok hp (po_TP hw) (po_PP hw) (.inl (by lom)) e₃.kb t₃)
    fun s₄ ⟨kb₄,f₄,t₄,x₄⟩ => ?_)
  have e₄ := e₃.frame hp kb₄ x₄ f₄ (far_one hp A (Nat.le_refl _) hn (by lom) (by lom))
  have fC := A.fC
  have hu := du_le hi
  refine WP.mono (ceL_ok hp hc (off := PP P) (d := P.du) (k := kC) (o := co+32*P.du*i)
    (po_PP hw) (.inl rfl) A.hkC A.wC (by lom) (by
      rcases A.sC with hC | hC
      · exact .inl hC
      · exact .inr ⟨by subst hC; lom,.inr (by subst hC; lom)⟩)
    e₄.kb t₄.1) fun s₅ ⟨kb₅,f₅,b₅,x₅⟩ => ?_
  have e₅ := e₄.frame hp kb₅ x₅ f₅ fun r hh => by
    rw [List.mem_singleton.mp hh]; exact far_ct hp A (Nat.le_refl _) (by lom)
  refine ⟨e₅.kb,e₅.x24,e₅.r,e₅.m,e₅.a,e₅.y,fun j hj => ?_,e₅.fr⟩
  rcases (by omega_using [hj] : j<i ∨ j=i) with hj | rfl
  · exact e₅.u j hj
  · rw [b₅,t₄.2]; rfl

theorem ErrorsW.frame_enc {s₀ s t : State} (hp : Pre P L s₀) (hr : Noise.Room P)
    {kE eo kC co : Nat} (A : EncArgs P L kE eo kC co) {rv : List Byte}
    (h : ErrorsW P L s₀ rv s) (hf : Frame (encW P L s₀ kC co) s.mem t.mem) : ErrorsW P L s₀ rv t := by
  intro j hj
  exact polyIsW_frame_poly (w16 := true) hf (encW_noise_far hp hr A hj) (h j hj)

theorem u_rowsW {s₀ s : State} (hp : Pre P L s₀) (hr : Noise.Room P) (hc : Calls P)
    {kE eo kC co : Nat} (A : EncArgs P L kE eo kC co)
    {mB : Mem} {v : BitVec 64} {rv mv : List Byte}
    (htr : Optimized.TransformTables s)
    (h : EInvW true P L s₀ kC co s.mem mB v rv mv P.k 0 s) (he : ErrorsW P L s₀ rv s)
    (ht : Dot.GammaArtifact s.mem (s.syms "VG_MLKEM_GAMMA"))
    (hcT : Covers [⟨s.syms "VG_MLKEM_GAMMA",512⟩] (s.rd++s.wr))
    (ha : ∀r∈encW P L s₀ kC co, (⟨s.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint r) :
    WPs ((List.range P.k).map (Kem16.uRow P (slotReg kC) co)) s
      (fun t => EInvW true P L s₀ kC co s.mem mB v rv mv P.k P.k t ∧ t.syms=s.syms) := by
  apply WPs.range (I := fun i t => EInvW true P L s₀ kC co s.mem mB v rv mv P.k i t ∧ t.syms=s.syms)
  · intro i hi t ⟨ei,hs⟩
    have et := he.frame_enc hp hr A ei.fr
    have gt : Dot.GammaArtifact t.mem (t.syms "VG_MLKEM_GAMMA") := by
      rw [hs]; exact gamma_frame ht ei.fr ha
    have ct : Covers [⟨t.syms "VG_MLKEM_GAMMA",512⟩] (t.rd++t.wr) := by
      simpa only [hs,ei.kb.rd,ei.kb.wr,←h.kb.rd,←h.kb.wr] using hcT
    have da : (polyRegion (sA L s₀ (TP P))).Disjoint ⟨t.syms "VG_MLKEM_GAMMA",512⟩ := by
      rw [hs]
      have hw := hp.wf
      have hsub : Region.Sub (R (kA s₀) L.sc (TP P) 1024) (R (kA s₀) L.sc PB (SV P-PB)) :=
        R.sub2 (by lom) (by lom)
      exact ((ha _ (by simp [encW])).sub_right hsub).symm
    exact WP.mono_syms (fused_u_rowW hp hr hc A hi ei (u_readyW hp hi ei gt ct da).data
      (u_sumW hi ei) (transform_enc_frame hp A h.kb ei.kb htr hs ei.fr) (et i hi)) fun u hu hsu => ⟨hu,hsu.trans hs⟩
  · exact ⟨h,rfl⟩

end VG.Proof.MlKem.AArch64.Kem

end

end

/-! # The 16-bit ciphertext component `v`

`v_restW`: `Kem16.vRest` decodes `t̂` from `ek` with 16 bits into the consumed
first row of the matrix (`v_decodeW`), takes its fused dot product with `ŷ`,
the inverse transform and the sum with `e₂` in 16 bits, widens the sum into
`PP` and adds the decompressed message there with 32 bits. -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Kem
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
variable {P : KemLay} {L : Layout}

/-- `VInv` with `ŷ` and `Â` stored with 16 bits. -/
structure VInvW (P : KemLay) (L : Layout) (s₀ : State) (kC co : Nat) (mE mB : Mem) (v : BitVec 64)
    (rv mv : List Byte) (nY nU : Nat) (s : State) : Prop where
  kb : KB P L s₀ s
  x24 : s.gpr .x24 = v
  r : bytesAt s.mem (sA L s₀ RB) 32 = rv
  m : bytesAt s.mem (sA L s₀ MB) 32 = mv
  y : ∀ j < nY, PolyIsW 16 s.mem (sA L s₀ (yOff P j)) (encY rv j)
  u : ∀ i < nU, bytesAt s.mem (kA s₀ (L.slot kC) + BitVec.ofNat 64 (co + 32 * P.du * i)) (32 * P.du) =
    compressEncode P.du (KPke.encU P.params (aMW true P L s₀ mB) rv i)
  fr : Frame (encW P L s₀ kC co) mE s.mem

theorem VInvW.frame {s₀ : State} (hp : Pre P L s₀) {kC co : Nat} {mE mB : Mem} {v : BitVec 64}
    {rv mv : List Byte} {nY nU : Nat} {s s' : State} (h : VInvW P L s₀ kC co mE mB v rv mv nY nU s)
    (hk : KB P L s₀ s') (hx : s'.gpr .x24 = s.gpr .x24) {W : List Region} (hf : Frame W s.mem s'.mem)
    (hW : ∀ r ∈ W, VFar P L s₀ kC co nY nU r) : VInvW P L s₀ kC co mE mB v rv mv nY nU s' := by
  have hw := hp.wf
  refine ⟨hk, by rw [hx, h.x24], ?_, ?_, fun j hj => ?_, fun i hi => ?_,
    h.fr.trans (hf.sub fun r hr => (hW r hr).2.2.2.2)⟩
  · rw [bytesAt_frame hf (fun r hr => (hW r hr).1) (by decide)]; exact h.r
  · rw [bytesAt_frame hf (fun r hr => (hW r hr).2.1) (by decide)]; exact h.m
  · exact polyIsW_frame_poly (w16 := true) hf (fun r hr => (hW r hr).2.2.1.sub_left
      (R.sub2 (by simp only [yOff]; omega_arith) (by simp only [yOff]; omega_arith))) (h.y j hj)
  · rw [bytesAt_frame hf (fun r hr => (hW r hr).2.2.2.1.sub_left
      (R.sub2 (by omega_arith) (by have := mul_succ_le (a := 32 * P.du) hi; omega_arith))) (by kom)]
    exact h.u i hi

theorem VInvW.frame_far {s₀ : State} (hp : Pre P L s₀) {kC co : Nat} {mE mB : Mem} {v : BitVec 64}
    {rv mv : List Byte} {nY nU : Nat} {s s' : State} (h : VInvW P L s₀ kC co mE mB v rv mv nY nU s)
    (hk : KB P L s₀ s') (hx : s'.gpr .x24=s.gpr .x24) {W : List Region} (hf : Frame W s.mem s'.mem)
    (hW : ∀r∈W, Far P L s₀ kC co nY nU r) : VInvW P L s₀ kC co mE mB v rv mv nY nU s' :=
  h.frame hp hk hx hf (fun r hr => (hW r hr).vfar)

theorem EInvW.vinv {s₀ s : State} {kC co : Nat} {mE mB : Mem} {v : BitVec 64}
    {rv mv : List Byte} {nY nU : Nat} (h : EInvW true P L s₀ kC co mE mB v rv mv nY nU s) :
    VInvW P L s₀ kC co mE mB v rv mv nY nU s :=
  ⟨h.kb,h.x24,h.r,h.m,h.y,h.u,h.fr⟩

/-- `DecodeInv` with 16 bits. -/
structure DecodeInvW (P : KemLay) (L : Layout) (s₀ : State) (mD : Mem)
    (T Y : Nat → Poly) (v : BitVec 64) (n : Nat) (s : State) : Prop where
  kb : KB P L s₀ s
  x24 : s.gpr .x24=v
  decoded : ∀ j<n, PolyIsW 16 s.mem (sA L s₀ (aOff P 0 j)) (T j)
  y : ∀ j<P.k, PolyIsW 16 s.mem (sA L s₀ (yOff P j)) (Y j)
  frame : Frame [R (kA s₀) L.sc AH (1024*n)] mD s.mem

theorem decode_stepW {s₀ s : State} (hp : Pre P L s₀) {kE eo : Nat}
    (hkE : kE<4) (hread : L.slot kE<L.nrd) (hfit : eo+384*P.k≤L.len (L.slot kE))
    {mD : Mem} {T Y : Nat → Poly} {v : BitVec 64} {j : Nat} (hj : j<P.k)
    (ht : ∀ i<P.k, decode12 (bytesAt s₀.mem (kA s₀ (L.slot kE)+BitVec.ofNat 64 (eo+384*i)) 384)=T i)
    (h : DecodeInvW P L s₀ mD T Y v j s) :
    WP isa (Kem16.dec12WAt (slotReg kE) (eo+384*j) (aOff P 0 j)) s (DecodeInvW P L s₀ mD T Y v (j+1)) := by
  have hw := hp.wf
  have h0 : 0<P.k := hw.facts.1
  have hs : L.slot kE ≠ L.sc := by have := hp.scw; omega_arith
  have hmul := mul_succ_le (a := 384) hj
  refine WP.mono (dec12W_ok hp (k := kE) (o := eo+384*j) hkE (by omega_arith)
    (po_a hw h0 hj) (.inl hs) h.kb) fun t ⟨kt,ft,pt,xt⟩ => ?_
  rw [h.kb.ro_bytes hread (by omega_arith),ht j hj] at pt
  refine ⟨kt,xt.trans h.x24,?_,?_,?_⟩
  · intro i hi
    rcases (by omega_arith : i<j ∨ i=j) with hi | rfl
    · exact polyIsW_frame_poly (w16 := true) ft (fun r hh => by
        rw [List.mem_singleton.mp hh]
        exact papart hp (po_a hw h0 (by omega_arith)) (po_a hw h0 hj) (.inl (by lom))) (h.decoded i hi)
    · exact pt
  · intro i hi
    exact polyIsW_frame_poly (w16 := true) ft (fun r hh => by
      rw [List.mem_singleton.mp hh]
      exact papart hp (po_y hw hi) (po_a hw h0 hj) (.inr (by
        have := Nat.mul_le_mul_right P.k hw.facts.1
        lom))) (h.y i hi)
  · exact (h.frame.sub (fun r hh => by
      rw [List.mem_singleton.mp hh]
      exact ⟨_,List.mem_singleton_self _,R.sub2 (by omega_arith) (by omega_arith)⟩)).trans
      (ft.sub (fun r hh => by
        rw [List.mem_singleton.mp hh]
        exact ⟨_,List.mem_singleton_self _,R.sub2 (by simp [aOff]) (by simp [aOff]; omega_arith)⟩))

theorem v_decodeW {s₀ s : State} (hp : Pre P L s₀) {kE eo kC co : Nat}
    (A : EncArgs P L kE eo kC co) {mE mB : Mem} {v : BitVec 64} {rv mv : List Byte} {T : Nat → Poly}
    (ht : ∀j<P.k, decode12 (bytesAt s₀.mem (kA s₀ (L.slot kE)+BitVec.ofNat 64 (eo+384*j)) 384)=T j)
    (h : VInvW P L s₀ kC co mE mB v rv mv P.k P.k s) :
    WPs ((List.range P.k).map fun j => Kem16.dec12WAt (slotReg kE) (eo+384*j) (aOff P 0 j)) s fun t =>
      VInvW P L s₀ kC co mE mB v rv mv P.k P.k t ∧
      DecodeInvW P L s₀ s.mem T (encY rv) v P.k t := by
  have hd : DecodeInvW P L s₀ s.mem T (encY rv) v 0 s :=
    ⟨h.kb,h.x24,fun _ hj => by omega_arith,h.y,Frame.refl _ _⟩
  exact WPs.mono (WPs.range (fun _ hj _ h => decode_stepW hp A.hkE A.rE A.fE hj ht h) hd) fun t dt =>
    ⟨h.frame hp dt.kb (dt.x24.trans h.x24.symm) dt.frame (fun r hh => by
      rw [List.mem_singleton.mp hh]; exact firstRow_vfar hp A),dt⟩

theorem decoded_readyW {s₀ s : State} (hp : Pre P L s₀)
    {mD : Mem} {T Y : Nat → Poly} {v : BitVec 64}
    (h : DecodeInvW P L s₀ mD T Y v P.k s)
    (ht : Dot.GammaArtifact s.mem (s.syms "VG_MLKEM_GAMMA"))
    (hc : Covers [⟨s.syms "VG_MLKEM_GAMMA",512⟩] (s.rd++s.wr))
    (ha : (polyRegion (sA L s₀ (TP P))).Disjoint ⟨s.syms "VG_MLKEM_GAMMA",512⟩) :
    DotW.ReadyW s (s.gpr .x28+BitVec.ofNat 64 (TP P)) (s.syms "VG_MLKEM_GAMMA")
      (decodedTerms P) (decodedF T) (decodedG P Y) := by
  have hw := hp.wf
  have h0 : 0<P.k := hw.facts.1
  have term : ∀ fg∈decodedTerms P, ∃ j<P.k, fg=(aOff P 0 j,yOff P j) := by
    intro fg hh
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hh
    exact ⟨j,List.mem_range.mp hj,rfl⟩
  refine fused_readyW hp h.kb (po_TP hw) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ht hc ha
  · simpa only [decodedTerms,List.length_map,List.length_range] using hw.facts.2.1
  · intro fg hh; obtain ⟨j,hj,rfl⟩ := term fg hh; exact po_a hw h0 hj
  · intro fg hh; obtain ⟨j,hj,rfl⟩ := term fg hh; exact po_y hw hj
  · intro fg hh; obtain ⟨j,hj,rfl⟩ := term fg hh
    simpa only [decodedF,aOff,Nat.mul_zero,Nat.zero_add,Nat.add_sub_cancel_left,
      Nat.mul_div_cancel_left _ (by decide : 0<1024)] using h.decoded j hj
  · intro fg hh; obtain ⟨j,hj,rfl⟩ := term fg hh
    simpa only [decodedG,yOff,Nat.add_sub_cancel_left,
      Nat.mul_div_cancel_left _ (by decide : 0<1024)] using h.y j hj
  · intro fg hh; obtain ⟨j,hj,rfl⟩ := term fg hh
    have := ij_lt h0 hj
    exact .inr (by lom)
  · intro fg hh; obtain ⟨j,hj,rfl⟩ := term fg hh
    exact .inr (by lom)

theorem v_tailW {prf : Nat→Nat→Prog isa} (valid : PrfValidW P L prf) {s₀ s : State} (hp : Pre P L s₀)
    (hc : Calls P) {kE eo kC co : Nat} (A : EncArgs P L kE eo kC co)
    {mE mB : Mem} {v : BitVec 64} {rv mv : List Byte} {T : Nat → Poly}
    (e₀ : VInvW P L s₀ kC co mE mB v rv mv P.k P.k s)
    (ht : Optimized.TransformTables s)
    (t₀ : PolyIsW 16 s.mem (sA L s₀ (TP P)) (KPke.dotK T (encY rv) P.k)) :
    WPs [Ntt16.Readonly.nttInvAtWithW (TP P) NS,prf (2*P.k) (EP P),Kem16.addWAt (TP P) (EP P),
      Kem16.widenAt (TP P) (PP P),ddAt .x28 MB 1 (EP P),addAt (PP P) (EP P),
      P.ceLAt (PP P) P.dv (slotReg kC) (co+32*P.du*P.k)] s
      (fun t => VInvW P L s₀ kC co mE mB v rv mv P.k P.k t ∧
        bytesAt t.mem (kA s₀ (L.slot kC)+BitVec.ofNat 64 (co+32*P.du*P.k)) (32*P.dv)=
          compressEncode P.dv (vPoly P T rv mv)) := by
  have hw := hp.wf
  refine WPs.cons (WP.mono (invW_ok hp (po_TP hw) e₀.kb t₀.1 ht) fun s₁ ⟨kb₁, f₁, t₁, x₁⟩ => ?_)
  have e₁ := e₀.frame_far hp kb₁ x₁ f₁ (far_mul hp A (Nat.le_refl _) (Nat.le_refl _) (by lom) (by lom))
  rw [t₀.2] at t₁
  refine WPs.cons (WP.mono (valid hp (N := 2 * P.k) (by lom) (po_EP hw) e₁.kb e₁.r)
    fun s₂ ⟨kb₂, f₂, p₂, x₂⟩ => ?_)
  have e₂ := e₁.frame_far hp kb₂ x₂ f₂ (far_pcW hp A (Nat.le_refl _) (Nat.le_refl _) (by lom) (by lom))
  have fTP : ∀ r ∈ pcW L s₀ (EP P), (polyRegion (sA L s₀ (TP P))).Disjoint r := fun r hr => by
    rcases mem6 hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact sdisj hp (po_TP hw).le (by lom) (by lom)
    · exact sdisj hp (po_TP hw).le (by lom) (by lom)
    · exact below_R hp hp.scb (hp.fs (po_TP hw).le)
    · exact sdisj hp (po_TP hw).le (by lom) (by lom)
    · exact sdisj hp (po_TP hw).le (by lom) (by lom)
    · exact papart hp (po_TP hw) (po_EP hw) (by lom)
  have t₂ : PolyIsW 16 s₂.mem _ _ := polyIsW_frame_poly (w16 := true) f₂ fTP t₁
  refine WPs.cons (WP.mono (addW_read_ok hp (po_TP hw) (by lom) (.inr (by lom)) e₂.kb t₂.1 p₂.1)
    fun s₃ ⟨kb₃, f₃, t₃, x₃⟩ => ?_)
  have e₃ := e₂.frame_far hp kb₃ x₃ f₃ (far_one hp A (Nat.le_refl _) (Nat.le_refl _) (by lom) (by lom))
  rw [t₂.2, p₂.2] at t₃
  refine WPs.cons (WP.mono (widenW_ok hp (po_TP hw) (po_PP hw) (.inl (by lom)) e₃.kb t₃)
    fun s₄ ⟨kb₄, f₄, t₄, x₄⟩ => ?_)
  have e₄ := e₃.frame_far hp kb₄ x₄ f₄ (far_one hp A (Nat.le_refl _) (Nat.le_refl _) (by lom) (by lom))
  refine WPs.cons (WP.mono (dd_ok hp (k := 3) (o := MB) (d := 1) (off := EP P) (by decide)
    (hp.fs (by lom)) (by decide) (po_EP hw) (.inr (.inl (by lom))) e₄.kb)
    fun s₅ ⟨kb₅, f₅, p₅, x₅⟩ => ?_)
  have e₅ := e₄.frame_far hp kb₅ x₅ f₅ (far_one hp A (Nat.le_refl _) (Nat.le_refl _) (by lom) (by lom))
  have t₅ := polyIs_frame f₅ (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact papart hp (po_PP hw) (po_EP hw) (by lom)) t₄
  have hm : bytesAt s₄.mem (kA s₀ (L.slot 3) + BitVec.ofNat 64 MB) (32 * 1) = mv := e₄.m
  rw [hm] at p₅
  refine WPs.cons (WP.mono (add_ok hp (po_PP hw) (po_EP hw) (.inr (by lom)) e₅.kb t₅.1 p₅.1)
    fun s₆ ⟨kb₆, f₆, t₆, x₆⟩ => ?_)
  have e₆ := e₅.frame_far hp kb₆ x₆ f₆ (far_one hp A (Nat.le_refl _) (Nat.le_refl _) (by lom) (by lom))
  rw [t₅.2, p₅.2] at t₆
  have fC := A.fC
  have hmk := Nat.mul_assoc 32 P.du P.k
  refine WPs.single (WP.mono (ceL_ok hp hc (off := PP P) (d := P.dv) (k := kC) (o := co + 32 * P.du * P.k)
    (po_PP hw) (.inr rfl) A.hkC A.wC (by lom) (by
      rcases A.sC with hC | hC
      · exact .inl hC
      · exact .inr ⟨by subst hC; lom, .inr (by subst hC; lom)⟩)
    e₆.kb t₆.1) fun s₇ ⟨kb₇, f₇, b₇, x₇⟩ => ?_)
  refine ⟨e₆.frame_far hp kb₇ x₇ f₇ fun r hr => by
    rw [List.mem_singleton.mp hr]; exact far_ct hp A (Nat.le_refl _) (by lom), ?_⟩
  rw [b₇, t₆.2]

theorem v_restW {prf : Nat→Nat→Prog isa} (valid : PrfValidW P L prf) {s₀ s : State} (hp : Pre P L s₀)
    (hc : Calls P) {kE eo kC co : Nat} (A : EncArgs P L kE eo kC co)
    {mE mB : Mem} {v : BitVec 64} {rv mv : List Byte} {T : Nat → Poly}
    (hT : ∀j<P.k, decode12 (bytesAt s₀.mem (kA s₀ (L.slot kE)+BitVec.ofNat 64 (eo+384*j)) 384)=T j)
    (htr : Optimized.TransformTables s)
    (h : VInvW P L s₀ kC co mE mB v rv mv P.k P.k s)
    (ht : Dot.GammaArtifact s.mem (s.syms "VG_MLKEM_GAMMA"))
    (hcT : Covers [⟨s.syms "VG_MLKEM_GAMMA",512⟩] (s.rd++s.wr))
    (ha : ∀r∈encW P L s₀ kC co, (⟨s.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint r) :
    WP isa (Kem16.vRest prf P (slotReg kE) eo .x28 MB (slotReg kC) co) s
      (fun t => VInvW P L s₀ kC co mE mB v rv mv P.k P.k t ∧
        bytesAt t.mem (kA s₀ (L.slot kC)+BitVec.ofNat 64 (co+32*P.du*P.k)) (32*P.dv)=
          compressEncode P.dv (vPoly P T rv mv)) := by
  have hw := hp.wf
  apply WPs.seqs (by simp)
  apply WPs.append
  refine WPs.mono_syms (v_decodeW hp A hT h) fun t ⟨vt,dt⟩ hs => ?_
  have ga : ∀r∈[R (kA s₀) L.sc AH (1024*P.k)],
      (⟨s.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint r := by
    intro r hh
    rw [List.mem_singleton.mp hh]
    obtain ⟨r',hm,hh'⟩ := (firstRow_vfar hp A).2.2.2.2
    exact (ha r' hm).sub_right hh'
  have gt : Dot.GammaArtifact t.mem (t.syms "VG_MLKEM_GAMMA") := by
    rw [hs]; exact gamma_frame ht dt.frame ga
  have ct : Covers [⟨t.syms "VG_MLKEM_GAMMA",512⟩] (t.rd++t.wr) := by
    simpa only [hs,dt.kb.rd,dt.kb.wr,←h.kb.rd,←h.kb.wr] using hcT
  have da : (polyRegion (sA L s₀ (TP P))).Disjoint ⟨t.syms "VG_MLKEM_GAMMA",512⟩ := by
    rw [hs]
    exact ((ha (R (kA s₀) L.sc PB (SV P-PB)) (by simp [encW])).sub_right
      (R.sub2 (by lom) (by lom))).symm
  have trt := htr.frame hs (dt.kb.rd.trans h.kb.rd.symm) (dt.kb.wr.trans h.kb.wr.symm)
    (dt.kb.sp.trans h.kb.sp.symm) dt.frame (cov_w hp h.kb ⟨hp.scw,hp.scb⟩ (hp.fs (by lom)))
  refine WPs.cons (WP.mono_syms (fusedW_ok hp (po_TP hw) dt.kb (decodedTerms P)
    (decoded_readyW hp dt gt ct da).data) fun u ⟨ku,fu,pu,xu⟩ hsu => ?_)
  rw [decoded_sum] at pu
  have vu := vt.frame_far hp ku xu fu (far_one hp A (Nat.le_refl _) (Nat.le_refl _) (by lom) (by lom))
  have tru := trt.frame hsu (ku.rd.trans dt.kb.rd.symm) (ku.wr.trans dt.kb.wr.symm)
    (ku.sp.trans dt.kb.sp.symm) fu (cov_w hp dt.kb ⟨hp.scw,hp.scb⟩ (hp.fs (by lom)))
  exact v_tailW valid hp hc A vu tru pu

end VG.Proof.MlKem.AArch64.Kem
