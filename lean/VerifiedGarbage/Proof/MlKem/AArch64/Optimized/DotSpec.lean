module

public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Field
public import VerifiedGarbage.Proof.MlKem.KPke
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.Sha3.AArch64.Sums
public import VerifiedGarbage.Proof.MlKem.AArch64.DotW.Lane
public import VerifiedGarbage.Impl.MlKem.AArch64.AddSubW
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Vec
public import VerifiedGarbage.Proof.MlKem.AArch64.Coeff16
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Mem
public import VerifiedGarbage.Impl.MlKem.AArch64.Codec12W
public import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.Lanes
public import VerifiedGarbage.Proof.MlKem.AArch64.Common
public import VerifiedGarbage.Proof.MlKem.Kpke16Contract
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Impl.MlKem.AArch64.Codec16
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
public import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.TCB.AArch64.Isa
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.MlKem.AArch64.DotW.Loop
public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Table
import VerifiedGarbage.Proof.MlKem.PolyW
public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Result
import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
import VerifiedGarbage.Proof.MlKem.AArch64.NttCommon
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Block

/-! ### `MlKem.AArch64.Kem16.DotReady`, which the modules that import this one used -/

section

/-! ### `MlKem.AArch64.DotW`, which the modules that import this one used -/

section

/-!
# ML-KEM's fused dot product of polynomials stored with 16 bits, on AArch64

`Impl.MlKem.AArch64.DotW.dotW bo bf bg out terms` writes `Σ F ∘ G`
(`polySum`) with 16-bit coefficients to `bo + out` (`dotW_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.DotW

open VG VG.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Impl.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Dot

def setupW (bo : Reg) (out : Nat) : List Instr := ptrTo .x0 bo out ++ vconsts ++
  [.adrSym .x3 "VG_MLKEM_GAMMA", .movz .x .x11 16 0, .movz .x .x12 0 0]

theorem setupW_ok {s : State} {bo : Reg} (hbo : bo ≠ .x0) {out : Nat} (ho : out < 65536)
    (O : Nat → BitVec 16) :
    WP isa (.block (setupW bo out)) s
      (LoopInvW s (s.gpr bo + BitVec.ofNat 64 out) (s.syms "VG_MLKEM_GAMMA") O 0) := by
  unfold setupW
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono_syms (wp_ptrTo' (d := .x0) (b := bo) (s := s)
    (Q := fun s' => Only [.x0] s s' ∧ s'.gpr .x0 = s.gpr bo + BitVec.ofNat 64 out)
    hbo.symm ho (fun _ hk hx => ⟨hk, hx⟩)) ?_
  intro s₁ h₁ sy₁
  rw [WP.block_append_iff]
  refine WP.mono_syms (Ntt.vconsts_ok s₁) ?_
  intro s₂ ⟨k₂, m₂, c₂, _⟩ sy₂
  refine WP.mono (WP.keepV (Q := fun s₃ => Only [.x3, .x11, .x12] s₂ s₃ ∧
    s₃.gpr .x3 = s₂.syms "VG_MLKEM_GAMMA" ∧ s₃.gpr .x11 = BitVec.ofNat 64 16 ∧ s₃.gpr .x12 = 0)
    (by rfl) (wp_x (by rfl) fun s₃ k₃ e₃ => wp_movz fun s₄ k₄ e₄ =>
      wp_movz fun s₅ k₅ e₅ => wp_nil ⟨((k₃.trans k₄).trans k₅).mono,
        by rw [k₅.get .x3, k₄.get .x3, e₃], by rw [k₅.get .x11, e₄]; rfl, by rw [e₅]; rfl⟩))
    fun s₃ ⟨⟨k₃, e₃, e11, e12⟩, v₃⟩ => ?_
  have hm : s₃.mem = s.mem := k₃.mem.trans (m₂.trans h₁.1.mem)
  refine ⟨((h₁.1.keep.trans k₂).trans k₃.keep).mono,
    by rw [hm]; exact Frame.refl _ _, ⟨by rw [v₃]; exact c₂.q, by rw [v₃]; exact c₂.m⟩,
    ?_, ?_, e12, ?_, ?_⟩
  · rw [k₃.get .x0, k₂.get .x0, h₁.2]; exact (BitVec.add_zero _).symm
  · rw [e₃, sy₂, sy₁]; exact (BitVec.add_zero _).symm
  · rw [e11]; rfl
  · rw [hm]; intro i _; rw [ite_eq_right (by omega_using [])]

theorem dotW_partition (bo bf bg : Reg) (out : Nat) (terms : List (Nat × Nat)) :
    Impl.MlKem.AArch64.DotW.dotW bo bf bg out terms =
      .seq (.block (setupW bo out))
        (.loop (.block (Impl.MlKem.AArch64.DotW.bodyW bf bg terms)) (.nonzero .x .x11)) := by
  simp only [Impl.MlKem.AArch64.DotW.dotW, setupW, List.append_assoc]

theorem dotW_ok {s : State} {bo bf bg : Reg} (hbo : bo ≠ .x0) {out : Nat} (ho : out < 65536)
    (terms : List (Nat × Nat)) {F G : (Nat × Nat) → Poly}
    (hd : LoopDataW s bf bg (s.gpr bo + BitVec.ofNat 64 out) (s.syms "VG_MLKEM_GAMMA") terms
      (polyValues F) (polyValues G) gammaValues) :
    WP isa (Impl.MlKem.AArch64.DotW.dotW bo bf bg out terms) s fun s' =>
      Keep clob s s' ∧ Frame [⟨s.gpr bo + BitVec.ofNat 64 out, 512⟩] s.mem s'.mem ∧
      PolyIsW 16 s'.mem (s.gpr bo + BitVec.ofNat 64 out) (polySum terms F G) := by
  rw [dotW_partition]
  refine WP.seq (WP.mono (setupW_ok hbo ho (resultW terms (polyValues F) (polyValues G) gammaValues))
    fun s₁ h₁ => ?_)
  refine WP.mono (loopW_ok hd h₁) fun s₂ h₂ => ?_
  refine ⟨h₂.keep, h₂.frame, h₂.out.polyIs (fun i hi => by omega_using [hi]) fun i hi => ?_⟩
  rw [resultW, result_field terms F G hi, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have : ((polySum terms F G)[i]!).val < 3329 := Fin.isLt _
  change _ % 2 ^ 32 % 2 ^ 16 = _
  omega_using [this]

end VG.Proof.MlKem.AArch64.DotW

end

end

/-! # The fused dot product of 16-bit polynomials in 1024-byte buffers

`ReadyW`: what the fused dot product needs of polynomials stored with 16 bits
in the first half of
buffers of 1024 bytes, from which `ReadyW.data` gives `dotW`'s `LoopDataW`. -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.DotW

open VG VG.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Spec.MlKem
open VG.Proof.MlKem.AArch64.Dot

structure ReadyW (s : State) (p t : Addr) (terms : List (Nat × Nat))
    (F G : (Nat × Nat) → Poly) : Prop where
  count : terms.length ≤ 4
  offF : ∀ fg ∈ terms, fg.1 < 65536
  offG : ∀ fg ∈ terms, fg.2 < 65536
  inputF : ∀ fg ∈ terms, PolyIsW 16 s.mem (s.gpr .x28+BitVec.ofNat 64 fg.1) (F fg)
  inputG : ∀ fg ∈ terms, PolyIsW 16 s.mem (s.gpr .x28+BitVec.ofNat 64 fg.2) (G fg)
  apartF : ∀ fg ∈ terms, (polyRegion p).Disjoint (polyRegion (s.gpr .x28+BitVec.ofNat 64 fg.1))
  apartG : ∀ fg ∈ terms, (polyRegion p).Disjoint (polyRegion (s.gpr .x28+BitVec.ofNat 64 fg.2))
  readF : ∀ fg ∈ terms, Covers [polyRegion (s.gpr .x28+BitVec.ofNat 64 fg.1)] (s.rd++s.wr)
  readG : ∀ fg ∈ terms, Covers [polyRegion (s.gpr .x28+BitVec.ofNat 64 fg.2)] (s.rd++s.wr)
  write : Covers [polyRegion p] s.wr
  tableApart : (polyRegion p).Disjoint ⟨t,512⟩
  tableRead : Covers [⟨t,512⟩] (s.rd++s.wr)
  table : GammaArtifact s.mem t

theorem half_sub (p : Addr) : Region.Sub ⟨p, 512⟩ (polyRegion p) := Region.sub_prefix (by decide)

theorem ReadyW.data {s : State} {p t : Addr} {terms : List (Nat × Nat)}
    {F G : (Nat × Nat) → Poly} (h : ReadyW s p t terms F G) :
    LoopDataW s .x28 .x28 p t terms (polyValues F) (polyValues G) gammaValues := by
  refine ⟨by decide, by decide, h.count, h.offF, h.offG, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    (h.tableApart.sub_left (half_sub p)), ?_, ?_, ?_⟩
  · intro fg _ i _; exact ((F fg)[i]!).isLt
  · intro fg _ i _; exact ((G fg)[i]!).isLt
  · intro fg hf i hi; exact polyIsW_toNat (h.inputF fg hf) hi
  · intro fg hf i hi; exact polyIsW_toNat (h.inputG fg hf) hi
  · intro fg hf; exact ((h.apartF fg hf).sub_left (half_sub p)).sub_right (half_sub _)
  · intro fg hf; exact ((h.apartG fg hf).sub_left (half_sub p)).sub_right (half_sub _)
  · intro fg hf o ho
    exact h.readF fg hf _ _ (in_regions (List.mem_singleton_self _) (contains_off (by omega_using [ho]) (by decide)))
  · intro fg hf o ho
    exact h.readG fg hf _ _ (in_regions (List.mem_singleton_self _) (contains_off (by omega_using [ho]) (by decide)))
  · intro o ho
    exact h.write _ _ (in_regions (List.mem_singleton_self _) (contains_off (by omega_using [ho]) (by decide)))
  · intro c hc
    exact h.tableRead _ _ (in_regions (List.mem_singleton_self _) (contains_off (by omega_using [hc]) (by decide)))
  · intro c hc; exact h.table.lanes hc
  · intro i _; exact (gamma i).isLt

end VG.Proof.MlKem.AArch64.DotW

end

end

/-! ### `MlKem.AArch64.AddSubW`, which the modules that import this one used -/

section

/-! ### `MlKem.AArch64.Codec12W.Enc`, which this module and modules that import it used -/

section

/-! ### `MlKem.AArch64.Codec16.EncLoop`, which only this module used -/

section

/-! ### `MlKem.AArch64.Codec16.Bytes`, which this module and modules that import it used -/

section

/-! # Contiguous stores in the 384-byte encoding -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Codec16
open VG VG.AArch64 VG.Proof.MlKem.AArch64

theorem bytes_write {m : Mem} {p : Addr} {t n : Nat} {L old : Nat → Byte}
    (h : BytesUpTo m p 384 t L old) (hn : t+n ≤ 384) {x : BitVec (8*n)}
    (hx : ∀ i < n, x.extractLsb' (8*i) 8 = L (t+i)) :
    BytesUpTo (m.write (p+BitVec.ofNat 64 t) n x) p 384 (t+n) L old := by
  intro j hj
  have d : ((p+BitVec.ofNat 64 j)-(p+BitVec.ofNat 64 t)).toNat =
      if t ≤ j then j-t else 2^64+j-t := by
    exact Offset.sub_toNat' p (by omega_using [hn]) (by omega_using [hj])
  rw [Mem.write,d]
  by_cases ht : t ≤ j
  · rw [ite_eq_left ht]
    by_cases hnj : j-t<n
    · rw [ite_eq_left hnj,ite_eq_left (by omega_using [hnj]),hx _ hnj]
      congr 1; omega_using [ht]
    · rw [ite_eq_right hnj,h j hj,ite_eq_right (by omega_using [ht]),ite_eq_right (by omega_using [ht, hnj])]
  · rw [ite_eq_right ht,ite_eq_right (by omega_using [hn]),h j hj,ite_eq_left (by omega_using [ht]),ite_eq_left (by omega_using [ht])]

end VG.Proof.MlKem.AArch64.Codec16

end

end

/-! ### `MlKem.AArch64.Codec16.EncMath`, which this module and modules that import it used -/

section

/-! # Encoding arithmetic block -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Codec16
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.Rc4.AArch64
open VG.Impl.MlKem.AArch64.Codec16 (encMath)

theorem math_ok (s : State) (hm : s.v .v16 = encMask) :
    WP isa (.block encMath) s fun t =>
      t.gpr .x9 = (tbl (packed (s.v .v0) (s.v .v1)) encMask).extractLsb' 0 64 ∧
      t.gpr .x10 = (tbl (packed (s.v .v0) (s.v .v1)) encMask).extractLsb' 64 64 ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → t.gpr r = s.gpr r) ∧ t.v .v16 = s.v .v16 := by
  unfold encMath
  rrun [hm,VShiftOp.eval,packed,tbl,RegUpd.sp_setV,RegUpd.sp_write]
  refine ⟨by rfl,by rfl,?_⟩
  intro r h9 h10
  simp only [h9,h10,ite_false]

end VG.Proof.MlKem.AArch64.Codec16

end

end

/-! # ML-KEM encoding eight coefficients at a time -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Codec16
open VG VG.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Spec.MlKem
open VG.Impl.MlKem.AArch64.Codec16 (encMath maskVec)
open VG.Proof.Rc4.AArch64

theorem low_byte (v : BitVec 128) {j : Nat} (hj : j<8) :
    (v.extractLsb' 0 64).extractLsb' (8*j) 8 = vbyte v j := by
  rw [BitVec.extractLsb'_extractLsb'_of_le (by omega_using [hj])]
  rfl

theorem high_byte (v : BitVec 128) {j : Nat} (hj : j<4) :
    ((v.extractLsb' 64 64).setWidth 32).extractLsb' (8*j) 8 = vbyte v (8+j) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [vbyte,BitVec.getLsbD_extractLsb',BitVec.getLsbD_setWidth,hi,decide_true,
    Bool.true_and,show 8*j+i<32 by omega_using [hj, hi],show 8*j+i<64 by omega_using [hj, hi]]
  exact congrArg _ (by omega_using [])


theorem encMask_value : encMask = 0xffffffff0e0d0c0a0908060504020100#128 := by
  apply vbyte_ext
  exact (by decide +kernel : ∀ e<16, vbyte encMask e = vbyte 0xffffffff0e0d0c0a0908060504020100#128 e)

end VG.Proof.MlKem.AArch64.Codec16

end

end

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

end

end

/-!
# Sums of polynomials stored with 16 bits, on AArch64

`accW op` is proven once for any step `op` that computes a function `F` of
two coefficients less than `q` in halfwords (`HOpSpec`): `haddOp` computes
`(a + b) mod q`, and `accW_ok` writes `G f g` to `f` for the `G` whose
coefficients `F` computes (`addW_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.AddSubW

open VG VG.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Spec.MlKem
open VG.Impl.MlKem.AArch64.AddSubW
open VG.Proof.MlKem.AArch64.Codec12W (WP.vcs)
open VG.Proof.MlKem.AArch64.DotW (HLanes hlanes_coeffs)

section
variable {rest : List Instr} {Q : State → Prop}

theorem hlanes_map2 {s : State} {f : (w : Nat) → BitVec w → BitVec w → BitVec w} {n m : VReg}
    {A B C : Nat → Nat} (hn : HLanes (s.v n) A) (hm : HLanes (s.v m) B)
    (hf : ∀ e < 8, (f 16 (BitVec.ofNat 16 (A e)) (BitVec.ofNat 16 (B e))).toNat = C e) :
    HLanes (VArr.h8.map2 f (s.v n) (s.v m)) C := fun e he => by
  have a : vhalf (s.v n) e = BitVec.ofNat 16 (A e) := by
    apply BitVec.eq_of_toNat_eq; rw [hn e he, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hn e he ▸ (vhalf _ e).isLt)]
  have b : vhalf (s.v m) e = BitVec.ofNat 16 (B e) := by
    apply BitVec.eq_of_toNat_eq; rw [hm e he, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hm e he ▸ (vhalf _ e).isLt)]
  rw [Ntt16.vhalf_map2 _ _ _ he, a, b, hf e he]

/-- `hcsub`: `x mod q` of halfwords `x < 2q`. -/
theorem hcsub_ok {s : State} (hq : HLanes (s.v .v16) fun _ => 3329) {X : Nat → Nat}
    (hx : HLanes (s.v .v2) X) (hb : ∀ e < 8, X e < 2 * 3329)
    (k : ∀ s', VChg [.v3, .v2] s s' → HLanes (s'.v .v2) (fun e => X e % 3329) → WP isa (.block rest) s' Q) :
    WP isa (.block (hcsub ++ rest)) s Q := by
  simp only [hcsub, List.cons_append, List.nil_append]
  refine wp_vop (d := .v3) rfl fun s₁ h₁ => wp_vop (d := .v3) rfl fun s₂ h₂ =>
    wp_vop (d := .v2) rfl fun s₃ h₃ => k s₃ ((h₁.chg.trans h₂.chg).trans h₃.chg |>.mono) ?_
  intro e he
  have b := hb e he
  rw [h₃.v, Ntt16.vhalf_map2 _ _ _ he, h₂.v, h₂.get .v2, h₁.get .v2]
  dsimp only
  have va : ∀ x y : BitVec 128, vhalf (x &&& y) e = vhalf x e &&& vhalf y e := fun x y => by
    simp only [vhalf, BitVec.extractLsb'_and]
  rw [va,
    h₁.get .v16, h₁.v, Ntt16.vhalf_map2 _ _ _ he]
  have hx' := hx e he
  have hq' := hq e he
  split
  · rename_i c
    simp only [VCmpOp.test, hx', hq', decide_eq_true_eq] at c
    simp only [BitVec.allOnes_and, BitVec.toNat_sub, hx', hq']
    omega_arith
  · rename_i c
    simp only [VCmpOp.test, hx', hq', decide_eq_true_eq] at c
    have z : (0 : BitVec 16) &&& vhalf (s.v .v16) e = 0 := by ext; simp
    rw [z, BitVec.toNat_sub, hx']; simp
    omega_arith

/-- `op` computes `F a b` in the halfwords of `v2` from those of `v0 = a` and `v1 = b`, with `q`
in the halfwords of `v16`, changing only `v2` and `v3`. -/
def HOpSpec (op : List Instr) (F : Nat → Nat → Nat) : Prop :=
  ∀ (is : List Instr) (s : State) (Q : State → Prop) (A B : Nat → Nat), (∀ e < 8, A e < 3329) →
    (∀ e < 8, B e < 3329) → HLanes (s.v .v0) A → HLanes (s.v .v1) B → HLanes (s.v .v16) (fun _ => 3329) →
    (∀ s', VChg [.v2, .v3] s s' → HLanes (s'.v .v2) (fun e => F (A e) (B e)) → WP isa (.block is) s' Q) →
    WP isa (.block (op ++ is)) s Q

theorem haddOp_spec : HOpSpec haddOp fun a b => (a + b) % 3329 := by
  intro is s Q A B hA hB lA lB hq k
  simp only [haddOp, List.cons_append]
  refine wp_vop (d := .v2) rfl fun s₁ h₁ => ?_
  have l₁ : HLanes (s₁.v .v2) fun e => A e + B e := by
    rw [h₁.v]
    refine hlanes_map2 lA lB fun e he => ?_
    have := hA e he; have := hB e he
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_arith
  refine hcsub_ok (by rw [h₁.get .v16]; exact hq) l₁ (fun e he => by have := hA e he; have := hB e he; omega_arith)
    fun s₂ h₂ l₂ => k s₂ ((h₁.chg.trans h₂).mono) l₂

end

/-! ## The loop -/

/-- What `accW` needs of the state `s₀` it starts in: the reduced polynomials at `x0`, which
it can write, and at `x1`, apart. -/
structure AccData (s₀ : State) : Prop where
  rf : ∀ j, j + 16 ≤ 512 → InRegions s₀.wr (s₀.gpr .x0 + BitVec.ofNat 64 j) 16
  rg : ∀ j, j + 16 ≤ 512 → InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x1 + BitVec.ofNat 64 j) 16
  apart : (⟨s₀.gpr .x0, 512⟩ : Region).Disjoint ⟨s₀.gpr .x1, 512⟩
  f : ReducedW 16 s₀.mem (s₀.gpr .x0)
  g : ReducedW 16 s₀.mem (s₀.gpr .x1)

/-- The registers `accW` writes. -/
abbrev accClob : List Reg := [.x0, .x1, .x9, .x11]

/-- Coefficient `i` of the result. -/
def newW (F : Nat → Nat → Nat) (s₀ : State) (i : Nat) : BitVec 16 :=
  BitVec.ofNat 16 (F (coeffAtW 16 s₀.mem (s₀.gpr .x0) i).toNat (coeffAtW 16 s₀.mem (s₀.gpr .x1) i).toNat)

/-- After `k` iterations. -/
structure AccInv (F : Nat → Nat → Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ accClob → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x0 : s.gpr .x0 = s₀.gpr .x0 + BitVec.ofNat 64 (16 * k)
  x1 : s.gpr .x1 = s₀.gpr .x1 + BitVec.ofNat 64 (16 * k)
  count : (s.gpr .x11).toNat = 32 - k
  q : HLanes (s.v .v16) fun _ => 3329
  out : CoeffsInW s.mem (s₀.gpr .x0) (· < 8 * k) (newW F s₀) fun i => coeffAtW 16 s₀.mem (s₀.gpr .x0) i
  frame : Frame [⟨s₀.gpr .x0, 512⟩] s₀.mem s.mem

theorem acc_step {op : List Instr} {F : Nat → Nat → Nat} (hop : HOpSpec op F)
    (hF : ∀ a < 3329, ∀ b < 3329, F a b < 2 ^ 16) {s₀ : State} (hd : AccData s₀) {k : Nat} (hk : k < 32)
    {s : State} (h : AccInv F s₀ k s) :
    WP isa (.block (accBodyW op)) s fun s' => AccInv F s₀ (k + 1) s' ∧ ((s'.gpr .x11).toNat ≠ 0 ↔ k + 1 ≠ 32) := by
  simp only [accBodyW, List.cons_append, List.nil_append]
  refine wp_ldrq (a := s₀.gpr .x0 + BitVec.ofNat 64 (2 * (8 * k))) (by decide)
    (by rw [h.x0, BitVec.add_zero]; congr 2; omega_arith)
    (by rw [h.rd, h.wr]; exact in_rd_wr (hd.rf _ (by omega_arith))) fun s₁ h₁ => ?_
  refine wp_ldrq (a := s₀.gpr .x1 + BitVec.ofNat 64 (2 * (8 * k))) (by decide)
    (by rw [h₁.gpr, h.x1, BitVec.add_zero]; congr 2; omega_arith)
    (by rw [h₁.rd, h₁.wr, h.rd, h.wr]; exact hd.rg _ (by omega_arith)) fun s₂ h₂ => ?_
  have cf : ∀ e < 8, (coeffAtW 16 s.mem (s₀.gpr .x0) (8 * k + e)) = coeffAtW 16 s₀.mem (s₀.gpr .x0) (8 * k + e) :=
    fun e he => by rw [h.out _ (by omega_arith), ite_eq_right (by omega_arith)]
  have cg : ∀ e < 8, (coeffAtW 16 s.mem (s₀.gpr .x1) (8 * k + e)) = coeffAtW 16 s₀.mem (s₀.gpr .x1) (8 * k + e) :=
    fun e he => h.frame.readW (r := ⟨s₀.gpr .x1, 512⟩) (contains_off (by omega_arith) (by decide))
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd.apart.symm) (by decide)
  have lA : HLanes (s₂.v .v0) fun e => (coeffAtW 16 s₀.mem (s₀.gpr .x0) (8 * k + e)).toNat := by
    rw [h₂.get .v0, h₁.v]; exact hlanes_coeffs _ _ _ fun e he => by rw [cf e he]
  have lB : HLanes (s₂.v .v1) fun e => (coeffAtW 16 s₀.mem (s₀.gpr .x1) (8 * k + e)).toNat := by
    rw [h₂.v, h₁.mem]; exact hlanes_coeffs _ _ _ fun e he => by rw [cg e he]
  refine hop _ s₂ _ _ _ (fun e _ => hd.f _ (by show _ < 256; omega_arith)) (fun e _ => hd.g _ (by show _ < 256; omega_arith))
    lA lB (by rw [h₂.get .v16, h₁.get .v16]; exact h.q) fun s₃ h₃ l₃ => ?_
  have g₃ : s₃.gpr = s.gpr := by rw [h₃.gpr, h₂.gpr, h₁.gpr]
  refine wp_strq (a := s₀.gpr .x0 + BitVec.ofNat 64 (2 * (8 * k))) (by decide)
    (by rw [g₃, h.x0, BitVec.add_zero]; congr 2; omega_arith)
    (by rw [h₃.wr, h₂.wr, h₁.wr, h.wr]; exact hd.rf _ (by omega_arith)) fun s₄ h₄ => ?_
  refine WP.mono (WP.keepV (Q := fun w' => Only [.x0, .x1, .x11] s₄ w' ∧
      w'.gpr .x0 = s₄.gpr .x0 + BitVec.ofNat 64 16 ∧ w'.gpr .x1 = s₄.gpr .x1 + BitVec.ofNat 64 16 ∧
      w'.gpr .x11 = s₄.gpr .x11 - BitVec.ofNat 64 1) (by decide)
    (wp_addImm (by decide) fun s₅ h₅ e₅ => wp_addImm (by decide) fun s₆ h₆ e₆ =>
      wp_subImm (by decide) fun s₇ h₇ e₇ => wp_nil ⟨((h₅.trans h₆).trans h₇).mono,
        by rw [h₇.get .x0, h₆.get .x0, e₅], by rw [h₇.get .x1, e₆, h₅.get .x1],
        by rw [e₇, h₆.get .x11, h₅.get .x11]⟩))
    fun s' ⟨⟨k', e0, e1, e11⟩, hv⟩ => ?_
  have g₄ : s₄.gpr = s.gpr := by rw [h₄.gpr, g₃]
  have c11 : (s₄.gpr .x11).toNat = 32 - k := by rw [g₄, h.count]
  have v11 : (s'.gpr .x11).toNat = 32 - (k + 1) := by
    rw [e11, toNat_sub_n (by rw [c11]; simp; omega_arith), c11]; simp; omega_arith
  have mm : s'.mem = s.mem.write (s₀.gpr .x0 + BitVec.ofNat 64 (2 * (8 * k))) 16 (s₃.v .v2) := by
    rw [k'.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, v11, ?_, ?_, ?_⟩, by rw [v11]; omega_arith⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [k'.gpr r (by simp [hr.1, hr.2.1, hr.2.2.2]), g₄, h.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2])]
  · rw [k'.rd, h₄.rd, h₃.rd, h₂.rd, h₁.rd, h.rd]
  · rw [k'.wr, h₄.wr, h₃.wr, h₂.wr, h₁.wr, h.wr]
  · rw [k'.sp, h₄.sp, h₃.sp, h₂.sp, h₁.sp, h.sp]
  · rw [e0, g₄, h.x0, ptr_add]; congr 2
  · rw [e1, g₄, h.x1, ptr_add]; congr 2
  · rw [hv, h₄.v, h₃.v .v16 (by decide), h₂.get .v16, h₁.get .v16]; exact h.q
  · rw [mm]
    refine h.out.write16 (by omega_arith) (fun e he => BitVec.eq_of_toNat_eq ?_) (fun i _ => by omega_arith)
    rw [l₃ e he, newW, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hF _ (hd.f _ (by show _ < 256; omega_arith)) _
      (hd.g _ (by show _ < 256; omega_arith)))]
  · rw [mm]; exact h.frame.write (List.mem_singleton_self _) _ (contains_off (by omega_arith) (by decide))

theorem acc_init (F : Nat → Nat → Nat) (s : State) :
    WP isa (.block [.movz .x .x9 3329 0, .vop (.dup .h8 .v16 .x9), .movz .x .x11 32 0]) s (AccInv F s 0) := by
  show WP isa (.block ([Instr.movz .x .x9 3329 0] ++ (.vop (.dup .h8 .v16 .x9) ::
    (([.movz .x .x11 32 0] : List Instr) ++ [])))) s _
  refine wp_scalar (by decide) (P := fun s₁ => Only [.x9] s s₁ ∧ (s₁.gpr .x9).toNat = 3329)
    (wp_movz fun s₁ h₁ e₁ => wp_nil ⟨h₁, by rw [e₁]; rfl⟩) fun s₁ ⟨k₁, e9⟩ _ => ?_
  refine wp_vop (d := .v16) rfl fun s₂ h₂ => ?_
  refine wp_scalar (by decide) (P := fun s₃ => Only [.x11] s₂ s₃ ∧ (s₃.gpr .x11).toNat = 32)
    (wp_movz fun s₃ h₃ e₃ => wp_nil ⟨h₃, by rw [e₃]; rfl⟩) fun s₃ ⟨k₃, e11⟩ hv₃ => wp_nil ?_
  have m : s₃.mem = s.mem := by rw [k₃.mem, h₂.mem, k₁.mem]
  have k₃ := (k₁.keep.trans h₂.keep).trans k₃.keep
  refine ⟨fun r hr => k₃.gpr r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or, List.append_nil, List.cons_append,
      List.nil_append] at hr ⊢
    exact ⟨hr.2.2.1, hr.2.2.2⟩), k₃.rd, k₃.wr, k₃.sp,
    by rw [k₃.get .x0]; exact (BitVec.add_zero _).symm, by rw [k₃.get .x1]; exact (BitVec.add_zero _).symm,
    e11, fun e he => ?_, fun i _ => by rw [m, ite_eq_right (by omega_arith)], by rw [m]; exact Frame.refl _ _⟩
  rw [hv₃, h₂.v, Ntt16.vhalf_ofVHalves _ he]
  simp only [BitVec.toNat_setWidth, e9]

theorem accW_ok {op : List Instr} {F : Nat → Nat → Nat} (hop : HOpSpec op F)
    (hF : ∀ a < 3329, ∀ b < 3329, F a b < 3329) {G : Poly → Poly → Poly}
    (hG : ∀ P R : Poly, ∀ i < 256, ((G P R)[i]!).val = F (P[i]!).val (R[i]!).val)
    (hv : (instrs (accW op)).all (fun i => preservedV.all fun r => vdstOf i != some r) = true)
    {s : State} (hd : AccData s) :
    WP isa (accW op) s fun s' => Keep accClob s s' ∧ Frame [⟨s.gpr .x0, 512⟩] s.mem s'.mem ∧
      PolyIsW 16 s'.mem (s.gpr .x0) (G (polyAtW 16 s.mem (s.gpr .x0)) (polyAtW 16 s.mem (s.gpr .x1))) := by
  refine WP.mono (WP.vcs hv (WP.seq (WP.mono (acc_init F s) fun s₁ h₁ =>
    count_loop (by decide) (AccInv F s) (fun k hk t ht => acc_step hop (fun a ha b hb => by
      have := hF a ha b hb; omega_arith) hd hk ht) h₁)))
    fun s' ⟨h', vcs⟩ => ⟨⟨h'.gpr, h'.rd, h'.wr, h'.sp, vcs⟩, h'.frame,
      h'.out.polyIs (fun i hi => by omega_arith) fun i hi => ?_⟩
  · have hl : i < 256 := hi
    rw [newW, BitVec.toNat_ofNat, hG _ _ i hl, Nat.mod_eq_of_lt (by have := hF _ (hd.f i hl) _ (hd.g i hl); omega_arith)]
    simp only [polyAtW]
    rw [getElem!_eq _ hl, getElem!_eq _ hl, Vector.getElem_ofFn, Vector.getElem_ofFn, val_ofNat, val_ofNat,
      Nat.mod_eq_of_lt (hd.f i hl), Nat.mod_eq_of_lt (hd.g i hl)]

theorem addW_ok {s : State} (hd : AccData s) :
    WP isa addW s fun s' => Keep accClob s s' ∧ Frame [⟨s.gpr .x0, 512⟩] s.mem s'.mem ∧
      PolyIsW 16 s'.mem (s.gpr .x0) (add (polyAtW 16 s.mem (s.gpr .x0)) (polyAtW 16 s.mem (s.gpr .x1))) :=
  accW_ok haddOp_spec (fun a _ b _ => Nat.mod_lt _ (by decide))
    (fun P R i hi => by
      have : (P[i]!).val < 3329 := Fin.isLt _
      have : (R[i]!).val < 3329 := Fin.isLt _
      have hq : q = 3329 := rfl
      rw [add_get _ _ hi, val_add, condSub]; split <;> omega_arith) (by decide +kernel) hd

end VG.Proof.MlKem.AArch64.AddSubW

end

end

/-! # Fused accumulators compute the existing K-PKE dot product -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Optimized
open VG VG.Spec.MlKem VG.Proof.MlKem

theorem polySum_dotK (offsets : Nat → Nat × Nat) (F G : (Nat × Nat) → Poly)
    (a b : Nat → Poly) {k : Nat}
    (hf : ∀ j<k, F (offsets j)=a j) (hg : ∀ j<k, G (offsets j)=b j) :
    Dot.polySum ((List.range k).map offsets) F G = KPke.dotK a b k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hrec := ih (fun j hj => hf j (by omega_using [hj])) (fun j hj => hg j (by omega_using [hj]))
    unfold Dot.polySum at *
    rw [List.range_succ,List.map_append,List.foldl_append,List.map_cons,List.map_nil,
      List.foldl_cons,List.foldl_nil,hrec,hf k (by omega_using []),hg k (by omega_using [])]
    exact (KPke.foldK_succ zero_add_poly (fun j => multiplyNTTs (a j) (b j)) k).symm

end VG.Proof.MlKem.AArch64.Optimized
