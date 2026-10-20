module

public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedRt.Copy
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Callee
public import VerifiedGarbage.Impl.Bignum.X86.PrecomputedRt
import VerifiedGarbage.Proof.Framework.Omega

/-! # The precomputed values into the working space

`copyIn j hi`: number `j` from the words at `pre`, `B` bytes in when `hi`
(`copyIn_ok`); `importKey`: the modulus (number 0), `R² mod M` (number 4)
and one (number 3) (`importKey_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PrecomputedRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicRt
open VG.Impl.Bignum.X86.PrecomputedRt VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.PublicRt

/-- What the copies need of `pre` (argument 2): `2 B` readable bytes, apart from the working space. -/
structure PreIn (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (s : State) : Prop where
  fit : (args 2).toNat + 2 * wb len ≤ 2 ^ 32
  read : InRegions (s.rd ++ s.wr) (byteAddr (args 2)) (2 * wb len)
  apart : Region.Disjoint ⟨byteAddr (args 2), 2 * wb len⟩ ⟨base, bytes⟩

theorem PreIn.keep {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {s t : State}
    (P : PreIn base bytes len args s) {rs : List Reg} (K : Keeps rs s t) : PreIn base bytes len args t :=
  ⟨P.fit, by rw [K.2.1, K.2.2]; exact P.read, P.apart⟩

theorem copyIn_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : RtIn base bytes len args s) (P : PreIn base bytes len args s) {j : Nat} (hj : j ≤ 7) (hi : Bool) :
    WP isa (copyIn j hi) s fun u =>
      val32 u.mem base (numAt len j) (nw len) = val32 s.mem (byteAddr (args 2)) (if hi then wb len else 0) (nw len) ∧
      Outside base (numAt len j) (wb len) s.mem u.mem ∧ Keeps [.eax, .ecx, .ebp, .esi] s u := by
  have fit := (h.fits hj).1
  have dims := h.dimensions
  have wbe := wb_eq len
  have hw := wb_le h.upper
  have pf := P.fit
  have pn : (byteAddr (args 2)).toNat = (args 2).toNat := setWidth_toNat _
  have fin : ∀ (v : State) (y : Nat), Keeps [.eax, .ecx, .ebp, .esi] s v → v.mem = s.mem →
      PtrAt v base .ebp (numAt len j) → PtrAt v (byteAddr (args 2)) .esi y → (v.gpr .ecx).toNat = wb len →
      y + wb len ≤ 2 * wb len →
      WP isa (.loop (.block [.mov .eax (.mem (at_ .esi 0)), .store (at_ .ebp 0) .eax, .alu .add .esi (.imm 4),
        .alu .add .ebp (.imm 4), .alu .sub .ecx (.imm 4)]) .ne) v fun u =>
        val32 u.mem base (numAt len j) (nw len) = val32 s.mem (byteAddr (args 2)) y (nw len) ∧
        Outside base (numAt len j) (wb len) s.mem u.mem ∧ Keeps [.eax, .ecx, .ebp, .esi] s u := by
    intro v y K mv ebp esi ecx hy
    have hv := h.ws.of_keeps K
    refine WP.mono (copyLoop_ok hv (by rw [K.2.1, K.2.2]; exact P.read) (by rw [pn]; exact pf) P.apart
      (N := nw len) (by simp only [nw]; omega) (by rw [← wbe]; exact fit) (by rw [← wbe]; exact hy) ebp esi
      (by rw [ecx, wbe])) fun u ⟨O, V, Ku⟩ => ⟨by rw [V, mv], by rw [mv] at O; rw [wbe]; exact O, K.trans Ku⟩
  have rp : ∀ (v : State) (rs : List Reg), Keeps rs s v → .esp ∉ rs → v.mem = s.mem →
      readSrc v (.mem (argAt 0 2)) = some (args 2) := fun v rs K sp mv =>
    ((h.stack 2 (by decide)).keep K sp (by rw [mv]; exact Outside.refl _ _ _ _)).readSrc
  have ptrP : ∀ (v : State) (y : Nat), y ≤ wb len → (v.gpr .esi).toNat = (args 2).toNat + y →
      PtrAt v (byteAddr (args 2)) .esi y := fun v y hy e => by
    rw [PtrAt, e, pn, Nat.mod_eq_of_lt (by omega)]
  unfold copyIn
  cases hi
  · simp only [Bool.false_eq_true, ite_false]
    refine WP.seq (slotPtr_ok (r := .ebp) (t := .ecx) (j := j) (by decide) (by decide) h.edi h.width h.upper
      (by omega) fun u K m p c => wp_movS (rp u _ K (by decide) m) fun u₁ e₁ _ => WP.block_nil ?_)
    refine fin u₁ 0 ((K.mono (by decide)).trans (e₁.keeps.mono (by decide))) (by rw [e₁.mem, m])
      (by rw [PtrAt, e₁.other _ (by decide)]; exact p) (ptrP _ 0 (Nat.zero_le _) (by rw [e₁.gpr]; rfl))
      (by rw [e₁.other _ (by decide), c, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]) (by omega)
  · simp only [ite_true]
    refine WP.seq (slotPtr_ok (r := .ebp) (t := .ecx) (j := j) (by decide) (by decide) h.edi h.width h.upper
      (by omega) fun u K m p c => wp_movS (rp u _ K (by decide) m) fun u₁ e₁ _ =>
        wp_addS rfl fun u₂ e₂ _ => WP.block_nil ?_)
    have ecx₂ : u₂.gpr .ecx = BitVec.ofNat 32 (wb len) := by
      rw [e₂.other _ (by decide), e₁.other _ (by decide), c]
    refine fin u₂ (wb len) (((K.mono (by decide)).trans (e₁.keeps.mono (by decide))).trans
        (e₂.keeps.mono (by decide))) (by rw [e₂.mem, e₁.mem, m])
      (by rw [PtrAt, e₂.other _ (by decide), e₁.other _ (by decide)]; exact p)
      (ptrP _ _ (Nat.le_refl _) ?_) (by rw [ecx₂, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]) (by omega)
    rw [e₂.gpr, e₁.gpr, show u₁.gpr .ecx = BitVec.ofNat 32 (wb len) by rw [e₁.other _ (by decide), c],
      BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := wb len) (by omega), Nat.mod_eq_of_lt (by omega)]

/-- Words of memory apart from the working space keep their value when only a range of it changes. -/
theorem val32_apart {base P : Addr} {bytes L x n d k : Nat} {m m' : Mem} (O : Outside base x n m m')
    (hxn : x + n ≤ bytes) (hap : Region.Disjoint ⟨P, L⟩ ⟨base, bytes⟩) (hd : d + 4 * k ≤ L) :
    val32 m' P d k = val32 m P d k := by
  refine val32_congr fun i hi => congrArg BitVec.toNat (Mem.readW_congr fun b hb => outside_apart O hxn ?_)
  intro hc
  refine hap _ ?_ hc
  rw [Offset.add_add]
  exact Region.contains_ofNat P (by omega)

theorem importKey_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : RtIn base bytes len args s) (P : PreIn base bytes len args s) :
    WP isa importKey s fun u =>
      val32 u.mem base (numAt len 0) (nw len) = val32 s.mem (byteAddr (args 2)) 0 (nw len) ∧
      val32 u.mem base (numAt len 4) (nw len) = val32 s.mem (byteAddr (args 2)) (wb len) (nw len) ∧
      val32 u.mem base (numAt len 3) (nw len) = 1 ∧
      Outside base numOff (5 * wb len) s.mem u.mem ∧ Keeps [.eax, .ecx, .ebp, .esi] s u := by
  have f5 := (h.fits (j := 5) (by decide)).2
  have nw' := h.scratch.nowrap
  have wbe := wb_eq len
  have e3 : numAt len 3 = 256 + 3 * wb len := by simp only [numAt, numOff] <;> omega
  have e4 : numAt len 4 = 256 + 4 * wb len := by simp only [numAt, numOff] <;> omega
  have e5 : numAt len 5 = 256 + 5 * wb len := by simp only [numAt, numOff] <;> omega
  have n0 : numAt len 0 = 256 := by simp [numAt, numOff]
  have h256 : numOff = 256 := rfl
  unfold importKey
  refine WP.seq (WP.mono (copyIn_ok h P (j := 0) (by decide) false) fun u₁ ⟨V₁, O₁, K₁⟩ => ?_)
  have h₁ := h.keep K₁ (by decide) (by decide) (O₁.mono (by omega) (by omega))
  refine WP.seq (WP.mono (copyIn_ok h₁ (P.keep K₁) (j := 4) (by decide) true) fun u₂ ⟨V₂, O₂, K₂⟩ => ?_)
  have h₂ := h₁.keep K₂ (by decide) (by decide) (O₂.mono (by omega) (by omega))
  refine WP.mono (setOne_ok h₂ (j := 3) (by decide)) fun t ⟨O₃, V₃, K₃⟩ => ⟨?_, ?_, V₃, ?_, ?_⟩
  · rw [O₃.val32 (d := numAt len 0) (k := nw len) (.inl (by omega)) (by omega),
      O₂.val32 (d := numAt len 0) (k := nw len) (.inl (by omega)) (by omega), V₁]; rfl
  · rw [O₃.val32 (d := numAt len 4) (k := nw len) (.inr (by omega)) (by omega), V₂,
      show (if true = true then wb len else 0) = wb len from rfl,
      val32_apart O₁ (by omega) P.apart (by rw [← wbe]; omega)]
  · exact ((O₁.mono (by omega) (by omega)).trans (O₂.mono (by omega) (by omega))).trans
      (O₃.mono (by omega) (by omega))
  · exact (K₁.trans K₂).trans (K₃.mono (by decide))

end VG.Proof.Bignum.X86.PrecomputedRt
