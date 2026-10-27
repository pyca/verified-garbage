module

public import VerifiedGarbage.Proof.Bignum.X86.PrecomputeRt.In
public import VerifiedGarbage.Proof.Framework.CallLay
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Callee
import VerifiedGarbage.Proof.Bignum.X86.PrecomputedRt.Copy
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.MulEnv
public import VerifiedGarbage.Proof.Bignum.MemoryFrame
public import VerifiedGarbage.Impl.Bignum.X86.PrecomputeFn

/-! # Numbers copied from the working space to `pre`

The loop of `copyOut` (`Impl/Bignum/X86/PrecomputeFn.lean`): `N` words from
`esi` in the working space to `ebp` in a writable region apart from it
(`copyOutLoop_ok`); `copyOut j hi`: number `j` to `pre`, `B` bytes in when
`hi` (`copyOut_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PrecomputeRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.PublicRt
open VG.Proof.Bignum.X86.PrecomputedRt (outside_apart)

/-- `[r + d]`, for `r = P + x`, an address in `P`'s bytes. -/
theorem ea_at {s : State} {P : Addr} {L : Nat} (hn : P.toNat + L ≤ 2 ^ 32) {r : Reg} {x d : Nat}
    (hp : PtrAt s P r x) (hd : x + d < L) : s.ea (at_ r d) = off P (x + d) := by
  rw [at_, ea_mk, addr_eq (by omega)]
  apply BitVec.eq_of_toNat_eq
  simp only [off, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have hP : P.toNat < 2 ^ 64 := P.isLt
  rw [Nat.mod_eq_of_lt (a := (s.gpr r).toNat) (by have := (s.gpr r).isLt; omega), hp]
  repeat rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem copyOutLoop_ok {t₀ : State} {W P : Addr} {L L' : Nat} (hw : Ws t₀ W L)
    (hpw : InRegions t₀.wr P L') (hn : P.toNat + L' ≤ 2 ^ 32)
    (hap : Region.Disjoint ⟨P, L'⟩ ⟨W, L⟩) {x y N : Nat} (hN : 0 < N)
    (hx : x + 4 * N ≤ L) (hy : y + 4 * N ≤ L') (hesi : PtrAt t₀ W .esi x) (hebp : PtrAt t₀ P .ebp y)
    (hecx : (t₀.gpr .ecx).toNat = 4 * N) :
    WP isa (.loop (.block [.mov .eax (.mem (at_ .esi 0)), .store (at_ .ebp 0) .eax, .alu .add .esi (.imm 4),
      .alu .add .ebp (.imm 4), .alu .sub .ecx (.imm 4)]) .ne) t₀
      fun u => Outside P y (4 * N) t₀.mem u.mem ∧ val32 u.mem P y N = val32 t₀.mem W x N ∧
        Keeps [.eax, .ecx, .ebp, .esi] t₀ u := by
  have hwn := hw.nowrap
  refine WP.mono (countLoop hN (fun j t => Keeps [.eax, .ecx, .ebp, .esi] t₀ t ∧ PtrAt t W .esi (x + 4 * j) ∧
      PtrAt t P .ebp (y + 4 * j) ∧ (t.gpr .ecx).toNat = 4 * (N - j) ∧ Outside P y (4 * j) t₀.mem t.mem ∧
      val32 t.mem P y j = val32 t₀.mem W x j) ?_
    ⟨Keeps.refl _ _, by simpa using hesi, by simpa using hebp, by simpa using hecx, Outside.refl _ _ _ _, rfl⟩)
    fun u ⟨K, _, _, _, O, V⟩ => ⟨O, V, K⟩
  rintro j t hj ⟨Kt, esi, ebp, ecx, O, V⟩
  have ht := hw.of_keeps Kt
  refine wp_movS (readSrc_ptr ht esi (d := 0) (by omega_using [hx, hj])) fun s₁ u₁ _ => ?_
  have ebp₁ : PtrAt s₁ P .ebp (y + 4 * j) := by rw [PtrAt, u₁.other _ (by decide)]; exact ebp
  have hw₁ : InRegions s₁.wr (off P (y + 4 * j + 0)) 4 := by
    rw [u₁.keeps.2.2, Kt.2.2]
    exact VG.CallLay.inRegions_sub hpw (by omega_using [hy, hj]) (by omega)
  refine wp_storeS (ea_at hn ebp₁ (d := 0) (by omega_using [hy, hj])) hw₁ fun s₂ m₂ => ?_
  refine wp_addS rfl fun s₃ u₃ _ => wp_addS rfl fun s₄ u₄ _ => wp_subZ rfl fun s₅ u₅ z₅ => WP.block_nil ?_
  obtain ⟨c₁, c₂⟩ := count_zf ecx hj
  have ecx₄ : s₄.gpr .ecx = t.gpr .ecx := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), m₂.gpr, u₁.other _ (by decide)]
  -- The source word, unchanged since the start.
  have word : (t.mem.readW (off W (x + 4 * j + 0)) 32).toNat = w32 t₀.mem W (x + 4 * j) := by
    rw [Nat.add_zero]
    refine congrArg BitVec.toNat (Mem.readW_congr fun i hi => outside_apart O (L := L') (by omega_using [hy, hj]) ?_)
    intro hc
    refine hap _ hc ?_
    rw [Offset.add_add]
    exact Region.contains_ofNat W (by omega_using [hx, hj, hi])
  refine ⟨⟨(((Kt.widen (u₁.keeps.widen (m₂.keeps []))).widen u₃.keeps).widen u₄.keeps).widen u₅.keeps,
    ?_, ?_, by rw [u₅.gpr, ecx₄]; exact c₁, ?_, ?_⟩, by rw [z₅, ecx₄, c₂]⟩
  · rw [PtrAt, u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, m₂.gpr, u₁.other _ (by decide)]
    exact ptr4 esi
  · rw [PtrAt, u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), m₂.gpr, u₁.other _ (by decide)]
    exact ptr4 ebp
  · rw [u₅.mem, u₄.mem, u₃.mem, m₂.mem, u₁.mem, Nat.add_zero]
    exact (O.mono (Nat.le_refl _) (by omega_using [])).trans
      ((writeW32_outside _ _ _ (by omega_using [hy, hj, hn])).mono (by omega_using []) (by omega_using []))
  · rw [u₅.mem, u₄.mem, u₃.mem, m₂.mem, u₁.mem, Nat.add_zero, val32_store hn (by omega_using [hy, hj]), V,
      u₁.gpr, val32_succ t₀.mem W x, ← word, Nat.add_zero]

/-- `PcIn` across writes to `pre`, which lies apart from the working space and the arguments. -/
theorem PcIn.keepOut {s t : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : PcIn base bytes len args s) {regs : List Reg} (K : Keeps regs s t) (di : .edi ∉ regs) (sp : .esp ∉ regs)
    (top : (s.gpr .esp).toNat + 28 ≤ 2 ^ 32) {o n : Nat}
    (O : Outside (byteAddr (args 0)) o n s.mem t.mem) (hon : o + n ≤ 2 * wb len) :
    PcIn base bytes len args t ∧ Frame [⟨off (byteAddr (args 0)) o, n⟩] s.mem t.mem := by
  have esp : t.gpr .esp = s.gpr .esp := K.1 _ sp
  have := wb_le h.upper
  have F := outside_frame O (by omega)
  have sub : Region.Sub ⟨off (byteAddr (args 0)) o, n⟩ ⟨byteAddr (args 0), 2 * wb len⟩ := by
    have := sub_off (base := byteAddr (args 0)) (d := o) (n := n) (e := 0) (k := 2 * wb len) (Nat.zero_le _)
      (by omega)
    simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this
  refine ⟨⟨h.scratch.of_keeps K di sp, h.lower, h.upper, h.space, fun i hi => ?_, h.wLen, h.nLen,
    h.hbase, h.hbytes, h.outFit, h.nFit, by rw [K.2.2]; exact h.outWrite, by rw [K.2.1, K.2.2]; exact h.nRead,
    h.outApart, h.nApart, by simp only [argAddr, esp]; exact h.outArgs⟩, F⟩
  have A := h.stack i hi
  refine ⟨A.stack.keep K sp, ?_⟩
  rw [← A.value]
  unfold VG.Proof.Dsa.X86.stackValue
  rw [show VG.Proof.Dsa.X86.stackAddress t i = VG.Proof.Dsa.X86.stackAddress s i by
    simp only [VG.Proof.Dsa.X86.stackAddress, esp]]
  refine F.readW (r := ⟨VG.Proof.Dsa.X86.stackAddress s i, 4⟩) (Region.contains_self _ _) (fun r hr => ?_)
    (by decide)
  rw [List.mem_singleton.mp hr]
  have P : VG.Proof.Dsa.X86.stackAddress s i = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) :=
    addr_eq (by omega)
  have Z : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 := addr_eq (by omega)
  have sa : Region.Sub ⟨VG.Proof.Dsa.X86.stackAddress s i, 4⟩ ⟨argAddr s 0, 24⟩ := by
    rw [P, Z]; exact Offset.sub _ (by omega) (by omega)
  exact ((h.outArgs.sub_left sub).sub_right sa).symm

theorem copyOut_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : PcIn base bytes len args s) {j : Nat} (hj : j ≤ 7) (hi : Bool) :
    WP isa (PrecomputeFn.copyOut j hi) s fun u =>
      val32 u.mem (byteAddr (args 0)) (if hi then wb len else 0) (nw len) = val32 s.mem base (numAt len j) (nw len) ∧
      Outside (byteAddr (args 0)) (if hi then wb len else 0) (wb len) s.mem u.mem ∧
      Keeps [.eax, .ecx, .ebp, .esi] s u := by
  have fit := (h.fits hj).1
  have dims := h.dimensions
  have wbe := wb_eq len
  have hw := wb_le h.upper
  have pf := h.outFit
  have pn : (byteAddr (args 0)).toNat = (args 0).toNat := setWidth_toNat _
  have fin : ∀ (v : State) (y : Nat), Keeps [.eax, .ecx, .ebp, .esi] s v → v.mem = s.mem →
      PtrAt v base .esi (numAt len j) → PtrAt v (byteAddr (args 0)) .ebp y → (v.gpr .ecx).toNat = wb len →
      y + wb len ≤ 2 * wb len →
      WP isa (.loop (.block [.mov .eax (.mem (at_ .esi 0)), .store (at_ .ebp 0) .eax, .alu .add .esi (.imm 4),
        .alu .add .ebp (.imm 4), .alu .sub .ecx (.imm 4)]) .ne) v fun u =>
        val32 u.mem (byteAddr (args 0)) y (nw len) = val32 s.mem base (numAt len j) (nw len) ∧
        Outside (byteAddr (args 0)) y (wb len) s.mem u.mem ∧ Keeps [.eax, .ecx, .ebp, .esi] s u := by
    intro v y K mv esi ebp ecx hy
    have hv := h.ws.of_keeps K
    refine WP.mono (copyOutLoop_ok hv (by rw [K.2.2]; exact h.outWrite) (by rw [pn]; exact pf) h.outApart
      (N := nw len) (by simp only [nw]; omega) (by rw [← wbe]; exact fit) (by rw [← wbe]; exact hy) esi ebp
      (by rw [ecx, wbe])) fun u ⟨O, V, Ku⟩ => ⟨by rw [V, mv], by rw [mv] at O; rw [wbe]; exact O, K.trans Ku⟩
  have rp : ∀ (v : State) (rs : List Reg), Keeps rs s v → .esp ∉ rs → v.mem = s.mem →
      readSrc v (.mem (argAt 0 0)) = some (args 0) := fun v rs K sp mv =>
    ((h.stack 0 (by decide)).keep K sp (by rw [mv]; exact Outside.refl _ _ _ _)).readSrc
  have ptrP : ∀ (v : State) (y : Nat), y ≤ wb len → (v.gpr .ebp).toNat = (args 0).toNat + y →
      PtrAt v (byteAddr (args 0)) .ebp y := fun v y hy e => by
    rw [PtrAt, e, pn, Nat.mod_eq_of_lt (by omega)]
  unfold PrecomputeFn.copyOut
  cases hi
  · simp only [Bool.false_eq_true, ite_false]
    refine WP.seq (slotPtr_ok (r := .esi) (t := .ecx) (j := j) (by decide) (by decide) h.edi h.width h.upper
      (by omega) fun u K m p c => wp_movS (rp u _ K (by decide) m) fun u₁ e₁ _ => WP.block_nil ?_)
    refine fin u₁ 0 ((K.mono (by decide)).trans (e₁.keeps.mono (by decide))) (by rw [e₁.mem, m])
      (by rw [PtrAt, e₁.other _ (by decide)]; exact p) (ptrP _ 0 (Nat.zero_le _) (by rw [e₁.gpr]; rfl))
      (by rw [e₁.other _ (by decide), c, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]) (by omega)
  · simp only [ite_true]
    refine WP.seq (slotPtr_ok (r := .esi) (t := .ecx) (j := j) (by decide) (by decide) h.edi h.width h.upper
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

end VG.Proof.Bignum.X86.PrecomputeRt
