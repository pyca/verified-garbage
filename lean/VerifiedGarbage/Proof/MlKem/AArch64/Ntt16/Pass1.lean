module

public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Rows
public import VerifiedGarbage.Proof.MlKem.AArch64.NttCommon
public import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# ML-KEM's 16-bit NTT on AArch64: pass 1

Pass 1 (`pass1Body`, chunks `c < 4`): the rows of chunk `c` loaded from the
polynomial at `f` (`p1_loads`), the first three layers on them (`bfRows`),
and the rows stored into `scratch` at `64r + 16c` (`p1_stores`). After chunk
`c` the slots of the chunks before it hold the first three layers of the
polynomial (`L1.scr`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Ntt16

open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.MlKem VG.Spec.MlKem
open Impl.MlKem.AArch64.Ntt16

section
variable (s₀ : State)

abbrev fP : Addr := s₀.gpr .x0
abbrev sP : Addr := s₀.gpr .x1
abbrev P₀ : Poly := polyAt s₀.mem (fP s₀)

end

/-- The precondition. -/
structure Pre (s₀ : State) : Prop where
  wr : s₀.wr = [polyRegion (fP s₀),polyRegion (sP s₀)]
  disj : (polyRegion (fP s₀)).Disjoint (polyRegion (sP s₀))
  red : Reduced s₀.mem (fP s₀)

theorem pre_of {s₀ : State} (h : Ntt.Pre s₀) : Pre s₀ := ⟨h.wr,h.disj,h.red⟩

/-- What holds throughout. -/
structure St (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x0 : s.gpr .x0 = fP s₀
  x1 : s.gpr .x1 = sP s₀

theorem St.keep {s₀ s s' : State} (h : St s₀ s) {rs : List Reg} (hk : Keep rs s s')
    (h0 : Reg.x0 ∉ rs := by decide) (h1 : Reg.x1 ∉ rs := by decide) : St s₀ s' :=
  ⟨by rw [hk.rd, h.rd], by rw [hk.wr, h.wr], by rw [hk.sp, h.sp], by rw [hk.gpr _ h0, h.x0],
    by rw [hk.gpr _ h1, h.x1]⟩

theorem St.vchg {s₀ s s' : State} (h : St s₀ s) {rs : List VReg} (hc : VChg rs s s') : St s₀ s' :=
  ⟨by rw [hc.rd, h.rd], by rw [hc.wr, h.wr], by rw [hc.sp, h.sp], by rw [hc.gpr, h.x0],
    by rw [hc.gpr, h.x1]⟩

theorem St.vmem {s₀ s s' : State} (h : St s₀ s) {m : Mem} (hc : VMem s s' m) : St s₀ s' :=
  ⟨by rw [hc.rd, h.rd], by rw [hc.wr, h.wr], by rw [hc.sp, h.sp], by rw [hc.gpr, h.x0],
    by rw [hc.gpr, h.x1]⟩

theorem inF {s₀ s : State} (hp : Pre s₀) (h : St s₀ s) {j : Nat} (hj : j + 4 ≤ 256) :
    InRegions (s.rd ++ s.wr) (coeffAddr (fP s₀) j) 16 := by
  apply in_rd_wr
  rw [h.wr,hp.wr]
  exact in_regions (List.mem_cons_self ..) (contains_off (by omega) (by decide))

theorem inF' {s₀ s : State} (hp : Pre s₀) (h : St s₀ s) {j : Nat} (hj : j + 4 ≤ 256) :
    InRegions s.wr (coeffAddr (fP s₀) j) 16 := by
  rw [h.wr, hp.wr]
  exact in_regions (List.mem_cons_self ..) (contains_off (by omega) (by decide))

theorem inS {s₀ s : State} (hp : Pre s₀) (h : St s₀ s) {o : Nat} (ho : o + 16 ≤ 1024) :
    InRegions s.wr (sP s₀ + BitVec.ofNat 64 o) 16 := by
  rw [h.wr, hp.wr]
  exact in_regions (R := polyRegion (sP s₀)) (by simp) (contains_off ho (by decide))

theorem inS' {s₀ s : State} (hp : Pre s₀) (h : St s₀ s) {o : Nat} (ho : o + 16 ≤ 1024) :
    InRegions (s.rd ++ s.wr) (sP s₀ + BitVec.ofNat 64 o) 16 := by
  exact in_rd_wr (inS hp h ho)

theorem getD_rep0 (n r : Nat) : (List.replicate n 0).getD r 0 = 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> rfl

/-! ## Loads -/

section
variable {rest : List Instr} {Q : State → Prop}

/-- The registers of the rows and the two the loads use. -/
abbrev ldRegs : List VReg := [.v20, .v21, .v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7]

theorem row_mem_ld {r : Nat} (hr : r < 8) : row r ∈ ldRegs := by
  match r, hr with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => decide

/-- The eight rows of chunk `c`, from the polynomial `P` at `f`. -/
theorem p1_loads {s₀ : State} (hp : Pre s₀) {P : Poly} {c : Nat} (hc : c < 4) {s : State}
    (hst : St s₀ s) (hx2 : s.gpr .x2 = coeffAddr (fP s₀) (8 * c)) (hpoly : PolyIs s.mem (fP s₀) P)
    (k : ∀ s', VChg ldRegs s s' → Rows P c (List.replicate 8 0) 8 s' → WP isa (.block rest) s' Q) :
    WP isa (.block (((List.range 8).flatMap fun r =>
      [.ldrq .v20 .x2 (128 * r), .ldrq .v21 .x2 (128 * r + 16),
       .vop (.perm .uzp1 .h8 (row r) .v20 .v21)]) ++ rest)) s Q := by
  rw [WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n s' => VChg ldRegs s s' ∧ Rows P c (List.replicate 8 0) n s') (fun r w hr ⟨cw, hw⟩ => ?_) 8
    (Nat.le_refl _) s ⟨VChg.refl _ _, fun r hr => absurd hr (Nat.not_lt_zero r)⟩)
    fun s' ⟨c', h'⟩ => k s' c' h'
  have hj : 32 * r + 8 * c + 8 ≤ 256 := by omega
  have st := hst.vchg cw
  refine wp_ldrq (a := coeffAddr (fP s₀) (32 * r + 8 * c)) (by omega)
    (by rw [cw.gpr, hx2, ptr_add]; congr 2; omega) (inF hp st (by omega)) fun w₁ h₁ => ?_
  refine wp_ldrq (a := coeffAddr (fP s₀) (32 * r + 8 * c + 4)) (by omega)
    (by rw [h₁.gpr, cw.gpr, hx2, ptr_add]; congr 2; omega)
    (by rw [h₁.rd, h₁.wr]; exact inF hp st (by omega)) fun w₂ h₂ => ?_
  refine wp_vop rfl fun w₃ h₃ => wp_nil ⟨(cw.trans ((h₁.chg.trans h₂.chg).trans h₃.chg)).mono
    fun x hx => ?_, fun r' hr' => ?_⟩
  · simp only [List.mem_append] at hx
    rcases hx with hx | (hx | hx) | hx
    · exact hx
    · rw [List.mem_singleton.mp hx]; decide
    · rw [List.mem_singleton.mp hx]; decide
    · rw [List.mem_singleton.mp hx]; exact row_mem_ld hr
  · simp only [getD_rep0, Nat.zero_add, Nat.one_mul, nttL_zero]
    by_cases e : r' = r
    · subst e
      rw [h₃.v, h₂.v, h₂.get .v20, h₁.v, h₁.mem, cw.mem]
      exact rep_load hpoly hj
    · have nr := row_ne (show r' < 8 by omega)
      rw [h₃.get _ (fun h => e (row_inj r' (by omega) r hr h)), h₂.get _ nr.2.2.2.2.2.2.2.2.1,
        h₁.get _ nr.2.2.2.2.2.2.2.1]
      have := hw r' (by omega)
      simp only [getD_rep0, Nat.zero_add, Nat.one_mul, nttL_zero] at this
      exact this

/-- After the first `n` stores of vectors `x r` at `p + base r`, in a region of `len` bytes at `p`. -/
structure SInvN (len : Nat) (p : Addr) (base : Nat → Nat) (x : Nat → BitVec 128) (s : State) (n : Nat)
    (w : State) : Prop where
  gpr : w.gpr = s.gpr
  v : w.v = s.v
  keep : Keep [] s w
  frame : Frame [⟨p, len⟩] s.mem w.mem
  st : ∀ r < n, w.mem.read (p + BitVec.ofNat 64 (base r)) 16 = x r
  other : ∀ o k, o + k ≤ len → (∀ r < n, o + k ≤ base r ∨ base r + 16 ≤ o) →
    w.mem.read (p + BitVec.ofNat 64 o) k = s.mem.read (p + BitVec.ofNat 64 o) k

/-- `SInvN` in a region of 1024 bytes. -/
abbrev SInv := SInvN 1024

/-- Stores of the vectors `v` into a region of `len` bytes at `p`, at offsets `base r`, through `x`,
apart from each other. -/
theorem wp_storesN (len : Nat) (hlen : len < 2 ^ 64) {s : State} {p : Addr} {xr : Reg} {vr : Nat → VReg}
    {off base : Nat → Nat} {N : Nat}
    (hx : ∀ r < N, s.gpr xr + BitVec.ofNat 64 (off r) = p + BitVec.ofNat 64 (base r))
    (ho : ∀ r < N, off r % 16 = 0 ∧ off r < 4096 * 16) (hb : ∀ r < N, base r + 16 ≤ len)
    (hsep : ∀ r < N, ∀ r' < N, r ≠ r' → base r + 16 ≤ base r' ∨ base r' + 16 ≤ base r)
    (hin : ∀ r < N, InRegions s.wr (p + BitVec.ofNat 64 (base r)) 16)
    (k : ∀ s', SInvN len p base (fun r => s.v (vr r)) s N s' → WP isa (.block rest) s' Q) :
    WP isa (.block (((List.range N).map fun r => Instr.strq (vr r) xr (off r)) ++ rest)) s Q := by
  rw [List.map_eq_flatMap, WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (SInvN len p base (fun r => s.v (vr r)) s) (fun r w hr h => ?_) N
    (Nat.le_refl _) s ⟨rfl, rfl, Keep.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ _ _ _ => rfl⟩) fun s' h => k s' h
  refine wp_strq (a := p + BitVec.ofNat 64 (base r)) (ho r hr) (by rw [h.gpr]; exact hx r hr)
    (by rw [h.keep.wr]; exact hin r hr) fun w₁ h₁ => wp_nil ?_
  have hbr := hb r hr
  refine ⟨by rw [h₁.gpr, h.gpr], by rw [h₁.v, h.v], h.keep.trans h₁.keep |>.mono, ?_, fun r' hr' => ?_,
    fun o k ho' hs => ?_⟩
  · rw [h₁.mem]; exact h.frame.write (List.mem_singleton_self _) _ (contains_off hbr hlen)
  · rw [h₁.mem, h.v]
    by_cases e : r' = r
    · subst e; exact read_write16 _ _ _
    · have := hb r' (by omega)
      rw [Mem.read_write_sep (sep_off _ (hsep r' (by omega) r hr e) (by omega) (by omega)) (by decide)]
      exact h.st r' (by omega)
  · rw [h₁.mem, Mem.read_write_sep (sep_off _ (hs r (by omega)) (by omega) (by omega)) (by omega)]
    exact h.other o k ho' fun r' hr' => hs r' (by omega)

/-- `wp_storesN` in a region of 1024 bytes. -/
theorem wp_stores {s : State} {p : Addr} {xr : Reg} {vr : Nat → VReg} {off base : Nat → Nat} {N : Nat}
    (hx : ∀ r < N, s.gpr xr + BitVec.ofNat 64 (off r) = p + BitVec.ofNat 64 (base r))
    (ho : ∀ r < N, off r % 16 = 0 ∧ off r < 4096 * 16) (hb : ∀ r < N, base r + 16 ≤ 1024)
    (hsep : ∀ r < N, ∀ r' < N, r ≠ r' → base r + 16 ≤ base r' ∨ base r' + 16 ≤ base r)
    (hin : ∀ r < N, InRegions s.wr (p + BitVec.ofNat 64 (base r)) 16)
    (k : ∀ s', SInv p base (fun r => s.v (vr r)) s N s' → WP isa (.block rest) s' Q) :
    WP isa (.block (((List.range N).map fun r => Instr.strq (vr r) xr (off r)) ++ rest)) s Q :=
  wp_storesN 1024 (by decide) hx ho hb hsep hin k

end

/-! ## A chunk -/

/-- The first three layers on the rows of chunk `c` (`pass1Arith`). -/
theorem p1_arith {rest : List Instr} {Q : State → Prop} {P : Poly} {c : Nat} (hc : c < 4) {s₁ : State} (h₁ : Rows P c (List.replicate 8 0) 8 s₁)
    (z₁ : ∀ k < 7, vhalf (s₁.v .v18) k = BitVec.ofNat 16 (Impl.MlKem.AArch64.Ntt16.zeta (k + 1)) ∧
      vhalf (s₁.v .v19) k = BitVec.ofNat 16 (tw (Impl.MlKem.AArch64.Ntt16.zeta (k + 1))))
    (q₁ : Cst (s₁.v .v31) fun _ => 3329)
    (kk : ∀ s₈, VChg (.v22 :: .v23 :: bfRegs) s₁ s₈ → Rows P c (List.replicate 8 3) 8 s₈ →
      WP isa (.block rest) s₈ Q) :
    WP isa (.block (pass1Arith ++ rest)) s₁ Q := by
  simp only [pass1Arith, List.append_assoc]
  refine rows_bfRows hc (K := 1) (by decide) _ (lay' := [1, 1, 1, 1, 1, 1, 1, 1]) (by decide) (by decide) h₁ (z₁ 0 (by decide)).1
    (z₁ 0 (by decide)).2 q₁ fun s₂ c₂ h₂ => ?_
  have z₂ : ∀ k < 7, vhalf (s₂.v .v18) k = BitVec.ofNat 16 (Impl.MlKem.AArch64.Ntt16.zeta (k + 1)) ∧
      vhalf (s₂.v .v19) k = BitVec.ofNat 16 (tw (Impl.MlKem.AArch64.Ntt16.zeta (k + 1))) := by
    rw [c₂.get .v18, c₂.get .v19]; exact z₁
  have q₂ : Cst (s₂.v .v31) fun _ => 3329 := by rw [c₂.get .v31]; exact q₁
  refine rows_bfRows hc (K := 2) (by decide) _ (lay' := [2, 2, 2, 2, 1, 1, 1, 1]) (by decide) (by decide) h₂ (z₂ 1 (by decide)).1
    (z₂ 1 (by decide)).2 q₂ fun s₃ c₃ h₃ => ?_
  have z₃ : ∀ k < 7, vhalf (s₃.v .v18) k = BitVec.ofNat 16 (Impl.MlKem.AArch64.Ntt16.zeta (k + 1)) ∧
      vhalf (s₃.v .v19) k = BitVec.ofNat 16 (tw (Impl.MlKem.AArch64.Ntt16.zeta (k + 1))) := by
    rw [c₃.get .v18, c₃.get .v19]; exact z₂
  have q₃ : Cst (s₃.v .v31) fun _ => 3329 := by rw [c₃.get .v31]; exact q₂
  refine rows_bfRows hc (K := 3) (by decide) _ (lay' := [2, 2, 2, 2, 2, 2, 2, 2]) (by decide) (by decide) h₃ (z₃ 2 (by decide)).1
    (z₃ 2 (by decide)).2 q₃ fun s₄ c₄ h₄ => ?_
  have z₄ : ∀ k < 7, vhalf (s₄.v .v18) k = BitVec.ofNat 16 (Impl.MlKem.AArch64.Ntt16.zeta (k + 1)) ∧
      vhalf (s₄.v .v19) k = BitVec.ofNat 16 (tw (Impl.MlKem.AArch64.Ntt16.zeta (k + 1))) := by
    rw [c₄.get .v18, c₄.get .v19]; exact z₃
  have q₄ : Cst (s₄.v .v31) fun _ => 3329 := by rw [c₄.get .v31]; exact q₃
  refine rows_bfRows hc (K := 4) (by decide) _ (lay' := [3, 3, 2, 2, 2, 2, 2, 2]) (by decide) (by decide) h₄ (z₄ 3 (by decide)).1
    (z₄ 3 (by decide)).2 q₄ fun s₅ c₅ h₅ => ?_
  have z₅ : ∀ k < 7, vhalf (s₅.v .v18) k = BitVec.ofNat 16 (Impl.MlKem.AArch64.Ntt16.zeta (k + 1)) ∧
      vhalf (s₅.v .v19) k = BitVec.ofNat 16 (tw (Impl.MlKem.AArch64.Ntt16.zeta (k + 1))) := by
    rw [c₅.get .v18, c₅.get .v19]; exact z₄
  have q₅ : Cst (s₅.v .v31) fun _ => 3329 := by rw [c₅.get .v31]; exact q₄
  refine rows_bfRows hc (K := 5) (by decide) _ (lay' := [3, 3, 3, 3, 2, 2, 2, 2]) (by decide) (by decide) h₅ (z₅ 4 (by decide)).1
    (z₅ 4 (by decide)).2 q₅ fun s₆ c₆ h₆ => ?_
  have z₆ : ∀ k < 7, vhalf (s₆.v .v18) k = BitVec.ofNat 16 (Impl.MlKem.AArch64.Ntt16.zeta (k + 1)) ∧
      vhalf (s₆.v .v19) k = BitVec.ofNat 16 (tw (Impl.MlKem.AArch64.Ntt16.zeta (k + 1))) := by
    rw [c₆.get .v18, c₆.get .v19]; exact z₅
  have q₆ : Cst (s₆.v .v31) fun _ => 3329 := by rw [c₆.get .v31]; exact q₅
  refine rows_bfRows hc (K := 6) (by decide) _ (lay' := [3, 3, 3, 3, 3, 3, 2, 2]) (by decide) (by decide) h₆ (z₆ 5 (by decide)).1
    (z₆ 5 (by decide)).2 q₆ fun s₇ c₇ h₇ => ?_
  have z₇ : ∀ k < 7, vhalf (s₇.v .v18) k = BitVec.ofNat 16 (Impl.MlKem.AArch64.Ntt16.zeta (k + 1)) ∧
      vhalf (s₇.v .v19) k = BitVec.ofNat 16 (tw (Impl.MlKem.AArch64.Ntt16.zeta (k + 1))) := by
    rw [c₇.get .v18, c₇.get .v19]; exact z₆
  have q₇ : Cst (s₇.v .v31) fun _ => 3329 := by rw [c₇.get .v31]; exact q₆
  refine rows_bfRows hc (K := 7) (by decide) _ (by decide) (lay' := List.replicate 8 3) (by decide) h₇
    (z₇ 6 (by decide)).1 (z₇ 6 (by decide)).2 q₇ fun s₈ c₈ h₈ => ?_
  exact kk s₈ ((c₂.trans (c₃.trans (c₄.trans (c₅.trans (c₆.trans (c₇.trans c₈)))))).mono) h₈

/-- After `c` chunks of pass 1. -/
structure L1 (s₀ : State) (c : Nat) (s : State) (withTable : Bool := true) : Prop where
  st : St s₀ s
  x2 : s.gpr .x2 = coeffAddr (fP s₀) (8 * c)
  x3 : s.gpr .x3 = sP s₀ + BitVec.ofNat 64 (16 * c)
  x5 : (s.gpr .x5).toNat = 4 - c
  frame : Frame [polyRegion (sP s₀)] s₀.mem s.mem
  tab : if withTable then ∀ j < 64, s.mem.readW (sP s₀ + BitVec.ofNat 64 (512 + 8 * j)) 64 = hw4 tableHalves j else True
  scr : ∀ r < 8, ∀ c' < c, Rep (s.mem.read (sP s₀ + BitVec.ofNat 64 (64 * r + 16 * c')) 16)
    (fun e => (nttL 3 (P₀ s₀))[32 * r + 8 * c' + e]!) (4 * 3329)
  z : ∀ k < 7, vhalf (s.v .v18) k = BitVec.ofNat 16 (Impl.MlKem.AArch64.Ntt16.zeta (k + 1)) ∧
    vhalf (s.v .v19) k = BitVec.ofNat 16 (tw (Impl.MlKem.AArch64.Ntt16.zeta (k + 1)))
  q : Cst (s.v .v31) fun _ => 3329
  c10 : Cst (s.v .v30) fun _ => 10
  c0 : Cst (s.v .v29) fun _ => 0

theorem getD_rep_lt {n r a : Nat} (hr : r < n) : (List.replicate n a).getD r 0 = a := by
  simp [List.getD_eq_getElem?_getD, hr]

theorem p1_body {s₀ : State} (hp : Pre s₀) {c : Nat} (hc : c < 4) {s : State} {withTable : Bool} (h : L1 s₀ c s withTable) :
    WP isa (.block pass1Body) s fun s' => L1 s₀ (c + 1) s' withTable ∧ ((s'.gpr .x5).toNat ≠ 0 ↔ c + 1 ≠ 4) := by
  simp only [pass1Body, List.append_assoc]
  have hpoly : PolyIs s.mem (fP s₀) (P₀ s₀) :=
    polyIs_frame h.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.disj) ⟨hp.red, rfl⟩
  refine p1_loads hp hc h.st h.x2 hpoly fun s₁ c₁ h₁ => ?_
  have z₁ : ∀ k < 7, vhalf (s₁.v .v18) k = BitVec.ofNat 16 (Impl.MlKem.AArch64.Ntt16.zeta (k + 1)) ∧
      vhalf (s₁.v .v19) k = BitVec.ofNat 16 (tw (Impl.MlKem.AArch64.Ntt16.zeta (k + 1))) := by
    rw [c₁.get .v18, c₁.get .v19]; exact h.z
  have q₁ : Cst (s₁.v .v31) fun _ => 3329 := by rw [c₁.get .v31]; exact h.q
  refine p1_arith hc h₁ z₁ q₁ fun s₈ c₈ h₈ => ?_
  have C := c₁.trans c₈
  have st₈ : St s₀ s₈ := h.st.vchg C
  refine wp_stores (p := sP s₀) (base := fun r => 64 * r + 16 * c)
    (fun r _ => by rw [C.gpr, h.x3, ptr_add]; congr 2; omega) (fun r hr => ⟨by omega, by omega⟩)
    (fun r hr => by omega) (fun r hr r' hr' e => by omega) (fun r hr => inS hp st₈ (by omega))
    fun s₉ h₉ => ?_
  refine WP.mono (WP.keepV (Q := fun w' => Keep [.x2, .x3, .x5] s₉ w' ∧ w'.mem = s₉.mem ∧
      w'.gpr .x2 = s₉.gpr .x2 + BitVec.ofNat 64 32 ∧ w'.gpr .x3 = s₉.gpr .x3 + BitVec.ofNat 64 16 ∧
      w'.gpr .x5 = s₉.gpr .x5 - BitVec.ofNat 64 1) (by decide)
    (wp_addImm (by decide) fun w₁ k₁ e₁ => wp_addImm (by decide) fun w₂ k₂ e₂ =>
      wp_subImm (by decide) fun w₃ k₃ e₃ => wp_nil ⟨((k₁.keep.trans k₂.keep).trans k₃.keep).mono,
        by rw [k₃.mem, k₂.mem, k₁.mem], by rw [k₃.gpr .x2 (by decide), k₂.gpr .x2 (by decide), e₁],
        by rw [k₃.gpr .x3 (by decide), e₂, k₁.gpr .x3 (by decide)],
        by rw [e₃, k₂.gpr .x5 (by decide), k₁.gpr .x5 (by decide)]⟩))
    fun w ⟨⟨kw, mw, e2, e3, e5⟩, hv⟩ => ?_
  have g₉ : s₉.gpr = s.gpr := by rw [h₉.gpr, C.gpr]
  have v₉ : w.v = s₈.v := by rw [hv, h₉.v]
  have x5' : (w.gpr .x5).toNat = 4 - (c + 1) := by
    rw [e5, g₉, toNat_sub_n (by rw [h.x5]; simp; omega), h.x5]; simp; omega
  refine ⟨⟨(st₈.keep h₉.keep).keep kw, ?_, ?_, x5', ?_, ?_, fun r hr c' hc' => ?_, ?_, ?_,
    ?_, ?_⟩, by rw [x5']; omega⟩
  · rw [e2, g₉, h.x2, coeffAddr, coeffAddr, ptr_add]; congr 2
  · rw [e3, g₉, h.x3, ptr_add]; congr 2
  · rw [mw]; exact h.frame.trans (C.mem ▸ h₉.frame)
  · cases withTable with
    | false => trivial
    | true =>
      intro j hj
      have := h.tab j hj
      simp only [Mem.readW] at this ⊢
      rw [mw, h₉.other _ (64 / 8) (by omega) (fun r hr => Or.inr (by omega)), C.mem]
      exact this
  · rw [mw]
    by_cases e : c' = c
    · subst e
      rw [h₉.st r hr]
      have := h₈ r hr
      rw [getD_rep_lt hr] at this
      exact this
    · rw [h₉.other _ 16 (by omega) (fun r' hr' => by omega), C.mem]
      exact h.scr r hr c' (by omega)
  · intro k hk; rw [v₉, C.get .v18, C.get .v19]; exact h.z k hk
  · rw [v₉, C.get .v31]; exact h.q
  · rw [v₉, C.get .v30]; exact h.c10
  · rw [v₉, C.get .v29]; exact h.c0

end VG.Proof.MlKem.AArch64.Ntt16
