module

public import VerifiedGarbage.Proof.Rc4.X86.Contract
import VerifiedGarbage.Proof.Rc4.X86.Lit
meta import VerifiedGarbage.Proof.Rc4.X86.Contract
meta import VerifiedGarbage.Proof.Rc4.X86.Lit
import VerifiedGarbage.Proof.Rc4.Stream
import VerifiedGarbage.Proof.Rc4.Table
public import VerifiedGarbage.Impl.Rc4.X86
public import VerifiedGarbage.Proof.MlDsa.X86.Pack.Run
import VerifiedGarbage.Proof.Rc4.Update
public import VerifiedGarbage.Proof.Rc4.Scan32
public import VerifiedGarbage.Spec.Rc4
import VerifiedGarbage.Proof.Rc4.Dword
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.TCB.Mem
public import VerifiedGarbage.TCB.X86.State
public import VerifiedGarbage.TCB.X86.Isa
public import VerifiedGarbage.Proof.Framework.X86.Exec
meta import VerifiedGarbage.Proof.Rc4.Stream
meta import VerifiedGarbage.Proof.Rc4.Table
meta import VerifiedGarbage.Impl.Rc4.X86
meta import VerifiedGarbage.Proof.MlDsa.X86.Pack.Run
meta import VerifiedGarbage.Proof.Rc4.Update
meta import VerifiedGarbage.Proof.Rc4.Scan32
meta import VerifiedGarbage.Spec.Rc4
meta import VerifiedGarbage.Proof.Rc4.Dword
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.TCB.Mem
meta import VerifiedGarbage.TCB.X86.State
meta import VerifiedGarbage.TCB.X86.Isa
meta import VerifiedGarbage.Proof.Framework.X86.Exec

/-! ### `Rc4.X86.Apply`, which this module and modules that import it used -/

section

/-! ### `Rc4.X86.ApplyLoop`, which this module and modules that import it used -/

section

/-! ### `Rc4.X86.Lookup`, which this module and modules that import it used -/

section

/-! # RC4 on x86 (32-bit): the table lookup, a doubleword at a time -/

@[expose] public section

namespace VG.Proof.Rc4.X86
open VG VG.X86 VG.Impl.Rc4.X86 VG.Proof.Rc4
open VG.Proof.MlDsa.X86.Pack (Keep WP.keep writesOnly addr_of_fit)

theorem eaAt (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = addr (s.gpr b) d := rfl

/-- Steps a block of the RC4 code, from a state whose accesses the hypotheses permit. -/
syntax "rrun" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| rrun) => `(tactic| rrun [])
  | `(tactic| rrun [$ls,*]) => `(tactic| (
      try unfold imm at *
      xrun [eaAt, List.cons_append, List.nil_append, $ls,*]))

/-- The address of doubleword `k` of the table at `P`, which does not wrap around. -/
theorem row_addr {P : BitVec 32} (hP : P.toNat + 256 ≤ 2 ^ 32) {k : Nat} (hk : k < 64) :
    addr P (4 * k) = P.setWidth 64 + BitVec.ofNat 64 (4 * k) := addr_of_fit (by omega_using [hP, hk])

/-! ## Visiting the doublewords -/

/-- The mask `rowMask` leaves. -/
theorem row_mask (idx : Byte) {k : Nat} (hk : k < 64) (y : BitVec 32) :
    (0#32 - (BitVec.ofBool (decide ((idx.setWidth 32 ^^^ BitVec.ofNat 32 (4 * k)).toNat <
      (BitVec.ofNat 32 4).toNat))).setWidth 32) &&& y = if idx.toNat / 4 = k then y else 0 := by
  rw [borrow_mask32, show (BitVec.ofNat 32 4).toNat = 4 from rfl]
  by_cases h : idx.toNat / 4 = k
  · rw [decide_eq_true ((row_hit32 idx hk).mpr h), ite_eq_left rfl, BitVec.allOnes_and,
      ite_eq_left h]
  · rw [decide_eq_false (fun h' => h ((row_hit32 idx hk).mp h')), ite_eq_right (by decide),
      ite_eq_right h]
    exact BitVec.zero_and

/-- The mask `laneMask` leaves. -/
theorem lane_mask (idx : Byte) {j : Nat} (hj : j < 4) (y : BitVec 32) :
    (0#32 - (BitVec.ofBool (decide (((idx.setWidth 32 &&& BitVec.ofNat 32 3) ^^^
      BitVec.ofNat 32 j).toNat < (BitVec.ofNat 32 1).toNat))).setWidth 32) &&& y =
      if idx.toNat % 4 = j then y else 0 := by
  rw [borrow_mask32, show (BitVec.ofNat 32 1).toNat = 1 from rfl]
  by_cases h : idx.toNat % 4 = j
  · rw [decide_eq_true ((lane_hit32 idx hj).mpr h), ite_eq_left rfl, BitVec.allOnes_and,
      ite_eq_left h]
  · rw [decide_eq_false (fun h' => h ((lane_hit32 idx hj).mp h')), ite_eq_right (by decide),
      ite_eq_right h]
    exact BitVec.zero_and

theorem gather_step (s : State) (idx : Byte) {k : Nat} (hk : k < 64)
    (hbp : s.gpr .ebp = idx.setWidth 32)
    (hr : InRegions (s.rd ++ s.wr) (addr (s.gpr .edi) (4 * k)) 4) :
    WP isa (.block (gatherStep k)) s fun t =>
      t.gpr .ecx = s.gpr .ecx |||
        (if idx.toNat / 4 = k then s.mem.readW (addr (s.gpr .edi) (4 * k)) 32 else 0) ∧
      t.gpr .ebp = s.gpr .ebp ∧ t.gpr .edi = s.gpr .edi ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
      t.wr = s.wr := by
  unfold gatherStep rowMask
  rrun [hbp, hr]
  rw [row_mask idx hk]

def GInv (s₀ : State) (idx : Byte) (k : Nat) (t : State) : Prop :=
  t.gpr .ecx = gather s₀.mem ((s₀.gpr .edi).setWidth 64) idx.toNat k ∧ t.gpr .ebp = s₀.gpr .ebp ∧
    t.gpr .edi = s₀.gpr .edi ∧ t.mem = s₀.mem ∧ t.rd = s₀.rd ∧ t.wr = s₀.wr

theorem gather_steps (s₀ : State) (idx : Byte) (hbp : s₀.gpr .ebp = idx.setWidth 32)
    (hfit : (s₀.gpr .edi).toNat + 256 ≤ 2 ^ 32)
    (hr : InRegions (s₀.rd ++ s₀.wr) ((s₀.gpr .edi).setWidth 64) 256) :
    ∀ n ≤ 64, ∀ s, GInv s₀ idx 0 s →
      WP isa (.block ((List.range n).flatMap gatherStep)) s (GInv s₀ idx n) := by
  intro n hn
  induction n with
  | zero => intro s h; exact WP.block_nil h
  | succ n ih =>
    intro s h
    rw [flatMap_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega_using [hn]) s h) fun t ht => ?_
    obtain ⟨h11, h9', hdi, hm, hrd, hwr⟩ := ht
    have hq : InRegions (t.rd ++ t.wr) (addr (t.gpr .edi) (4 * n)) 4 := by
      rw [hrd, hwr, hdi, row_addr hfit (by omega_using [hn])]
      exact region_offset _ _ _ _ _ (by omega_using [hn]) (by omega_using [hn]) hr
    refine WP.mono (gather_step t idx (by omega_using [hn]) (h9'.trans hbp) hq) fun u hu => ?_
    obtain ⟨u11, u9, udi, um, urd, uwr⟩ := hu
    refine ⟨?_, u9.trans h9', udi.trans hdi, um.trans hm, urd.trans hrd, uwr.trans hwr⟩
    rw [u11, h11, hdi, hm, row_addr hfit (by omega_using [hn]), gather_succ]

/-! ## Picking the byte of the doubleword -/

theorem pick_step (s : State) (idx : Byte) {j : Nat} (hj : j < 4)
    (hbp : s.gpr .ebp = idx.setWidth 32) :
    WP isa (.block (pickStep j)) s fun t =>
      t.gpr .eax = s.gpr .eax ||| (if idx.toNat % 4 = j then s.gpr .ecx else 0) ∧
      t.gpr .ecx = s.gpr .ecx >>> 8 ∧
      t.gpr .ebp = s.gpr .ebp ∧ t.gpr .edi = s.gpr .edi ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
      t.wr = s.wr := by
  unfold pickStep laneMask
  rrun [hbp]
  rw [lane_mask idx hj]

def PInv (s₀ : State) (q : BitVec 32) (L j : Nat) (t : State) : Prop :=
  t.gpr .eax = pick q L j ∧ t.gpr .ecx = q >>> (8 * j) ∧ t.gpr .ebp = s₀.gpr .ebp ∧
    t.gpr .edi = s₀.gpr .edi ∧ t.mem = s₀.mem ∧ t.rd = s₀.rd ∧ t.wr = s₀.wr

theorem pick_steps (s₀ : State) (idx : Byte) (q : BitVec 32) (hbp : s₀.gpr .ebp = idx.setWidth 32) :
    ∀ n ≤ 4, ∀ s, PInv s₀ q (idx.toNat % 4) 0 s →
      WP isa (.block ((List.range n).flatMap pickStep)) s (PInv s₀ q (idx.toNat % 4) n) := by
  intro n hn
  induction n with
  | zero => intro s h; exact WP.block_nil h
  | succ n ih =>
    intro s h
    rw [flatMap_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega_using [hn]) s h) fun t ht => ?_
    obtain ⟨hax, h11, h9', hdi, hm, hrd, hwr⟩ := ht
    refine WP.mono (pick_step t idx (by omega_using [hn]) (h9'.trans hbp)) fun u hu => ?_
    obtain ⟨uax, u11, u9, udi, um, urd, uwr⟩ := hu
    refine ⟨?_, ?_, u9.trans h9', udi.trans hdi, um.trans hm, urd.trans hrd, uwr.trans hwr⟩
    · rw [uax, hax, h11, pick_succ]
    · rw [u11, h11, shr_byte32]

/-! ## The lookup -/

theorem lookup_core (s : State) (idx : Byte) (hbp : s.gpr .ebp = idx.setWidth 32)
    (hfit : (s.gpr .edi).toNat + 256 ≤ 2 ^ 32)
    (hr : InRegions (s.rd ++ s.wr) ((s.gpr .edi).setWidth 64) 256) :
    WP isa (.block lookup) s fun t =>
      t.gpr .eax = (s.mem ((s.gpr .edi).setWidth 64 + BitVec.ofNat 64 idx.toNat)).setWidth 32 ∧
      t.mem = s.mem := by
  have hn := idx.isLt
  simp only [lookup, List.append_assoc]
  rw [WP.block_append_iff]
  have h0 : WP isa (.block [.mov .ecx (imm 0)]) s (GInv s idx 0) := by
    rrun [GInv, gather, Nat.not_lt_zero]
  refine WP.mono h0 fun t ht => ?_
  rw [WP.block_append_iff]
  refine WP.mono (gather_steps s idx hbp hfit hr 64 (by decide) t ht) fun u hu => ?_
  obtain ⟨u11, u9, udi, um, urd, uwr⟩ := hu
  let q := s.mem.readW ((s.gpr .edi).setWidth 64 + BitVec.ofNat 64 (4 * (idx.toNat / 4))) 32
  have hq : u.gpr .ecx = q := by
    rw [u11]; unfold gather; rw [ite_eq_left (by omega_using [])]
  rw [WP.block_append_iff]
  have h1 : WP isa (.block [.mov .eax (imm 0)]) u (PInv s q (idx.toNat % 4) 0) := by
    rrun [PInv, pick, hq, u9, udi, um, urd, uwr, Nat.mul_zero, BitVec.ushiftRight_zero,
      Nat.not_lt_zero]
  refine WP.mono h1 fun v hv => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pick_steps s idx q hbp 4 (by decide) v hv) fun w hw => ?_
  obtain ⟨wax, _, _, _, wm, _, _⟩ := hw
  have hL : idx.toNat % 4 < 4 := Nat.mod_lt _ (by decide)
  rrun [wax, wm]
  unfold pick
  rw [ite_eq_left hL, dword_byte _ _ hL, row_lane32]

end VG.Proof.Rc4.X86

end

end

/-! ### `Rc4.X86.Replace`, which this module and modules that import it used -/

section

/-! # RC4 on x86 (32-bit): replacing a secret-indexed byte of the table -/

@[expose] public section

namespace VG.Proof.Rc4.X86
open VG VG.X86 VG.Impl.Rc4.X86 VG.Proof.Rc4
open VG.Proof.MlDsa.X86.Pack (Keep WP.keep writesOnly addr_of_fit)

/-! ## Moving the difference to the byte's lane -/

theorem spread_step (s : State) (idx c : Byte) {j : Nat} (hj : j < 4)
    (hbp : s.gpr .ebp = idx.setWidth 32) (hax : s.gpr .eax = c.setWidth 32)
    (hcx : s.gpr .ecx = spread c (idx.toNat % 4) (j + 1)) :
    WP isa (.block (spreadStep j)) s fun t =>
      t.gpr .ecx = spread c (idx.toNat % 4) j ∧ t.gpr .eax = s.gpr .eax ∧
      t.gpr .ebp = s.gpr .ebp ∧ t.mem = s.mem := by
  unfold spreadStep laneMask
  rrun [hbp, hax, hcx]
  rw [lane_mask idx hj, spread_succ c (Nat.mod_lt _ (by decide))]

theorem spread_steps (s₀ : State) (idx c : Byte) (hbp : s₀.gpr .ebp = idx.setWidth 32)
    (hax : s₀.gpr .eax = c.setWidth 32) :
    ∀ n ≤ 4, ∀ s, s.gpr .ecx = spread c (idx.toNat % 4) n → s.gpr .eax = s₀.gpr .eax →
      s.gpr .ebp = s₀.gpr .ebp → s.mem = s₀.mem →
      WP isa (.block ((List.range n).reverse.flatMap spreadStep)) s fun t =>
        t.gpr .ecx = spread c (idx.toNat % 4) 0 ∧ t.gpr .eax = s₀.gpr .eax ∧ t.mem = s₀.mem := by
  intro n hn
  induction n with
  | zero => intro s hcx hax' _ hm; exact WP.block_nil ⟨hcx, hax', hm⟩
  | succ n ih =>
    intro s hcx hax' hbp' hm
    rw [List.range_succ, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, WP.block_append_iff]
    refine WP.mono (spread_step s idx c (by omega_using [hn]) (hbp'.trans hbp) (hax'.trans hax) hcx)
      fun t ⟨tcx, tax, tbp, tm⟩ => ?_
    exact ih (by omega_using [hn]) t tcx (tax.trans hax') (tbp.trans hbp') (tm.trans hm)

theorem lanesDown_eq : lanesDown = (List.range 4).reverse := rfl

/-! ## Storing back every doubleword -/

theorem scatter_step (s : State) (idx : Byte) {k : Nat} (hk : k < 64)
    (hbp : s.gpr .ebp = idx.setWidth 32)
    (hw : InRegions s.wr (addr (s.gpr .edi) (4 * k)) 4) :
    WP isa (.block (scatterStep k)) s fun t =>
      t.mem = s.mem.writeW (addr (s.gpr .edi) (4 * k))
        ((if idx.toNat / 4 = k then s.gpr .ecx else 0) ^^^
          s.mem.readW (addr (s.gpr .edi) (4 * k)) 32) ∧
      t.gpr .ecx = s.gpr .ecx ∧ t.gpr .ebp = s.gpr .ebp ∧ t.gpr .edi = s.gpr .edi ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  have hr : InRegions (s.rd ++ s.wr) (addr (s.gpr .edi) (4 * k)) 4 := by
    obtain ⟨r, hr, hc⟩ := hw
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  unfold scatterStep rowMask
  rrun [hbp, hr, hw]
  rw [row_mask idx hk]

theorem scatter_steps (s₀ : State) (idx : Byte) (d : BitVec 32)
    (hbp : s₀.gpr .ebp = idx.setWidth 32) (hfit : (s₀.gpr .edi).toNat + 256 ≤ 2 ^ 32)
    (hw : InRegions s₀.wr ((s₀.gpr .edi).setWidth 64) 256) :
    ∀ n ≤ 64, ∀ s, s.gpr .ecx = d → s.gpr .ebp = s₀.gpr .ebp → s.gpr .edi = s₀.gpr .edi →
      s.wr = s₀.wr → s.mem = s₀.mem →
      WP isa (.block ((List.range n).flatMap scatterStep)) s fun t =>
        t.mem = scatter s₀.mem ((s₀.gpr .edi).setWidth 64) idx.toNat d n ∧ t.gpr .ecx = d ∧
        t.gpr .ebp = s₀.gpr .ebp ∧ t.gpr .edi = s₀.gpr .edi ∧ t.wr = s₀.wr := by
  intro n hn
  induction n with
  | zero =>
    intro s hcx hbp' hdi hwr hm
    refine WP.block_nil ⟨?_, hcx, hbp', hdi, hwr⟩
    rw [hm]; unfold scatter; rw [ite_eq_right (Nat.not_lt_zero _)]
  | succ n ih =>
    intro s hcx hbp' hdi hwr hm
    rw [flatMap_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega_using [hn]) s hcx hbp' hdi hwr hm) fun t ⟨tm, tcx, tbp, tdi, twr⟩ => ?_
    have hq : InRegions t.wr (addr (t.gpr .edi) (4 * n)) 4 := by
      rw [twr, tdi, row_addr hfit (by omega_using [hn])]
      exact region_offset _ _ _ _ _ (by omega_using [hn]) (by omega_using [hn]) hw
    refine WP.mono (scatter_step t idx (by omega_using [hn]) (tbp.trans hbp) hq)
      fun u ⟨um, ucx, ubp, udi, _, uwr⟩ => ?_
    refine ⟨?_, ucx.trans tcx, ubp.trans tbp, udi.trans tdi, uwr.trans twr⟩
    rw [um, tm, tcx, tdi, row_addr hfit (by omega_using [hn]), scatter_succ]

/-! ## The replacement -/

/-- The address `loadI` reads: byte `i` of the table at `P`. -/
theorem idx_addr {P : BitVec 32} (hP : P.toNat + 256 ≤ 2 ^ 32) (i : Byte) :
    addr (P + i.setWidth 32) 0 = P.setWidth 64 + BitVec.ofNat 64 i.toNat := by
  unfold addr
  rw [BitVec.add_zero, byte32 i]
  exact VG.Proof.MlKem.X86.ea_off (by have := i.isLt; omega_using [hP])

theorem loadI_ok (s : State) (ii : Byte) (hsi : s.gpr .esi = ii.setWidth 32)
    (hfit : (s.gpr .edi).toNat + 256 ≤ 2 ^ 32)
    (hr : InRegions (s.rd ++ s.wr) ((s.gpr .edi).setWidth 64) 256) :
    WP isa (.block loadI) s fun t =>
      t.gpr .edx = (s.mem ((s.gpr .edi).setWidth 64 + BitVec.ofNat 64 ii.toNat)).setWidth 32 ∧
      Keep [.edx] s t ∧ t.mem = s.mem := by
  have hi : InRegions (s.rd ++ s.wr) (addr (s.gpr .edi + ii.setWidth 32) 0) 1 := by
    rw [idx_addr hfit ii]
    exact region_offset _ _ _ _ _ (by have := ii.isLt; omega_using []) (by have := ii.isLt; omega_using []) hr
  refine WP.mono (WP.keep (Q := fun t =>
      t.gpr .edx = (s.mem ((s.gpr .edi).setWidth 64 + BitVec.ofNat 64 ii.toNat)).setWidth 32 ∧
      t.mem = s.mem) [.edx] ?_ (by decide +kernel)) fun t ⟨h, hk⟩ => ⟨h.1, hk, h.2⟩
  unfold loadI
  rw [← hsi] at hi
  rrun [hi]
  rw [hsi, idx_addr hfit ii]

theorem replace_core (s : State) (idx ii : Byte) (hbp : s.gpr .ebp = idx.setWidth 32)
    (hsi : s.gpr .esi = ii.setWidth 32) (hfit : (s.gpr .edi).toNat + 256 ≤ 2 ^ 32)
    (hw : InRegions s.wr ((s.gpr .edi).setWidth 64) 256) :
    WP isa (.block replace) s fun t =>
      t.gpr .eax = (s.mem ((s.gpr .edi).setWidth 64 + BitVec.ofNat 64 idx.toNat)).setWidth 32 ∧
      t.mem = s.mem.write ((s.gpr .edi).setWidth 64 + BitVec.ofNat 64 idx.toNat) 1
        (s.mem ((s.gpr .edi).setWidth 64 + BitVec.ofNat 64 ii.toNat)) := by
  have hn := idx.isLt
  have hr : InRegions (s.rd ++ s.wr) ((s.gpr .edi).setWidth 64) 256 := by
    obtain ⟨r, hr, hc⟩ := hw
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  let p := (s.gpr .edi).setWidth 64
  let b := s.mem (p + BitVec.ofNat 64 idx.toNat)
  let v := s.mem (p + BitVec.ofNat 64 ii.toNat)
  simp only [replace, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.eax, .ecx, .edx] (lookup_core s idx hbp hfit hr) (by decide +kernel))
    fun t ⟨⟨tax, tm⟩, tk⟩ => ?_
  have tbp : t.gpr .ebp = s.gpr .ebp := tk.gpr (by decide)
  have tdi : t.gpr .edi = s.gpr .edi := tk.gpr (by decide)
  have tsi : t.gpr .esi = s.gpr .esi := tk.gpr (by decide)
  have htr : InRegions (t.rd ++ t.wr) ((t.gpr .edi).setWidth 64) 256 := by
    rw [tk.2.1, tk.2.2, tdi]; exact hr
  rw [WP.block_append_iff]
  refine WP.mono (loadI_ok t ii (tsi.trans hsi) (by rw [tdi]; exact hfit) htr)
    fun t' ⟨t'dx, t'k, t'm⟩ => ?_
  rw [tdi, tm] at t'dx
  rw [WP.block_append_iff]
  have h1 : WP isa (.block [.alu .xor .eax (.reg .edx), .mov .ecx (imm 0)]) t' fun u =>
      u.gpr .eax = (b ^^^ v).setWidth 32 ∧ u.gpr .ecx = 0 ∧ u.gpr .ebp = s.gpr .ebp ∧
        u.gpr .edi = s.gpr .edi ∧ u.gpr .esi = s.gpr .esi ∧ u.mem = s.mem ∧ u.rd = s.rd ∧
        u.wr = s.wr := by
    have t'ax : t'.gpr .eax = b.setWidth 32 := (t'k.gpr (by decide)).trans tax
    rrun [t'ax, t'dx, t'm, tm, (t'k.gpr (r := .ebp) (by decide)).trans tbp,
      (t'k.gpr (r := .edi) (by decide)).trans tdi, (t'k.gpr (r := .esi) (by decide)).trans tsi,
      t'k.2.1, t'k.2.2, tk.2.1, tk.2.2]
    rw [xor_byte32]
  refine WP.mono h1 fun u ⟨uax, ucx, ubp, udi, usi, um, urd, uwr⟩ => ?_
  rw [WP.block_append_iff]
  have hsp := spread_steps u idx (b ^^^ v) (ubp.trans hbp) uax 4 (by decide) u
    (by rw [ucx]; unfold spread; rw [ite_eq_right (by omega_using [])]) rfl rfl rfl
  rw [← lanesDown_eq] at hsp
  refine WP.mono (WP.keep [.ecx, .edx] hsp (by decide +kernel)) fun w ⟨⟨wcx, wax, wm⟩, wk⟩ => ?_
  have wbp : w.gpr .ebp = s.gpr .ebp := (wk.gpr (by decide)).trans ubp
  have wdi : w.gpr .edi = s.gpr .edi := (wk.gpr (by decide)).trans udi
  have wsi : w.gpr .esi = s.gpr .esi := (wk.gpr (by decide)).trans usi
  have wrd : w.rd = s.rd := wk.2.1.trans urd
  have wwr : w.wr = s.wr := wk.2.2.trans uwr
  have hwr' : InRegions (w.rd ++ w.wr) ((w.gpr .edi).setWidth 64) 256 := by
    rw [wrd, wwr, wdi]; exact hr
  rw [WP.block_append_iff]
  refine WP.mono (loadI_ok w ii (wsi.trans hsi) (by rw [wdi]; exact hfit) hwr')
    fun w' ⟨w'dx, w'k, w'm⟩ => ?_
  rw [wdi, wm, um] at w'dx
  rw [WP.block_append_iff]
  have h2 : WP isa (.block [.alu .xor .eax (.reg .edx)]) w'
      fun x => x.gpr .eax = b.setWidth 32 ∧ x.gpr .ecx = w.gpr .ecx ∧ x.gpr .ebp = s.gpr .ebp ∧
        x.gpr .edi = s.gpr .edi ∧ x.mem = s.mem ∧ x.wr = s.wr := by
    have w'ax : w'.gpr .eax = (b ^^^ v).setWidth 32 :=
      (w'k.gpr (by decide)).trans (wax.trans uax)
    rrun [w'ax, w'dx, w'm, wm, um, (w'k.gpr (r := .ecx) (by decide)),
      (w'k.gpr (r := .ebp) (by decide)).trans wbp, (w'k.gpr (r := .edi) (by decide)).trans wdi,
      w'k.2.2, wwr]
    rw [xor_byte32, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  refine WP.mono h2 fun x ⟨xax, xcx, xbp, xdi, xm, xwr⟩ => ?_
  refine WP.mono (WP.keep [.edx] (scatter_steps s idx _ hbp hfit hw 64 (by decide) x rfl xbp xdi
    xwr xm) (by decide +kernel)) fun y ⟨⟨ym, _⟩, yk⟩ => ?_
  refine ⟨(yk.gpr (by decide)).trans xax, ?_⟩
  rw [ym, xcx, wcx]
  unfold scatter spread
  rw [ite_eq_left (by omega_using []), ite_eq_left (Nat.zero_le _), Nat.sub_zero, writeW_byte32,
    ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

end VG.Proof.Rc4.X86

end

end

/-! ### `Rc4.X86.Save`, which this module and modules that import it used -/

section

/-! # RC4 on x86 (32-bit): our caller's registers, saved in `scratch` -/

@[expose] public section

namespace VG.Proof.Rc4.X86
open VG VG.X86 VG.Impl.Rc4.X86 VG.Proof.Rc4
open VG.Proof.MlDsa.X86.Pack (Keep WP.keep writesOnly addr_of_fit)

/-- The memory once `save` has stored `b`, `si`, `di` and `bp` at `S`. -/
def savedMem (m : Mem) (S : BitVec 32) (b si di bp : BitVec 32) : Mem :=
  (((m.writeW (S.setWidth 64 + BitVec.ofNat 64 0) b).writeW (S.setWidth 64 + BitVec.ofNat 64 4) si).writeW
    (S.setWidth 64 + BitVec.ofNat 64 8) di).writeW (S.setWidth 64 + BitVec.ofNat 64 12) bp

/-- Our caller's `ebx`, `esi`, `edi` and `ebp` (of `s₀`) are at `S` in `m`. -/
def Saved (m : Mem) (S : BitVec 32) (s₀ : State) : Prop :=
  m.readW (S.setWidth 64 + BitVec.ofNat 64 0) 32 = s₀.gpr .ebx ∧
    m.readW (S.setWidth 64 + BitVec.ofNat 64 4) 32 = s₀.gpr .esi ∧
    m.readW (S.setWidth 64 + BitVec.ofNat 64 8) 32 = s₀.gpr .edi ∧
    m.readW (S.setWidth 64 + BitVec.ofNat 64 12) 32 = s₀.gpr .ebp

theorem save_addr {S : BitVec 32} (hS : S.toNat + 64 ≤ 2 ^ 32) {d : Nat} (hd : d < 64) :
    addr S d = S.setWidth 64 + BitVec.ofNat 64 d := addr_of_fit (by omega_using [hS, hd])

theorem save_ok (s : State) (S : BitVec 32) (hS : S.toNat + 64 ≤ 2 ^ 32)
    (ha : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 16) 4)
    (hv : s.mem.readW (addr (s.gpr .esp) 16) 32 = S)
    (hw : InRegions s.wr (S.setWidth 64) 64) :
    WP isa (.block save) s fun t =>
      t.mem = savedMem s.mem S (s.gpr .ebx) (s.gpr .esi) (s.gpr .edi) (s.gpr .ebp) ∧
      Keep [.ecx] s t := by
  have w (d : Nat) (hd : d + 4 ≤ 64) : InRegions s.wr (addr S d) 4 := by
    rw [save_addr hS (by omega_using [hd])]
    exact region_offset _ _ _ _ _ (by omega_using [hd]) hd hw
  have w0 := w 0 (by decide)
  have w4 := w 4 (by decide)
  have w8 := w 8 (by decide)
  have w12 := w 12 (by decide)
  rw [save_addr hS (by decide)] at w0 w4 w8 w12
  refine WP.mono (WP.keep (Q := fun t =>
      t.mem = savedMem s.mem S (s.gpr .ebx) (s.gpr .esi) (s.gpr .edi) (s.gpr .ebp)) [.ecx] ?_
    (by decide +kernel)) fun t ⟨h, hk⟩ => ⟨h, hk⟩
  unfold save
  rrun [ha, hv, save_addr hS, w0, w4, w8, w12]
  rfl

theorem saved_sep (S : BitVec 32) {d e : Nat} (h : d + 4 ≤ e ∨ e + 4 ≤ d) (hd : d < 64)
    (he : e < 64) :
    Mem.Sep (S.setWidth 64 + BitVec.ofNat 64 d) (32 / 8) (S.setWidth 64 + BitVec.ofNat 64 e)
      (32 / 8) :=
  Offset.sep _ h (by omega_using [hd]) (by omega_using [he])

theorem saved_savedMem (m : Mem) (S : BitVec 32) (s₀ : State) :
    Saved (savedMem m S (s₀.gpr .ebx) (s₀.gpr .esi) (s₀.gpr .edi) (s₀.gpr .ebp)) S s₀ := by
  unfold savedMem Saved
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Mem.readW_writeW_sep (saved_sep S (d := 0) (e := 12) (by omega_using []) (by omega_using []) (by omega_using []))
      (by decide), Mem.readW_writeW_sep (saved_sep S (d := 0) (e := 8) (by omega_using []) (by omega_using [])
      (by omega_using [])) (by decide), Mem.readW_writeW_sep (saved_sep S (d := 0) (e := 4) (by omega_using [])
      (by omega_using []) (by omega_using [])) (by decide), Mem.readW_writeW_self32]
  · rw [Mem.readW_writeW_sep (saved_sep S (d := 4) (e := 12) (by omega_using []) (by omega_using []) (by omega_using []))
      (by decide), Mem.readW_writeW_sep (saved_sep S (d := 4) (e := 8) (by omega_using []) (by omega_using [])
      (by omega_using [])) (by decide), Mem.readW_writeW_self32]
  · rw [Mem.readW_writeW_sep (saved_sep S (d := 8) (e := 12) (by omega_using []) (by omega_using []) (by omega_using []))
      (by decide), Mem.readW_writeW_self32]
  · rw [Mem.readW_writeW_self32]

/-- What `save` writes lies within `scratch`. -/
theorem savedMem_frame (m : Mem) (S : BitVec 32) (b si di bp : BitVec 32) :
    Frame [⟨S.setWidth 64, 64⟩] m (savedMem m S b si di bp) := by
  unfold savedMem
  refine Frame.writeW ?_ (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  refine Frame.writeW ?_ (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  refine Frame.writeW ?_ (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (Offset.contains_base _ (by decide) (by decide))

/-- The saved registers survive writes outside their 16 bytes. -/
theorem Saved.frame {m m' : Mem} {S : BitVec 32} {s₀ : State} {rs : List Region}
    (h : Saved m S s₀) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨S.setWidth 64, 16⟩ r) : Saved m' S s₀ := by
  have e (d : Nat) (hd' : d + 4 ≤ 16) :
      m'.readW (S.setWidth 64 + BitVec.ofNat 64 d) 32 = m.readW (S.setWidth 64 + BitVec.ofNat 64 d) 32 :=
    hf.readW (Offset.contains_base _ hd' (by omega_using [hd'])) hd (by decide)
  obtain ⟨h0, h4, h8, h12⟩ := h
  exact ⟨(e 0 (by decide)).trans h0, (e 4 (by decide)).trans h4, (e 8 (by decide)).trans h8,
    (e 12 (by decide)).trans h12⟩

theorem restore_ok (s₀ s : State) (S : BitVec 32) (hS : S.toNat + 64 ≤ 2 ^ 32)
    (ha : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 16) 4)
    (hv : s.mem.readW (addr (s.gpr .esp) 16) 32 = S)
    (hr : InRegions (s.rd ++ s.wr) (S.setWidth 64) 64) (hs : Saved s.mem S s₀) :
    WP isa (.block restore) s fun t =>
      t.gpr .ebx = s₀.gpr .ebx ∧ t.gpr .esi = s₀.gpr .esi ∧ t.gpr .edi = s₀.gpr .edi ∧
      t.gpr .ebp = s₀.gpr .ebp ∧ t.mem = s.mem ∧ Keep [.ecx, .ebx, .esi, .edi, .ebp] s t := by
  have r (d : Nat) (hd : d + 4 ≤ 64) : InRegions (s.rd ++ s.wr) (addr S d) 4 := by
    rw [save_addr hS (by omega_using [hd])]
    exact region_offset _ _ _ _ _ (by omega_using [hd]) hd hr
  have r0 := r 0 (by decide)
  have r4 := r 4 (by decide)
  have r8 := r 8 (by decide)
  have r12 := r 12 (by decide)
  rw [save_addr hS (by decide)] at r0 r4 r8 r12
  obtain ⟨h0, h4, h8, h12⟩ := hs
  refine WP.mono (WP.keep (Q := fun t =>
      t.gpr .ebx = s₀.gpr .ebx ∧ t.gpr .esi = s₀.gpr .esi ∧ t.gpr .edi = s₀.gpr .edi ∧
      t.gpr .ebp = s₀.gpr .ebp ∧ t.mem = s.mem) [.ecx, .ebx, .esi, .edi, .ebp] ?_
    (by decide +kernel)) fun t ⟨h, hk⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, hk⟩
  unfold restore
  rrun [ha, hv, save_addr hS, r0, r4, r8, r12, h0, h4, h8, h12]

end VG.Proof.Rc4.X86

end

end

/-! ### `Rc4.X86.ApplyStep`, which only this module used -/

section

/-! # RC4 on x86 (32-bit): one PRGA step -/

@[expose] public section

namespace VG.Proof.Rc4.X86
open VG VG.X86 VG.Impl.Rc4.X86 VG.Spec.Rc4 VG.Proof.Rc4
open VG.Proof.MlDsa.X86.Pack (Keep WP.keep writesOnly addr_of_fit)

theorem apply_before (s : State) (i j : Byte)
    (hsi : s.gpr .esi = i.setWidth 32) (hbp : s.gpr .ebp = j.setWidth 32)
    (hfit : (s.gpr .edi).toNat + 256 ≤ 2 ^ 32)
    (hp : InRegions (s.rd ++ s.wr) ((s.gpr .edi).setWidth 64) 256) :
    WP isa (.block (([.alu .add .esi (imm 1), .alu .and .esi (imm 255)] : List Instr) ++ loadI ++
      ([.alu .add .ebp (.reg .edx), .alu .and .ebp (imm 255)] : List Instr))) s fun t =>
      t.gpr .esi = (i + 1#8).setWidth 32 ∧
      t.gpr .ebp = (j + s.mem ((s.gpr .edi).setWidth 64 +
        BitVec.ofNat 64 (i + 1#8).toNat)).setWidth 32 ∧
      Keep (([.esi] : List Reg) ++ ([.edx] : List Reg) ++ ([.ebp] : List Reg)) s t ∧ t.mem = s.mem := by
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep (Q := fun t => t.gpr .esi = (i + 1#8).setWidth 32 ∧ t.mem = s.mem)
    [.esi] (by rrun [hsi, byte_inc32]) (by decide +kernel)) fun t ⟨⟨tsi, tm⟩, tk⟩ => ?_
  obtain hft : (t.gpr .edi).toNat + 256 ≤ 2 ^ 32 := by rw [tk.gpr (by decide)]; exact hfit
  obtain hpt : InRegions (t.rd ++ t.wr) ((t.gpr .edi).setWidth 64) 256 := by
    rw [tk.2.1, tk.2.2, tk.gpr (by decide)]; exact hp
  refine WP.mono (loadI_ok t (i + 1#8) tsi hft hpt) fun u ⟨udx, uk, um⟩ => ?_
  obtain ubp : u.gpr .ebp = j.setWidth 32 := (uk.gpr (by decide)).trans ((tk.gpr (by decide)).trans hbp)
  rw [tm, tk.gpr (r := .edi) (by decide)] at udx
  refine WP.mono (WP.keep (Q := fun v => v.gpr .ebp = (j + s.mem ((s.gpr .edi).setWidth 64 +
      BitVec.ofNat 64 (i + 1#8).toNat)).setWidth 32 ∧ v.mem = u.mem) [.ebp]
    (by rrun [ubp, udx]; rw [byte_add32]) (by decide +kernel)) fun v ⟨⟨vbp, vm⟩, vk⟩ => ?_
  exact ⟨(vk.gpr (by decide)).trans ((uk.gpr (by decide)).trans tsi), vbp,
    (tk.trans uk).trans vk, vm.trans (um.trans tm)⟩

theorem apply_middle (s : State) (ii a b jj : Byte) (Sc : BitVec 32)
    (hsi : s.gpr .esi = ii.setWidth 32) (hax : s.gpr .eax = b.setWidth 32)
    (hdx : s.gpr .edx = a.setWidth 32) (hbp : s.gpr .ebp = jj.setWidth 32)
    (hfit : (s.gpr .edi).toNat + 256 ≤ 2 ^ 32) (hSfit : Sc.toNat + 64 ≤ 2 ^ 32)
    (hw : InRegions s.wr ((s.gpr .edi).setWidth 64 + BitVec.ofNat 64 ii.toNat) 1)
    (hw16 : InRegions s.wr (Sc.setWidth 64 + BitVec.ofNat 64 16) 4)
    (ha16 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 16) 4)
    (hv16 : (s.mem.write ((s.gpr .edi).setWidth 64 + BitVec.ofNat 64 ii.toNat) 1 b).readW
      (addr (s.gpr .esp) 16) 32 = Sc) :
    WP isa (.block [.mov .ecx (.reg .edi), .alu .add .ecx (.reg .esi), .store8 (at_ .ecx 0) .al,
      .alu .add .eax (.reg .edx), .alu .and .eax (imm 255),
      .mov .edx (.mem (at_ .esp 16)), .store (at_ .edx 16) .ebp, .mov .ebp (.reg .eax)]) s
      fun t => t.mem = (s.mem.write ((s.gpr .edi).setWidth 64 + BitVec.ofNat 64 ii.toNat) 1 b).writeW
          (Sc.setWidth 64 + BitVec.ofNat 64 16) (jj.setWidth 32) ∧
        t.gpr .ebp = (b + a).setWidth 32 ∧ Keep [.eax, .ecx, .edx, .ebp] s t := by
  obtain he := idx_addr hfit ii
  obtain h16 : addr Sc 16 = Sc.setWidth 64 + BitVec.ofNat 64 16 := save_addr hSfit (by decide)
  have hr16 : InRegions ((s.rd ++ s.wr)) (addr (s.gpr .esp) 16) 4 := ha16
  refine WP.mono (WP.keep (Q := fun t =>
      t.mem = (s.mem.write ((s.gpr .edi).setWidth 64 + BitVec.ofNat 64 ii.toNat) 1 b).writeW
          (Sc.setWidth 64 + BitVec.ofNat 64 16) (jj.setWidth 32) ∧
        t.gpr .ebp = (b + a).setWidth 32) [.eax, .ecx, .edx, .ebp] ?_ (by decide +kernel))
    fun t ⟨h, hk⟩ => ⟨h.1, h.2, hk⟩
  rrun [hsi, hax, hdx, hbp, he, hw, writeW_byte8, low_byte32, hr16, hv16, h16, hw16, byte_add32]

theorem apply_after (s : State) (k : Byte) (Sc D L : BitVec 32) (n : Nat)
    (hax : s.gpr .eax = k.setWidth 32) (hbx : s.gpr .ebx = BitVec.ofNat 32 n)
    (hSfit : Sc.toNat + 64 ≤ 2 ^ 32) (hDfit : D.toNat + n < 2 ^ 32)
    (ha16 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 16) 4)
    (hv16 : s.mem.readW (addr (s.gpr .esp) 16) 32 = Sc)
    (hr16 : InRegions (s.rd ++ s.wr) (Sc.setWidth 64 + BitVec.ofNat 64 16) 4)
    (ha8 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 8) 4)
    (hv8 : s.mem.readW (addr (s.gpr .esp) 8) 32 = D)
    (hd : InRegions s.wr (D.setWidth 64 + BitVec.ofNat 64 n) 1)
    (ha12 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 12) 4)
    (hv12 : ∀ v, (s.mem.write (D.setWidth 64 + BitVec.ofNat 64 n) 1 v).readW
      (addr (s.gpr .esp) 12) 32 = L) :
    WP isa (.block [.mov .edx (.mem (at_ .esp 16)), .mov .ebp (.mem (at_ .edx 16)),
      .mov .edx (.mem (at_ .esp 8)), .alu .add .edx (.reg .ebx), .movzx8 .ecx (at_ .edx 0),
      .alu .xor .ecx (.reg .eax), .store8 (at_ .edx 0) .cl,
      .alu .add .ebx (imm 1), .mov .edx (.mem (at_ .esp 12)), .alu .cmp .ebx (.reg .edx)]) s
      fun t => t.mem = s.mem.write (D.setWidth 64 + BitVec.ofNat 64 n) 1
          (s.mem (D.setWidth 64 + BitVec.ofNat 64 n) ^^^ k) ∧
        t.gpr .ebp = s.mem.readW (Sc.setWidth 64 + BitVec.ofNat 64 16) 32 ∧
        t.gpr .ebx = BitVec.ofNat 32 (n + 1) ∧
        t.zf = some (BitVec.ofNat 32 (n + 1) - L == 0#32) ∧ Keep [.ecx, .edx, .ebx, .ebp] s t := by
  obtain h16 : addr Sc 16 = Sc.setWidth 64 + BitVec.ofNat 64 16 := save_addr hSfit (by decide)
  obtain hdn : addr (D + BitVec.ofNat 32 n) 0 = D.setWidth 64 + BitVec.ofNat 64 n := by
    unfold addr
    rw [BitVec.add_zero]
    exact VG.Proof.MlKem.X86.ea_off hDfit
  obtain hdr : InRegions (s.rd ++ s.wr) (D.setWidth 64 + BitVec.ofNat 64 n) 1 := by
    obtain ⟨r, hr, hc⟩ := hd
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  obtain hadd : BitVec.ofNat 32 n + BitVec.ofNat 32 1 = BitVec.ofNat 32 (n + 1) := by
    rw [← BitVec.ofNat_add]
  refine WP.mono (WP.keep (Q := fun t =>
      t.mem = s.mem.write (D.setWidth 64 + BitVec.ofNat 64 n) 1
          (s.mem (D.setWidth 64 + BitVec.ofNat 64 n) ^^^ k) ∧
        t.gpr .ebp = s.mem.readW (Sc.setWidth 64 + BitVec.ofNat 64 16) 32 ∧
        t.gpr .ebx = BitVec.ofNat 32 (n + 1) ∧
        t.zf = some (BitVec.ofNat 32 (n + 1) - L == 0#32)) [.ecx, .edx, .ebx, .ebp] ?_
    (by decide +kernel)) fun t ⟨h, hk⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, hk⟩
  rrun [hax, hbx, ha16, hv16, h16, hr16, ha8, hv8, hdn, hdr, hd, writeW_byte8, low_xor32, hadd,
    ha12, hv12]
  rfl

/-- What a step of the stream function needs of its state: the table at `P`,
the `L` bytes of data at `D`, `scratch` at `Sc`, the arguments readable and
apart from what the step writes. -/
structure StepEnv (s : State) (P D L Sc : BitVec 32) : Prop where
  p : s.gpr .edi = P
  pfit : P.toNat + 258 ≤ 2 ^ 32
  sfit : Sc.toNat + 64 ≤ 2 ^ 32
  dfit : D.toNat + L.toNat ≤ 2 ^ 32
  table : InRegions s.wr (P.setWidth 64) 256
  spill : InRegions s.wr (Sc.setWidth 64 + BitVec.ofNat 64 16) 4
  data : InRegions s.wr (D.setWidth 64) L.toNat
  a8 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 8) 4
  a12 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 12) 4
  a16 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 16) 4
  v8 : s.mem.readW (addr (s.gpr .esp) 8) 32 = D
  v12 : s.mem.readW (addr (s.gpr .esp) 12) 32 = L
  v16 : s.mem.readW (addr (s.gpr .esp) 16) 32 = Sc
  s8T : Mem.Sep (addr (s.gpr .esp) 8) 4 (P.setWidth 64) 256
  s12T : Mem.Sep (addr (s.gpr .esp) 12) 4 (P.setWidth 64) 256
  s16T : Mem.Sep (addr (s.gpr .esp) 16) 4 (P.setWidth 64) 256
  s8S : Mem.Sep (addr (s.gpr .esp) 8) 4 (Sc.setWidth 64 + BitVec.ofNat 64 16) 4
  s12S : Mem.Sep (addr (s.gpr .esp) 12) 4 (Sc.setWidth 64 + BitVec.ofNat 64 16) 4
  s16S : Mem.Sep (addr (s.gpr .esp) 16) 4 (Sc.setWidth 64 + BitVec.ofNat 64 16) 4
  s8D : Mem.Sep (addr (s.gpr .esp) 8) 4 (D.setWidth 64) L.toNat
  s12D : Mem.Sep (addr (s.gpr .esp) 12) 4 (D.setWidth 64) L.toNat
  s16D : Mem.Sep (addr (s.gpr .esp) 16) 4 (D.setWidth 64) L.toNat
  sTS : Mem.Sep (P.setWidth 64) 256 (Sc.setWidth 64 + BitVec.ofNat 64 16) 4
  sTD : Mem.Sep (P.setWidth 64) 256 (D.setWidth 64) L.toNat
  sSD : Mem.Sep (Sc.setWidth 64 + BitVec.ofNat 64 16) 4 (D.setWidth 64) L.toNat

theorem readW_writeW_sep4 {m : Mem} {a q : Addr} {v : BitVec 32} (h : Mem.Sep a 4 q 4) :
    (m.writeW q v).readW a 32 = m.readW a 32 := Mem.readW_writeW_sep h (by decide)

/-- One iteration, with the writes expressed against the original memory.
Both swap operands are read before either write, including for a self-swap. -/
theorem apply_step (s : State) (i j : Byte) (P D L Sc : BitVec 32) (n : Nat)
    (hsi : s.gpr .esi = i.setWidth 32) (hbp : s.gpr .ebp = j.setWidth 32)
    (hbx : s.gpr .ebx = BitVec.ofNat 32 n) (hn : n < L.toNat) (he : StepEnv s P D L Sc) :
    let p := P.setWidth 64
    let ii := i + 1#8
    let a := s.mem (p + BitVec.ofNat 64 ii.toNat)
    let jj := j + a
    let b := s.mem (p + BitVec.ofNat 64 jj.toNat)
    let swapped := (s.mem.write (p + BitVec.ofNat 64 jj.toNat) 1 a).write
      (p + BitVec.ofNat 64 ii.toNat) 1 b
    let m₂ := swapped.writeW (Sc.setWidth 64 + BitVec.ofNat 64 16) (jj.setWidth 32)
    let k := swapped (p + BitVec.ofNat 64 (a + b).toNat)
    WP isa (.block applyStep) s fun t =>
      t.mem = m₂.write (D.setWidth 64 + BitVec.ofNat 64 n) 1
        (m₂ (D.setWidth 64 + BitVec.ofNat 64 n) ^^^ k) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.gpr .edi = P ∧ t.gpr .esp = s.gpr .esp ∧
      t.gpr .esi = ii.setWidth 32 ∧ t.gpr .ebp = jj.setWidth 32 ∧
      t.gpr .ebx = BitVec.ofNat 32 (n + 1) ∧
      t.zf = some (BitVec.ofNat 32 (n + 1) - L == 0#32) := by
  intro p ii a jj b swapped m₂ k
  obtain hfit : (s.gpr .edi).toNat + 256 ≤ 2 ^ 32 := by rw [he.p]; have := he.pfit; omega_using [this]
  obtain hp : InRegions s.wr ((s.gpr .edi).setWidth 64) 256 := by rw [he.p]; exact he.table
  obtain hr : InRegions (s.rd ++ s.wr) ((s.gpr .edi).setWidth 64) 256 := by
    obtain ⟨r, hr, hc⟩ := hp
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  obtain hrP : InRegions (s.rd ++ s.wr) (P.setWidth 64) 256 := by
    obtain ⟨r, hr, hc⟩ := he.table
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have argT {o : Nat} (h : Mem.Sep (addr (s.gpr .esp) o) 4 p 256) (x : Byte) :
      Mem.Sep (addr (s.gpr .esp) o) 4 (p + BitVec.ofNat 64 x.toNat) 1 :=
    sep_offset_right h (by have := x.isLt; omega_using []) (by have := x.isLt; omega_using [])
  simp only [applyStep, List.append_assoc]
  rw [← List.append_assoc, ← List.append_assoc, WP.block_append_iff]
  refine WP.mono (apply_before s i j hsi hbp hfit hr) fun t ⟨tsi, tbp, tk, tm⟩ => ?_
  rw [he.p] at tbp
  obtain tdi : t.gpr .edi = P := (tk.gpr (by decide)).trans he.p
  obtain tsp : t.gpr .esp = s.gpr .esp := tk.gpr (by decide)
  obtain tbx : t.gpr .ebx = BitVec.ofNat 32 n := (tk.gpr (by decide)).trans hbx
  obtain htp : InRegions t.wr ((t.gpr .edi).setWidth 64) 256 := by rw [tk.2.2, tdi]; exact he.table
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.eax, .ecx, .edx]
    (replace_core t jj ii tbp tsi (by rw [tdi]; have := he.pfit; omega_using [this]) htp) (by decide +kernel))
    fun u ⟨⟨uax, um⟩, uk⟩ => ?_
  rw [tm, tdi] at uax um
  obtain usi : u.gpr .esi = ii.setWidth 32 := (uk.gpr (by decide)).trans tsi
  obtain udi : u.gpr .edi = P := (uk.gpr (by decide)).trans tdi
  obtain usp : u.gpr .esp = s.gpr .esp := (uk.gpr (by decide)).trans tsp
  obtain ubp : u.gpr .ebp = jj.setWidth 32 := (uk.gpr (by decide)).trans tbp
  obtain ubx : u.gpr .ebx = BitVec.ofNat 32 n := (uk.gpr (by decide)).trans tbx
  obtain urd : u.rd = s.rd := uk.2.1.trans tk.2.1
  obtain uwr : u.wr = s.wr := uk.2.2.trans tk.2.2
  rw [WP.block_append_iff]
  refine WP.mono (loadI_ok u ii usi (by rw [udi]; have := he.pfit; omega_using [this])
    (by rw [urd, uwr, udi]; exact hrP)) fun v ⟨vdx, vk, vm⟩ => ?_
  obtain ha : u.mem (p + BitVec.ofNat 64 ii.toNat) = a := by
    rw [um, write_byte]
    split <;> rfl
  rw [udi, ha] at vdx
  obtain vax : v.gpr .eax = b.setWidth 32 := (vk.gpr (by decide)).trans uax
  obtain vsi : v.gpr .esi = ii.setWidth 32 := (vk.gpr (by decide)).trans usi
  obtain vbp : v.gpr .ebp = jj.setWidth 32 := (vk.gpr (by decide)).trans ubp
  obtain vdi : v.gpr .edi = P := (vk.gpr (by decide)).trans udi
  obtain vsp : v.gpr .esp = s.gpr .esp := (vk.gpr (by decide)).trans usp
  obtain vrd : v.rd = s.rd := vk.2.1.trans urd
  obtain vwr : v.wr = s.wr := vk.2.2.trans uwr
  rw [WP.block_append_iff]
  obtain hw : InRegions v.wr ((v.gpr .edi).setWidth 64 + BitVec.ofNat 64 ii.toNat) 1 := by
    rw [vwr, vdi]
    exact region_offset _ _ _ _ _ (by have := ii.isLt; omega_using []) (by have := ii.isLt; omega_using []) he.table
  refine WP.mono (apply_middle v ii a b jj Sc vsi vax vdx vbp (by rw [vdi]; have := he.pfit; omega_using [this])
    he.sfit hw (by rw [vwr]; exact he.spill) (by rw [vrd, vwr, vsp]; exact he.a16)
    (by rw [vm, um, vsp, vdi, readW_write2 (argT he.s16T jj) (argT he.s16T ii)]; exact he.v16))
    fun w ⟨wm, wbp, wk⟩ => ?_
  rw [vm, um, vdi] at wm
  have hwm : w.mem = m₂ := wm
  obtain wdi : w.gpr .edi = P := (wk.gpr (by decide)).trans vdi
  obtain wsp : w.gpr .esp = s.gpr .esp := (wk.gpr (by decide)).trans vsp
  obtain wsi : w.gpr .esi = ii.setWidth 32 := (wk.gpr (by decide)).trans vsi
  obtain wbx : w.gpr .ebx = BitVec.ofNat 32 n :=
    (wk.gpr (by decide)).trans ((vk.gpr (by decide)).trans ubx)
  obtain wrd : w.rd = s.rd := wk.2.1.trans vrd
  obtain wwr : w.wr = s.wr := wk.2.2.trans vwr
  obtain wbp' : w.gpr .ebp = (a + b).setWidth 32 := by rw [wbp, BitVec.add_comm]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.eax, .ecx, .edx] (lookup_core w (a + b) wbp'
    (by rw [wdi]; have := he.pfit; omega_using [this]) (by rw [wrd, wwr, wdi]; exact hrP))
    (by decide +kernel)) fun x ⟨⟨xax, xm⟩, xk⟩ => ?_
  obtain hk : w.mem ((w.gpr .edi).setWidth 64 + BitVec.ofNat 64 (a + b).toNat) = k := by
    rw [hwm, wdi]
    apply Mem.write_apply
    exact he.sTS _ (by rw [Mem.sub_ofNat_toNat _ (by omega_using [])]; exact (a + b).isLt)
  rw [hk] at xax
  obtain xsp : x.gpr .esp = s.gpr .esp := (xk.gpr (by decide)).trans wsp
  obtain xrd : x.rd = s.rd := xk.2.1.trans wrd
  obtain xwr : x.wr = s.wr := xk.2.2.trans wwr
  have hm2 (o : Nat) (hT : Mem.Sep (addr (s.gpr .esp) o) 4 p 256)
      (hS : Mem.Sep (addr (s.gpr .esp) o) 4 (Sc.setWidth 64 + BitVec.ofNat 64 16) 4) :
      m₂.readW (addr (s.gpr .esp) o) 32 = s.mem.readW (addr (s.gpr .esp) o) 32 := by
    rw [readW_writeW_sep4 hS, readW_write2 (argT hT jj) (argT hT ii)]
  have hdn : n < L.toNat := hn
  refine WP.mono (apply_after x k Sc D L n xax ((xk.gpr (by decide)).trans wbx) he.sfit
    (by have := he.dfit; omega_using [hn, this])
    (by rw [xrd, xwr, xsp]; exact he.a16) (by rw [xm, hwm, xsp, hm2 16 he.s16T he.s16S]; exact he.v16)
    (by rw [xrd, xwr]; obtain ⟨r, hr', hc⟩ := he.spill; exact ⟨r, List.mem_append_right _ hr', hc⟩)
    (by rw [xrd, xwr, xsp]; exact he.a8) (by rw [xm, hwm, xsp, hm2 8 he.s8T he.s8S]; exact he.v8)
    (by rw [xwr]; exact region_offset _ _ _ _ _ (by omega_using [hn]) (by omega_using [hn]) he.data)
    (by rw [xrd, xwr, xsp]; exact he.a12)
    (fun v => by
      rw [xm, hwm, xsp, readW_write1 (sep_offset_right he.s12D (by omega_using [hn]) (by omega_using [hn])),
        hm2 12 he.s12T he.s12S]
      exact he.v12)) fun y ⟨ym, ybp, ybx, yz, yk⟩ => ?_
  refine ⟨by rw [ym, xm, hwm], yk.2.1.trans xrd, yk.2.2.trans xwr,
    (yk.gpr (by decide)).trans ((xk.gpr (by decide)).trans wdi), (yk.gpr (by decide)).trans xsp,
    (yk.gpr (by decide)).trans ((xk.gpr (by decide)).trans wsi), ?_, ybx, yz⟩
  rw [ybp, xm, hwm]
  exact Mem.readW_writeW_self32 _ _ _

end VG.Proof.Rc4.X86

end

end


/-! # RC4 on x86 (32-bit): the stream loop -/

@[expose] public section

namespace VG.Proof.Rc4.X86
open VG VG.X86 VG.Impl.Rc4.X86 VG.Spec.Rc4 VG.Proof.Rc4
open VG.Proof.MlDsa.X86.Pack (Keep WP.keep writesOnly addr_of_fit)

/-- `vg_rc4_apply(ctx, data, len, scratch)`: what its proof needs on entry. -/
structure ApplyPre (s : State) (P D L Sc : BitVec 32) : Prop where
  aP : arg s 0 = P
  aD : arg s 1 = D
  aL : arg s 2 = L
  aS : arg s 3 = Sc
  args : InRegions s.rd (argAddr s 0) 16
  ctx : InRegions s.wr (P.setWidth 64) 258
  data : InRegions s.wr (D.setWidth 64) L.toNat
  scratch : InRegions s.wr (Sc.setWidth 64) 64
  ctxFit : P.toNat + 258 ≤ 2 ^ 32
  dataFit : D.toNat + L.toNat ≤ 2 ^ 32
  scratchFit : Sc.toNat + 64 ≤ 2 ^ 32
  spFit : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32
  ctxData : Region.Disjoint ⟨P.setWidth 64, 258⟩ ⟨D.setWidth 64, L.toNat⟩
  ctxScratch : Region.Disjoint ⟨P.setWidth 64, 258⟩ ⟨Sc.setWidth 64, 64⟩
  dataScratch : Region.Disjoint ⟨D.setWidth 64, L.toNat⟩ ⟨Sc.setWidth 64, 64⟩
  argsCtx : Region.Disjoint ⟨argAddr s 0, 16⟩ ⟨P.setWidth 64, 258⟩
  argsData : Region.Disjoint ⟨argAddr s 0, 16⟩ ⟨D.setWidth 64, L.toNat⟩
  argsScratch : Region.Disjoint ⟨argAddr s 0, 16⟩ ⟨Sc.setWidth 64, 64⟩

/-- What the function writes: the context, the data and `scratch`. -/
def applyRegions (P D L Sc : BitVec 32) : List Region :=
  [⟨P.setWidth 64, 258⟩, ⟨D.setWidth 64, L.toNat⟩, ⟨Sc.setWidth 64, 64⟩]

/-- What the stream loop writes: the table, `scratch[16]` and the data. -/
def loopRegions (P D L Sc : BitVec 32) : List Region :=
  [⟨P.setWidth 64, 256⟩, ⟨Sc.setWidth 64 + BitVec.ofNat 64 16, 4⟩, ⟨D.setWidth 64, L.toNat⟩]

theorem loop_sub_apply (P D L Sc : BitVec 32) :
    ∀ r ∈ loopRegions P D L Sc, ∃ r' ∈ applyRegions P D L Sc, Region.Sub r r' := by
  intro r hr
  simp only [loopRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
      Offset.sub_base _ (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Region.sub_prefix (Nat.le_refl _)⟩

theorem arg_contains' {s : State} (hsp : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32) {i : Nat} (hi : i < 4) :
    (⟨argAddr s 0, 16⟩ : Region).Contains (argAddr s i) 4 := by
  obtain h : argAddr s i = argAddr s 0 + BitVec.ofNat 64 (4 * i) := by
    unfold argAddr
    rw [VG.Proof.MlKem.X86.ea_off (by omega_using [hsp, hi]), VG.Proof.MlKem.X86.ea_off (by omega_using [hsp]),
      BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [h]
  exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])

namespace ApplyPre

variable {s : State} {P D L Sc : BitVec 32}

theorem arg_in (hp : ApplyPre s P D L Sc) {i : Nat} (hi : i < 4) :
    InRegions (s.rd ++ s.wr) (argAddr s i) 4 := by
  obtain ⟨r, hr, hc⟩ := hp.args
  obtain hc' := arg_contains' hp.spFit hi
  refine ⟨r, List.mem_append_left _ hr, ?_⟩
  simp only [Region.Contains] at hc hc' ⊢
  rw [← Offset.sub_add_sub_cancel (argAddr s i) (argAddr s 0) r.base, BitVec.toNat_add]
  omega_using [hc, hc']

theorem arg_disjoint (hp : ApplyPre s P D L Sc) :
    ∀ r ∈ applyRegions P D L Sc, Region.Disjoint ⟨argAddr s 0, 16⟩ r := by
  intro r hr
  simp only [applyRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.argsCtx
  · exact hp.argsData
  · exact hp.argsScratch

theorem arg_eq (hp : ApplyPre s P D L Sc) {m : Mem} (hf : Frame (applyRegions P D L Sc) s.mem m)
    {i : Nat} (hi : i < 4) : m.readW (argAddr s i) 32 = arg s i :=
  hf.readW (arg_contains' hp.spFit hi) hp.arg_disjoint (by decide)

/-- What a stream iteration needs, from what the function's memory keeps. -/
theorem env {t : State} (hp : ApplyPre s P D L Sc) (hf : Frame (applyRegions P D L Sc) s.mem t.mem)
    (hsp : t.gpr .esp = s.gpr .esp) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr)
    (hdi : t.gpr .edi = P) : StepEnv t P D L Sc := by
  have ac (i : Nat) (hi : i < 4) := arg_contains' hp.spFit (s := s) hi
  obtain hT : (⟨P.setWidth 64, 258⟩ : Region).Contains (P.setWidth 64) 256 :=
    contains_prefix _ (by decide)
  obtain hS : (⟨Sc.setWidth 64, 64⟩ : Region).Contains (Sc.setWidth 64 + BitVec.ofNat 64 16) 4 :=
    Offset.contains_base _ (by decide) (by decide)
  obtain hD : (⟨D.setWidth 64, L.toNat⟩ : Region).Contains (D.setWidth 64) L.toNat :=
    contains_prefix _ (Nat.le_refl _)
  refine
    { p := hdi
      pfit := by have := hp.ctxFit; omega_using [this]
      sfit := hp.scratchFit
      dfit := hp.dataFit
      table := ?_
      spill := by rw [hwr]; exact region_offset _ _ _ 16 4 (by decide) (by decide) hp.scratch
      data := by rw [hwr]; exact hp.data
      a8 := by rw [hrd, hwr, hsp]; exact hp.arg_in (i := 1) (by decide)
      a12 := by rw [hrd, hwr, hsp]; exact hp.arg_in (i := 2) (by decide)
      a16 := by rw [hrd, hwr, hsp]; exact hp.arg_in (i := 3) (by decide)
      v8 := by rw [hsp]; exact (hp.arg_eq hf (i := 1) (by decide)).trans hp.aD
      v12 := by rw [hsp]; exact (hp.arg_eq hf (i := 2) (by decide)).trans hp.aL
      v16 := by rw [hsp]; exact (hp.arg_eq hf (i := 3) (by decide)).trans hp.aS
      s8T := by rw [hsp]; exact sep_of_sub hp.argsCtx (ac 1 (by decide)) hT
      s12T := by rw [hsp]; exact sep_of_sub hp.argsCtx (ac 2 (by decide)) hT
      s16T := by rw [hsp]; exact sep_of_sub hp.argsCtx (ac 3 (by decide)) hT
      s8S := by rw [hsp]; exact sep_of_sub hp.argsScratch (ac 1 (by decide)) hS
      s12S := by rw [hsp]; exact sep_of_sub hp.argsScratch (ac 2 (by decide)) hS
      s16S := by rw [hsp]; exact sep_of_sub hp.argsScratch (ac 3 (by decide)) hS
      s8D := by rw [hsp]; exact sep_of_sub hp.argsData (ac 1 (by decide)) hD
      s12D := by rw [hsp]; exact sep_of_sub hp.argsData (ac 2 (by decide)) hD
      s16D := by rw [hsp]; exact sep_of_sub hp.argsData (ac 3 (by decide)) hD
      sTS := sep_of_sub hp.ctxScratch hT hS
      sTD := sep_of_sub hp.ctxData hT hD
      sSD := sep_of_sub hp.dataScratch.symm hS hD }
  rw [hwr]
  obtain h := region_offset _ _ _ 0 256 (by decide) (by decide) hp.ctx
  simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h

end ApplyPre

/-- The context and output after the first `k` data bytes. -/
def upd (s : State) (P D : BitVec 32) (k : Nat) : Context × List Byte :=
  update (contextAt s.mem (P.setWidth 64)) (bytesAt s.mem (D.setWidth 64) k)

theorem upd_succ (s : State) (P D : BitVec 32) (k : Nat) :
    upd s P D (k + 1) = ((step (upd s P D k).1).1, (upd s P D k).2 ++
      [s.mem (D.setWidth 64 + BitVec.ofNat 64 k) ^^^ (step (upd s P D k).1).2]) := by
  unfold upd
  rw [bytes_snoc, update_snoc]

/-- The stream loop after `k` bytes, `m₁` being the memory it started from. -/
structure LoopInv (s : State) (P D L Sc : BitVec 32) (m₁ : Mem) (k : Nat) (t : State) : Prop where
  le : k ≤ L.toNat
  table : (contextAt t.mem (P.setWidth 64)).table = (upd s P D k).1.table
  i : t.gpr .esi = (upd s P D k).1.i.setWidth 32
  j : t.gpr .ebp = (upd s P D k).1.j.setWidth 32
  data : bytesAt t.mem (D.setWidth 64) k = (upd s P D k).2
  tail : ∀ x, k ≤ x → x < L.toNat →
    t.mem (D.setWidth 64 + BitVec.ofNat 64 x) = s.mem (D.setWidth 64 + BitVec.ofNat 64 x)
  frame : Frame (loopRegions P D L Sc) m₁ t.mem
  bx : t.gpr .ebx = BitVec.ofNat 32 k
  p : t.gpr .edi = P
  sp : t.gpr .esp = s.gpr .esp
  rd : t.rd = s.rd
  wr : t.wr = s.wr

/-- A byte outside the table, `scratch[16]` and the data byte an iteration writes. -/
theorem step_other {m : Mem} {p q d x : Addr} {ii jj : Byte} {v : BitVec 32} {w : Byte}
    (hT : ¬ (x - p).toNat < 256) (hS : ¬ (x - q).toNat < 4) (hD : x ≠ d) :
    ((((m.write (p + BitVec.ofNat 64 jj.toNat) 1 (m (p + BitVec.ofNat 64 ii.toNat))).write
      (p + BitVec.ofNat 64 ii.toNat) 1 (m (p + BitVec.ofNat 64 jj.toNat))).writeW q v).write d 1 w) x =
      m x := by
  rw [write_byte, ite_eq_right hD]
  unfold Mem.writeW
  rw [Mem.write_apply hS]
  exact swap_frame m p ii jj x hT

/-- The concrete stream iteration realizes the abstract PRGA transition. -/
theorem apply_step_table (t : State) (i j : Byte) (P D L Sc : BitVec 32) (k : Nat)
    (hsi : t.gpr .esi = i.setWidth 32) (hbp : t.gpr .ebp = j.setWidth 32)
    (hbx : t.gpr .ebx = BitVec.ofNat 32 k) (hk : k < L.toNat) (he : StepEnv t P D L Sc) :
    let next := step { table := (contextAt t.mem (P.setWidth 64)).table, i, j }
    WP isa (.block applyStep) t fun u =>
      (contextAt u.mem (P.setWidth 64)).table = next.1.table ∧
      u.gpr .esi = next.1.i.setWidth 32 ∧ u.gpr .ebp = next.1.j.setWidth 32 ∧
      u.mem (D.setWidth 64 + BitVec.ofNat 64 k) =
        t.mem (D.setWidth 64 + BitVec.ofNat 64 k) ^^^ next.2 ∧
      (∀ x, ¬ (x - P.setWidth 64).toNat < 256 →
        ¬ (x - (Sc.setWidth 64 + BitVec.ofNat 64 16)).toNat < 4 →
        x ≠ D.setWidth 64 + BitVec.ofNat 64 k → u.mem x = t.mem x) ∧
      Frame (loopRegions P D L Sc) t.mem u.mem ∧
      u.rd = t.rd ∧ u.wr = t.wr ∧ u.gpr .edi = P ∧ u.gpr .esp = t.gpr .esp ∧
      u.gpr .ebx = BitVec.ofNat 32 (k + 1) ∧
      u.zf = some (BitVec.ofNat 32 (k + 1) - L == 0#32) := by
  dsimp only
  rw [step_eq]
  dsimp only
  simp only [table_get]
  have hone : (1 : Byte) = 1#8 := rfl
  simp only [hone]
  refine WP.mono (apply_step t i j P D L Sc k hsi hbp hbx hk he)
    fun u ⟨hum, hurd, huwr, hudi, husp, husi, hubp, hubx, huz⟩ => ?_
  obtain hdk : ¬ (D.setWidth 64 + BitVec.ofNat 64 k - P.setWidth 64).toNat < 256 ∧
      ¬ (D.setWidth 64 + BitVec.ofNat 64 k - (Sc.setWidth 64 + BitVec.ofNat 64 16)).toNat < 4 := by
    obtain hin : (D.setWidth 64 + BitVec.ofNat 64 k - D.setWidth 64).toNat < L.toNat := by
      rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hk])]
      exact hk
    exact ⟨fun h => he.sTD _ h hin, fun h => he.sSD _ h hin⟩
  obtain hTD : Mem.Sep (P.setWidth 64) 256 (D.setWidth 64 + BitVec.ofNat 64 k) 1 :=
    sep_offset_right he.sTD (by omega_using [hk]) (by omega_using [hk])
  refine ⟨?_, husi, hubp, ?_, ?_, ?_, hurd, huwr, hudi, husp, hubx, huz⟩
  · rw [hum]
    unfold Mem.writeW
    rw [table_write_sep' _ _ _ _ hTD, table_write_sep' _ _ _ _ he.sTS, table_swap]
  · rw [hum, write_byte, ite_eq_left rfl]
    unfold Mem.writeW
    rw [Mem.write_apply hdk.2]
    rw [swap_frame _ _ _ _ _ hdk.1]
    obtain ht := table_swap t.mem (P.setWidth 64) (i + 1#8)
      (j + t.mem (P.setWidth 64 + BitVec.ofNat 64 (i + 1#8).toNat))
    rw [← ht, table_get]
  · intro x hT hS hD
    rw [hum]
    exact step_other hT hS hD
  · rw [hum]
    have hP : (⟨P.setWidth 64, 256⟩ : Region) ∈ loopRegions P D L Sc := List.mem_cons_self
    obtain hS : (⟨Sc.setWidth 64 + BitVec.ofNat 64 16, 4⟩ : Region) ∈ loopRegions P D L Sc :=
      List.mem_cons_of_mem _ List.mem_cons_self
    obtain hD : (⟨D.setWidth 64, L.toNat⟩ : Region) ∈ loopRegions P D L Sc :=
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    refine Frame.write ?_ hD _ (Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk]))
    refine Frame.writeW ?_ hS _ (contains_prefix _ (by decide))
    refine Frame.write ?_ hP _ (Offset.contains_base _ (by omega_using []) (by omega_using []))
    exact Frame.write (Frame.refl _ _) hP _ (Offset.contains_base _ (by omega_using []) (by omega_using []))

theorem loop_step (s : State) (P D L Sc : BitVec 32) (m₁ : Mem) (hp : ApplyPre s P D L Sc)
    (hb : Frame (applyRegions P D L Sc) s.mem m₁) {k : Nat} (hk : k < L.toNat) (t : State)
    (ht : LoopInv s P D L Sc m₁ k t) :
    WP isa (.block applyStep) t fun u => LoopInv s P D L Sc m₁ (k + 1) u ∧
      u.zf = some (BitVec.ofNat 32 (k + 1) - L == 0#32) := by
  obtain hft : Frame (applyRegions P D L Sc) s.mem t.mem :=
    hb.trans (ht.frame.sub (loop_sub_apply P D L Sc))
  obtain he := hp.env hft ht.sp ht.rd ht.wr ht.p
  obtain hsD : ∀ x, x < L.toNat →
      ¬ (D.setWidth 64 + BitVec.ofNat 64 x - P.setWidth 64).toNat < 256 ∧
      ¬ (D.setWidth 64 + BitVec.ofNat 64 x - (Sc.setWidth 64 + BitVec.ofNat 64 16)).toNat < 4 := by
    intro x hx
    obtain hin : (D.setWidth 64 + BitVec.ofNat 64 x - D.setWidth 64).toNat < L.toNat := by
      rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hx])]
      exact hx
    exact ⟨fun h => he.sTD _ h hin, fun h => he.sSD _ h hin⟩
  obtain hctx : (⟨(contextAt t.mem (P.setWidth 64)).table, (upd s P D k).1.i, (upd s P D k).1.j⟩ :
      Context) = (upd s P D k).1 := context_ext ht.table rfl rfl
  obtain hst := apply_step_table t (upd s P D k).1.i (upd s P D k).1.j P D L Sc k ht.i ht.j ht.bx hk he
  rw [hctx] at hst
  refine WP.mono hst fun u ⟨htab, hui, huj, hbyte, hother, hfr, hurd, huwr, hudi, husp, hubx, huz⟩ =>
    ⟨?_, huz⟩
  obtain hkeep : ∀ x, x < L.toNat → x ≠ k →
      u.mem (D.setWidth 64 + BitVec.ofNat 64 x) = t.mem (D.setWidth 64 + BitVec.ofNat 64 x) :=
    fun x hx hne => hother _ (hsD x hx).1 (hsD x hx).2 (data_ne hx hk hne)
  refine
    { le := hk
      table := by rw [upd_succ]; exact htab
      i := by rw [upd_succ]; exact hui
      j := by rw [upd_succ]; exact huj
      data := ?_
      tail := fun x hx hxL => by
        rw [hkeep x hxL (by omega_using [hx])]
        exact ht.tail x (by omega_using [hx]) hxL
      frame := ht.frame.trans hfr
      bx := hubx
      p := hudi
      sp := husp.trans ht.sp
      rd := hurd.trans ht.rd
      wr := huwr.trans ht.wr }
  rw [bytes_snoc, upd_succ, hbyte, ht.tail k (Nat.le_refl _) hk, ← ht.data]
  refine congrArg (· ++ _) ?_
  exact bytes_frame _ _ _ _ fun x hx => hkeep x (by omega_using [hk, hx]) (by omega_using [hx])

theorem apply_loop (s : State) (P D L Sc : BitVec 32) (m₁ : Mem) (hp : ApplyPre s P D L Sc)
    (hb : Frame (applyRegions P D L Sc) s.mem m₁) {k : Nat} (hk : k < L.toNat) (t : State)
    (ht : LoopInv s P D L Sc m₁ k t) :
    WP isa (.loop (.block applyStep) .ne) t (LoopInv s P D L Sc m₁ L.toNat) := by
  refine WP.loop (M := isa)
    (fun rem u => ∃ j, j < L.toNat ∧ rem = L.toNat - j ∧ LoopInv s P D L Sc m₁ j u)
    ?_ (L.toNat - k) t ⟨k, hk, rfl, ht⟩
  intro rem u ⟨j, hj, hrem, hu⟩
  refine WP.mono (loop_step s P D L Sc m₁ hp hb hj u hu) fun v ⟨hv, hz⟩ => ?_
  by_cases hend : j + 1 = L.toNat
  · left
    refine ⟨?_, hend ▸ hv⟩
    rw [hend, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.sub_self] at hz
    simp only [eval, hz, Option.map_some]
    rfl
  · right
    have hL := L.isLt
    obtain hnz : BitVec.ofNat 32 (j + 1) - L ≠ 0#32 := by
      intro h
      obtain h' := congrArg BitVec.toNat h
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h'
      omega_using [hj, hend, h']
    refine ⟨?_, L.toNat - (j + 1), by omega_using [hj, hrem], j + 1, by omega_using [hj, hend], rfl, hv⟩
    simp only [eval, hz, Option.map_some, beq_eq_false_iff_ne.mpr hnz, Bool.not_false]

end VG.Proof.Rc4.X86

end

end

/-! # RC4 on x86 (32-bit): the stream function -/

@[expose] public section

namespace VG.Proof.Rc4.X86
open VG VG.X86 VG.Impl.Rc4.X86 VG.Spec.Rc4 VG.Proof.Rc4
open VG.Proof.MlDsa.X86.Pack (Keep WP.keep writesOnly addr_of_fit)

theorem apply_entry (s : State) {P D L Sc : BitVec 32} (hp : ApplyPre s P D L Sc) :
    WP isa (.block entry) s fun a => a.mem = s.mem ∧ Keep [.eax, .ecx, .edx] s a ∧
      a.gpr .eax = (contextAt s.mem (P.setWidth 64)).i.setWidth 32 ∧
      a.zf = some (L &&& L == 0#32) := by
  obtain h4 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 4) 4 := hp.arg_in (i := 0) (by decide)
  have v4 : s.mem.readW (addr (s.gpr .esp) 4) 32 = P := hp.aP
  obtain h12 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 12) 4 := hp.arg_in (i := 2) (by decide)
  have v12 : s.mem.readW (addr (s.gpr .esp) 12) 32 = L := hp.aL
  obtain a256 : addr P 256 = P.setWidth 64 + 256#64 := addr_of_fit (by have := hp.ctxFit; omega_using [this])
  obtain r256 : InRegions (s.rd ++ s.wr) (P.setWidth 64 + 256#64) 1 := by
    obtain ⟨r, hr, hc⟩ := region_offset _ _ _ 256 1 (by decide) (by decide) hp.ctx
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.mono (WP.keep (Q := fun a => a.mem = s.mem ∧
      a.gpr .eax = (contextAt s.mem (P.setWidth 64)).i.setWidth 32 ∧
      a.zf = some (L &&& L == 0#32)) [.eax, .ecx, .edx] ?_ (by decide +kernel))
    fun a ⟨h, hk⟩ => ⟨h.1, hk, h.2.1, h.2.2⟩
  unfold entry
  rrun [h4, v4, a256, r256, h12, v12, contextAt]
  exact ⟨rfl, rfl⟩

theorem apply_start (b : State) (P : BitVec 32) (hfit : P.toNat + 258 ≤ 2 ^ 32)
    (h4 : InRegions (b.rd ++ b.wr) (addr (b.gpr .esp) 4) 4)
    (v4 : b.mem.readW (addr (b.gpr .esp) 4) 32 = P)
    (h257 : InRegions (b.rd ++ b.wr) (P.setWidth 64 + 257#64) 1) :
    WP isa (.block start) b fun c => c.mem = b.mem ∧ Keep [.esi, .edi, .ebp, .ebx] b c ∧
      c.gpr .esi = b.gpr .eax ∧ c.gpr .edi = P ∧
      c.gpr .ebp = (b.mem (P.setWidth 64 + 257#64)).setWidth 32 ∧ c.gpr .ebx = 0#32 := by
  obtain a257 : addr P 257 = P.setWidth 64 + 257#64 := addr_of_fit (by omega_using [hfit])
  refine WP.mono (WP.keep (Q := fun c => c.mem = b.mem ∧ c.gpr .esi = b.gpr .eax ∧
      c.gpr .edi = P ∧ c.gpr .ebp = (b.mem (P.setWidth 64 + 257#64)).setWidth 32 ∧
      c.gpr .ebx = 0#32) [.esi, .edi, .ebp, .ebx] ?_ (by decide +kernel))
    fun c ⟨h, hk⟩ => ⟨h.1, hk, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  unfold start
  rrun [h4, v4, a257, h257]

theorem apply_finish (d : State) (i j : Byte) (P : BitVec 32) (hfit : P.toNat + 258 ≤ 2 ^ 32)
    (hsi : d.gpr .esi = i.setWidth 32) (hbp : d.gpr .ebp = j.setWidth 32) (hdi : d.gpr .edi = P)
    (hw : InRegions d.wr (P.setWidth 64) 258) :
    WP isa (.block finish) d fun e =>
      e.mem = (d.mem.write (P.setWidth 64 + 256#64) 1 i).write (P.setWidth 64 + 257#64) 1 j ∧
      Keep [.eax] d e := by
  obtain a256 : addr P 256 = P.setWidth 64 + 256#64 := addr_of_fit (by omega_using [hfit])
  obtain a257 : addr P 257 = P.setWidth 64 + 257#64 := addr_of_fit (by omega_using [hfit])
  obtain h256 := region_offset _ _ _ 256 1 (by decide) (by decide) hw
  obtain h257 := region_offset _ _ _ 257 1 (by decide) (by decide) hw
  refine WP.mono (WP.keep (Q := fun e =>
      e.mem = (d.mem.write (P.setWidth 64 + 256#64) 1 i).write (P.setWidth 64 + 257#64) 1 j)
    [.eax] ?_ (by decide +kernel)) fun e ⟨h, hk⟩ => ⟨h, hk⟩
  unfold finish
  rrun [hsi, hbp, hdi, a256, a257, h256, h257, writeW_byte8, low_byte32]

theorem saved_spill (Sc : BitVec 32) :
    Region.Disjoint ⟨Sc.setWidth 64, 16⟩ ⟨Sc.setWidth 64 + BitVec.ofNat 64 16, 4⟩ := by
  intro x h₁ h₂
  exact Offset.sep_base (Sc.setWidth 64) (n := 16) (e := 16) (k := 4) (Nat.le_refl _) (by decide) x
    (by simp only [Region.Contains] at h₁; omega_using [h₁]) (by simp only [Region.Contains] at h₂; omega_using [h₂])

/-- The full stream function, including empty input. -/
theorem apply_ok (s : State) {P D L Sc : BitVec 32} (hp : ApplyPre s P D L Sc) :
    WP isa VG.Impl.Rc4.X86.apply s fun t =>
      (contextAt t.mem (P.setWidth 64) = (upd s P D L.toNat).1 ∧
        bytesAt t.mem (D.setWidth 64) L.toNat = (upd s P D L.toNat).2) ∧
      Frame (applyRegions P D L Sc) s.mem t.mem ∧ t.gpr .ebx = s.gpr .ebx ∧
      t.gpr .esi = s.gpr .esi ∧ t.gpr .edi = s.gpr .edi ∧ t.gpr .ebp = s.gpr .ebp := by
  unfold VG.Impl.Rc4.X86.apply
  refine WP.seq (WP.mono (apply_entry s hp) fun a ⟨ham, hak, hax, haz⟩ => ?_)
  obtain hasp : a.gpr .esp = s.gpr .esp := hak.gpr (by decide)
  refine WP.ite (L == 0#32) (by simp only [eval, haz, BitVec.and_self]) (fun hz => ?_)
    (fun hnz => ?_)
  · have hL : L.toNat = 0 := by rw [beq_iff_eq.mp hz]; rfl
    refine WP.block_nil ?_
    rw [hL, ham]
    exact ⟨⟨rfl, rfl⟩, Frame.refl _ _, hak.gpr (by decide), hak.gpr (by decide),
      hak.gpr (by decide), hak.gpr (by decide)⟩
  obtain hL0 : L.toNat ≠ 0 := fun h => by
    have : L = 0#32 := BitVec.eq_of_toNat_eq h
    rw [this] at hnz
    exact absurd hnz (by decide)
  refine WP.seq ?_
  rw [WP.block_append_iff]
  obtain hsc : InRegions a.wr (Sc.setWidth 64) 64 := by rw [hak.2.2]; exact hp.scratch
  refine WP.mono (save_ok a Sc hp.scratchFit
    (by rw [hak.2.1, hak.2.2, hasp]; exact hp.arg_in (i := 3) (by decide))
    (by rw [ham, hasp]; exact hp.aS) hsc) fun b ⟨hbm, hbk⟩ => ?_
  obtain hsave : Frame [⟨Sc.setWidth 64, 64⟩] s.mem b.mem := by
    rw [hbm, ham]; exact savedMem_frame _ _ _ _ _ _
  obtain hbf : Frame (applyRegions P D L Sc) s.mem b.mem :=
    hsave.mono fun r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain hbsp : b.gpr .esp = s.gpr .esp := (hbk.gpr (by decide)).trans hasp
  obtain hbrd : b.rd = s.rd := hbk.2.1.trans hak.2.1
  obtain hbwr : b.wr = s.wr := hbk.2.2.trans hak.2.2
  obtain hsd : ∀ r ∈ [(⟨Sc.setWidth 64, 64⟩ : Region)],
      Region.Disjoint ⟨P.setWidth 64, 258⟩ r := by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    exact hp.ctxScratch
  obtain hctx : contextAt b.mem (P.setWidth 64) = contextAt s.mem (P.setWidth 64) :=
    contextAt_frame hsave hsd
  obtain r257 : InRegions (b.rd ++ b.wr) (P.setWidth 64 + 257#64) 1 := by
    obtain ⟨r, hr, hc⟩ := region_offset _ _ _ 257 1 (by decide) (by decide) hp.ctx
    exact ⟨r, by rw [hbrd, hbwr]; exact List.mem_append_right _ hr, hc⟩
  refine WP.mono (apply_start b P hp.ctxFit
    (by rw [hbrd, hbwr, hbsp]; exact hp.arg_in (i := 0) (by decide))
    (by rw [hbsp]; exact (hp.arg_eq hbf (i := 0) (by decide)).trans hp.aP) r257)
    fun c ⟨hcm, hck, hcsi, hcdi, hcbp, hcbx⟩ => ?_
  obtain hinv : LoopInv s P D L Sc b.mem 0 c := by
    have hu0 : upd s P D 0 = (contextAt s.mem (P.setWidth 64), []) := rfl
    refine
      { le := Nat.zero_le _
        table := by rw [hu0, hcm, hctx]
        i := by rw [hu0, hcsi, (hbk.gpr (by decide) : b.gpr .eax = a.gpr .eax), hax]
        j := by
          rw [hu0, hcbp, ← hctx]
          rfl
        data := by rw [hu0]; rfl
        tail := fun x _ hx => by
          rw [hcm]
          exact hsave.bytes (R := ⟨D.setWidth 64, L.toNat⟩) (fun r hr => by
            simp only [List.mem_singleton] at hr
            subst hr
            exact hp.dataScratch) (show L.toNat ≤ 2 ^ 64 by have := L.isLt; omega_using []) hx
        frame := by rw [hcm]; exact Frame.refl _ _
        bx := hcbx
        p := hcdi
        sp := (hck.gpr (by decide)).trans hbsp
        rd := hck.2.1.trans hbrd
        wr := hck.2.2.trans hbwr }
  refine WP.seq (WP.mono (apply_loop s P D L Sc b.mem hp hbf (Nat.pos_of_ne_zero hL0) c hinv)
    fun d hd => ?_)
  rw [WP.block_append_iff]
  refine WP.mono (apply_finish d (upd s P D L.toNat).1.i (upd s P D L.toNat).1.j P hp.ctxFit
    hd.i hd.j hd.p (by rw [hd.wr]; exact hp.ctx)) fun e ⟨hem, hek⟩ => ?_
  have hc258 : (⟨P.setWidth 64, 258⟩ : Region) ∈
      [⟨P.setWidth 64, 258⟩, ⟨Sc.setWidth 64 + BitVec.ofNat 64 16, 4⟩, ⟨D.setWidth 64, L.toNat⟩] :=
    List.mem_cons_self
  obtain hbe : Frame [⟨P.setWidth 64, 258⟩, ⟨Sc.setWidth 64 + BitVec.ofNat 64 16, 4⟩,
      ⟨D.setWidth 64, L.toNat⟩] b.mem e.mem := by
    rw [hem]
    refine Frame.write ?_ hc258 _ (Offset.contains_base _ (by decide) (by decide))
    refine Frame.write ?_ hc258 _ (Offset.contains_base _ (by decide) (by decide))
    refine hd.frame.sub fun r hr => ?_
    simp only [loopRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Region.sub_prefix (Nat.le_refl _)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
        Region.sub_prefix (Nat.le_refl _)⟩
  obtain hse : Frame (applyRegions P D L Sc) s.mem e.mem := by
    refine hbf.trans (hbe.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, Region.sub_prefix (Nat.le_refl _)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
        Offset.sub_base _ (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Region.sub_prefix (Nat.le_refl _)⟩
  obtain hsaved : Saved e.mem Sc a := by
    obtain h0 := saved_savedMem a.mem Sc a
    rw [← hbm] at h0
    refine h0.frame hbe fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hp.ctxScratch.symm).sub_left (Region.sub_prefix (by decide))
    · exact saved_spill Sc
    · exact (hp.dataScratch.symm).sub_left (Region.sub_prefix (by decide))
  obtain hesp : e.gpr .esp = s.gpr .esp := (hek.gpr (by decide)).trans hd.sp
  obtain herd : e.rd = s.rd := hek.2.1.trans hd.rd
  obtain hewr : e.wr = s.wr := hek.2.2.trans hd.wr
  refine WP.mono (restore_ok a e Sc hp.scratchFit
    (by rw [herd, hewr, hesp]; exact hp.arg_in (i := 3) (by decide))
    (by rw [hesp]; exact (hp.arg_eq hse (i := 3) (by decide)).trans hp.aS)
    (by rw [herd, hewr]; obtain ⟨r, hr, hc⟩ := hp.scratch; exact ⟨r, List.mem_append_right _ hr, hc⟩)
    hsaved) fun g ⟨gbx, gsi, gdi, gbp, gm, _⟩ => ?_
  have hDP (o : Nat) (ho : o < 258) :
      Mem.Sep (D.setWidth 64) L.toNat (P.setWidth 64 + BitVec.ofNat 64 o) 1 :=
    sep_of_sub hp.ctxData.symm (contains_prefix _ (Nat.le_refl _))
      (Offset.contains_base _ (by omega_using [ho]) (by omega_using [ho]))
  obtain hLn : L.toNat < 2 ^ 64 := by have := L.isLt; omega_using []
  refine ⟨⟨?_, ?_⟩, by rw [gm]; exact hse, gbx.trans (hak.gpr (by decide)),
    gsi.trans (hak.gpr (by decide)), gdi.trans (hak.gpr (by decide)),
    gbp.trans (hak.gpr (by decide))⟩
  · rw [gm, hem, context_finish]
    exact context_ext hd.table rfl rfl
  · rw [gm, hem, bytes_write_sep _ _ _ _ _ hLn (hDP 257 (by decide)),
      bytes_write_sep _ _ _ _ _ hLn (hDP 256 (by decide))]
    exact hd.data

end VG.Proof.Rc4.X86

end

end

/-! # RC4 on x86 (32-bit): constant time

Initialization is checked by the taint analysis alone. The stream function
first loads the PRGA index `i` from the context, which the analysis takes
for secret: the contract lets it leak, so the proof makes it public by hand
(`entry_ct`) and the analysis checks the rest.
-/

@[expose] public section

namespace VG.Proof.Rc4.X86
open VG VG.X86 VG.Impl.Rc4.X86 VG.Spec.Rc4 VG.Proof.Rc4
open VG.Proof.MlDsa.X86.Pack (Keep WP.keep writesOnly addr_of_fit)

/-! ## Initialization -/

def initTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [258, 64],
    argLen := 20, argBases := [(12, 0), (16, 1)] }

theorem initTaint_wf {s : State} (hs : initC.pre s) : VG.X86.Taint.Wf initTaint s := by
  obtain ⟨_, hwr, _, _, cs, ac, as, rc, rs, _, cfit, sfit, spfit⟩ := hs
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨?_, ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨spfit, ?_⟩, ?_⟩
  · rw [hwr]
    exact .cons (Nat.le_refl _) (.cons (Nat.le_refl _) .nil)
  · simp only [hwr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq, List.Pairwise.nil, and_true]
    exact ⟨cs, fun _ h => h.elim⟩
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega_arith
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega_using [spfit]) rc ac
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega_using [spfit]) rs as
  · intro p hp
    simp only [initTaint, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hwr, addr, arg, argAddr]

theorem initTaint_agree {s t : State} (hs : initC.pre s) (ht : initC.pre t) (hp : initC.pub s t) :
    VG.X86.Taint.Agree initTaint s t := by
  obtain ⟨sp, args⟩ := hp
  have fit : ∀ s, initC.pre s → (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 := by
    intro s hs; obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, h⟩ := hs; exact h
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, initTaint_wf hs,
    initTaint_wf ht, VG.X86.Taint.slotsOk_empty,
    VG.X86.Taint.slotsAgree_empty, fun _ => sp, fun k h4 hk => ?_⟩
  · simp only [initTaint, RegSet.mem_ofList, List.mem_singleton] at hr
    subst r; exact sp
  · rw [hs.2.1, ht.2.1, args 2 (by decide), args 3 (by decide)]
  · simp only [initTaint] at hk
    rw [show VG.X86.Taint.depth initTaint.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (fit _ hs) h4 hk, VG.X86.Taint.argByte_eq (fit _ ht) h4 hk,
      Mem.readW_byte s.mem _ (Nat.mod_lt _ (by decide)),
      Mem.readW_byte t.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (args ((k - 4) / 4) (by omega_using [hk]))

theorem init_ct : ConstantTime isa initC.pre initC.pub init :=
  VG.Taint.constantTime (A := taint) initTaint (fun _ _ h₁ h₂ hp => initTaint_agree h₁ h₂ hp)
    (by taint_decide)

/-! ## The stream function -/

def applyTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [258, 0, 64],
    argLen := 20, argBases := [(4, 0), (8, 1), (16, 2)] }

/-- After `entry`, with `i` in `eax`. -/
def loopTaint : VG.X86.Taint.T := { applyTaint with regs := .ofList [.esp, .eax] }

theorem applyTaint_wf {s : State} (hs : applyC.pre s) : VG.X86.Taint.Wf applyTaint s := by
  obtain ⟨_, hwr, cd, cs, ds, ac, ad, as, rc, rd, rs, cfit, dfit, sfit, spfit⟩ := hs
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨?_, ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨spfit, ?_⟩, ?_⟩
  · rw [hwr]
    exact .cons (Nat.le_refl _) (.cons (Nat.zero_le _) (.cons (Nat.le_refl _) .nil))
  · simp only [hwr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true]
    exact ⟨⟨cd, cs⟩, ds, fun _ h => h.elim⟩
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega_arith
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega_using [spfit]) rc ac
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega_using [spfit]) rd ad
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega_using [spfit]) rs as
  · intro p hp
    simp only [applyTaint, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hwr, addr, arg, argAddr]

theorem applyTaint_agree {s t : State} (hs : applyC.pre s) (ht : applyC.pre t)
    (sp : s.gpr .esp = t.gpr .esp) (args : ∀ i < 4, arg s i = arg t i) :
    VG.X86.Taint.Agree applyTaint s t := by
  have fit : ∀ s, applyC.pre s → (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 := by
    intro s hs; obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, h⟩ := hs; exact h
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, applyTaint_wf hs,
    applyTaint_wf ht, VG.X86.Taint.slotsOk_empty,
    VG.X86.Taint.slotsAgree_empty, fun _ => sp, fun k h4 hk => ?_⟩
  · simp only [applyTaint, RegSet.mem_ofList, List.mem_singleton] at hr
    subst r; exact sp
  · rw [hs.2.1, ht.2.1, args 0 (by decide), args 1 (by decide), args 2 (by decide),
      args 3 (by decide)]
  · simp only [applyTaint] at hk
    rw [show VG.X86.Taint.depth applyTaint.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (fit _ hs) h4 hk, VG.X86.Taint.argByte_eq (fit _ ht) h4 hk,
      Mem.readW_byte s.mem _ (Nat.mod_lt _ (by decide)),
      Mem.readW_byte t.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (args ((k - 4) / 4) (by omega_using [hk]))

theorem applyPre_of {s : State} (hs : applyC.pre s) :
    ApplyPre s (arg s 0) (arg s 1) (arg s 2) (arg s 3) := by
  obtain ⟨hrd, hwr, cd, cs, ds, ac, ad, as, _, _, _, cfit, dfit, sfit, spfit⟩ := hs
  exact
    { aP := rfl, aD := rfl, aL := rfl, aS := rfl
      args := ⟨_, by rw [hrd]; exact List.mem_singleton_self _, Region.contains_self _ _⟩
      ctx := ⟨_, by rw [hwr]; exact List.mem_cons_self, Region.contains_self _ _⟩
      data := ⟨_, by rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self,
        Region.contains_self _ _⟩
      scratch := ⟨_, by rw [hwr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        List.mem_cons_self), Region.contains_self _ _⟩
      ctxFit := cfit, dataFit := dfit, scratchFit := sfit, spFit := spfit
      ctxData := cd, ctxScratch := cs, dataScratch := ds
      argsCtx := ac, argsData := ad, argsScratch := as }

/-- The PRGA index `i` is loaded from the context, where the taint analysis
takes it for secret: it may leak, so it is public. -/
theorem entry_ct : RelCT isa (fun a b => applyC.pre a ∧ applyC.pre b ∧ applyC.pub a b)
    (.block entry) fun a b => VG.X86.Taint.Agree loopTaint a b ∧ a.zf = b.zf := by
  intro a b tr tr' a' b' ⟨hpa, hpb, hsp, hargs, hi⟩ ea eb
  have hag := applyTaint_agree hpa hpb hsp hargs
  obtain ⟨htrace, -⟩ := RelCT.taint (A := taint) (P := fun a b => VG.X86.Taint.Agree applyTaint a b)
    applyTaint (fun _ _ h => h) (by taint_decide) a b tr tr' a' b' hag ea eb
  obtain ⟨_, u, eu, ham, hak, hax, haz⟩ := apply_entry a (applyPre_of hpa)
  obtain ⟨_, rfl⟩ := Exec.det eu ea
  obtain ⟨_, v, ev, hbm, hbk, hbx, hbz⟩ := apply_entry b (applyPre_of hpb)
  obtain ⟨_, rfl⟩ := Exec.det ev eb
  have hi' : (contextAt a.mem ((arg a 0).setWidth 64)).i =
      (contextAt b.mem ((arg b 0).setWidth 64)).i :=
    BitVec.eq_of_toNat_eq (List.cons.inj hi).1
  have hsp₁ : u.gpr .esp = a.gpr .esp := hak.gpr (by decide)
  have hsp₂ : v.gpr .esp = b.gpr .esp := hbk.gpr (by decide)
  refine ⟨htrace, VG.X86.Taint.Agree.keep hag ⟨fun r hr => ?_, fun h => nomatch h⟩ rfl rfl rfl rfl
    rfl hak.2.2 hbk.2.2 ham hbm hsp₁ hsp₂ (fun _ h => (List.not_mem_nil h).elim)
    (fun _ h => (List.not_mem_nil h).elim), ?_⟩
  · simp only [loopTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [hsp₁, hsp₂, hsp]
    · rw [hax, hbx, hi']
  · rw [haz, hbz, hargs 2 (by decide)]

theorem nil_ct {P : State → State → Prop} : RelCT isa P (.block []) fun _ _ => True := by
  intro _ _ _ _ _ _ _ e₁ e₂
  rw [Exec.block_iff] at e₁ e₂
  simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e₁ e₂
  exact ⟨e₁.2.symm.trans e₂.2, trivial⟩

theorem apply_ct : ConstantTime isa applyC.pre applyC.pub apply := by
  apply RelCT.constantTime (Q := fun _ _ => True)
  unfold apply
  refine RelCT.seq entry_ct (RelCT.ite ?_ nil_ct ?_)
  · intro a b ⟨_, hz⟩
    simp only [eval, hz]
  · exact RelCT.taint (A := taint) loopTaint (fun _ _ h => h.1.1) (by taint_decide)

end VG.Proof.Rc4.X86
