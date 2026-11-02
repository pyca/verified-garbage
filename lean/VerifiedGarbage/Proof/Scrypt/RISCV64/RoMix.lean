module

public import VerifiedGarbage.Proof.Scrypt.RISCV64.Common
public import VerifiedGarbage.Proof.Scrypt.RISCV64.RoMixLoops
public import VerifiedGarbage.Proof.Scrypt.RoMix
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
import VerifiedGarbage.Proof.Scrypt.RISCV64.BlockMix
import VerifiedGarbage.Proof.Scrypt.RISCV64.Lit
import VerifiedGarbage.Proof.Scrypt.Memory
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import all Init.Data.Nat.Power2.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.DefEqTransformations
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Scrypt.RISCV64.Lit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Impl.Scrypt.RISCV64.RoMix

/-!
# scryptROMix on RISC-V: correctness

Untrusted: everything here is checked by Lean. The structure of the PPC64LE
proof (`Proof/Scrypt/PPC64LE/RoMix.lean`), for both widths of the accesses:
the calls of scryptBlockMix by `WP.call` from its proof (`bm_ok`), step 2
(`Inv2`) and step 3 (`Inv3`), with our caller's registers and `N` kept in
`save` (`Kept`). There is no stack frame: the return address is saved with
the callee-saved registers.
-/

@[expose] public section

namespace VG.Proof.Scrypt.RISCV64.RoMix

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Scrypt.RISCV64 VG.WriteBytes
open VG.Spec.Scrypt (bytesAt blockMix roMix)
open VG.Proof.Scrypt (vList vList_getD roMix_eq roMixIndices_eq mixLoop_succ_fst mixLoop_succ_snd
  integerify_mod and_mask)
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt add_ofNat toNat_add_ofNat contains_off sub_off disj_off
  InRegions.of_mem InRegions.right frame_bytesAt bytesAt_writeBytes_self bytesAt_writeBytes_sep
  bytesAt_length xorBytes_length)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev bP : Addr := s₀.gpr .a0
abbrev rr : Nat := (s₀.gpr .a1).toNat
abbrev vP : Addr := s₀.gpr .a2
abbrev vl : Nat := (s₀.gpr .a3).toNat
abbrev tP : Addr := s₀.gpr .a4
abbrev sv : Addr := s₀.gpr .a5
/-- `N`. -/
abbrev NN : Nat := vl s₀ / rr s₀
abbrev bR : Region := ⟨bP s₀, rr s₀ * 128⟩
abbrev vR : Region := ⟨vP s₀, vl s₀ * 128⟩
abbrev tR : Region := ⟨tP s₀, rr s₀ * 128⟩
abbrev svR : Region := ⟨sv s₀, 168⟩
/-- The input. -/
abbrev B : List Byte := bytesAt s₀.mem (bP s₀) (128 * rr s₀)
/-- `V[i]`. -/
abbrev vAt (i : Nat) : Addr := vP s₀ + BitVec.ofNat 64 (128 * rr s₀ * i)
/-- scryptBlockMix's `save`. -/
abbrev bsv : Addr := sv s₀ + BitVec.ofNat 64 72

/-- Our return address and our caller's registers are saved in `save`. -/
abbrev Saved (m : Mem) : Prop := Spill.Saved (sv s₀) s₀.gpr rmSaved m

end

structure Pre (wide : Bool) (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [bR s₀, vR s₀, tR s₀, svR s₀]
  b_v : (bR s₀).Disjoint (vR s₀)
  b_t : (bR s₀).Disjoint (tR s₀)
  b_s : (bR s₀).Disjoint (svR s₀)
  v_t : (vR s₀).Disjoint (tR s₀)
  v_s : (vR s₀).Disjoint (svR s₀)
  t_s : (tR s₀).Disjoint (svR s₀)
  b_nw : (bP s₀).toNat + rr s₀ * 128 ≤ 2 ^ 64
  v_nw : (vP s₀).toNat + vl s₀ * 128 ≤ 2 ^ 64
  t_nw : (tP s₀).toNat + rr s₀ * 128 ≤ 2 ^ 64
  s_nw : (sv s₀).toNat + 168 ≤ 2 ^ 64
  pos : 0 < rr s₀
  vl_eq : vl s₀ = rr s₀ * NN s₀
  pow : (NN s₀).isPowerOfTwo
  s_al : (sv s₀).toNat % 8 = 0
  al : wide = true → (bP s₀).toNat % 8 = 0 ∧ (vP s₀).toNat % 8 = 0 ∧ (tP s₀).toNat % 8 = 0

theorem pre_of {wide : Bool} {s₀ : State} (h : (Proof.Scrypt.roMixRISCV64 wide).pre s₀) :
    Pre wide s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h14)).symm, h15, h16, h17⟩

section
variable {wide : Bool} {s₀ : State} (hp : Pre wide s₀)
include hp

theorem NN_pos : 0 < NN s₀ := by
  obtain ⟨e, he⟩ := hp.pow
  rw [he]; exact Nat.two_pow_pos _

theorem vl_mul : vl s₀ * 128 = 128 * rr s₀ * NN s₀ := by
  rw [hp.vl_eq, Nat.mul_comm, ← Nat.mul_assoc]

/-- `v` is not the whole address space, since `save` is not in it. -/
theorem v_lt : 128 * rr s₀ * NN s₀ < 2 ^ 64 := by
  rw [← vl_mul hp]
  by_contra hc
  refine hp.v_s (sv s₀) ?_ (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega)
  simp only [Region.Contains]
  have := (sv s₀ - vP s₀).isLt
  omega

theorem r_lt : 128 * rr s₀ < 2 ^ 64 := by
  have := v_lt hp
  have := NN_pos hp
  have : 128 * rr s₀ ≤ 128 * rr s₀ * NN s₀ := Nat.le_mul_of_pos_right _ (by omega)
  omega

theorem NN_lt : NN s₀ < 2 ^ 64 := by
  have := v_lt hp
  have : NN s₀ ≤ 128 * rr s₀ * NN s₀ := Nat.le_mul_of_pos_left _ (by have := hp.pos; omega)
  omega

omit hp in
theorem v_le {i : Nat} (hi : i < NN s₀) : 128 * rr s₀ * i + 128 * rr s₀ ≤ 128 * rr s₀ * NN s₀ := by
  rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi

/-- `V[i]` is in `v`. -/
theorem vAt_sub {i : Nat} (hi : i < NN s₀) : Region.Sub ⟨vAt s₀ i, 128 * rr s₀⟩ (vR s₀) := by
  have := v_lt hp
  have := v_le hi
  show Region.Sub ⟨vP s₀ + BitVec.ofNat 64 (128 * rr s₀ * i), 128 * rr s₀⟩ ⟨vP s₀, vl s₀ * 128⟩
  exact sub_off (by rw [vl_mul hp]; omega) (by omega)

theorem vAt_disj {i k : Nat} (hi : i < NN s₀) (hk : k < NN s₀) (hik : i ≠ k) :
    Region.Disjoint ⟨vAt s₀ i, 128 * rr s₀⟩ ⟨vAt s₀ k, 128 * rr s₀⟩ := by
  have := v_lt hp
  have h1 := v_le hi
  have h2 := v_le hk
  refine disj_off _ ?_ (by omega) (by omega) (by omega) (by omega)
  rcases Nat.lt_or_gt_of_ne hik with h | h
  · left; rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h
  · right; rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h

theorem vAt_al (hw : wide = true) (i : Nat) : (vAt s₀ i).toNat % 8 = 0 :=
  Spill.al8 (hp.al hw).2.1 (by
    rw [Nat.mul_assoc, show 128 = 8 * 16 from rfl, Nat.mul_assoc]; exact Nat.mul_mod_right _ _)

end

theorem in_s (s₀ : State) {o n : Nat} (h : o + n ≤ 168) :
    (svR s₀).Contains (sv s₀ + BitVec.ofNat 64 o) n :=
  contains_off (by omega) (by omega)

theorem s_sub (s₀ : State) {o n : Nat} (h : o + n ≤ 168) :
    Region.Sub ⟨sv s₀ + BitVec.ofNat 64 o, n⟩ (svR s₀) :=
  sub_off (by omega) (by omega)

/-! ## What stays in `save`: the caller's registers and `N` -/

/-- Bytes `[0, 72)` of `save`. -/
abbrev keepR (s₀ : State) : Region := ⟨sv s₀, 72⟩

/-- scryptBlockMix's part of `save`. -/
abbrev bsvR (s₀ : State) : Region := ⟨bsv s₀, 96⟩

def Kept (s₀ : State) (m : Mem) : Prop :=
  Saved s₀ m ∧ m.readW (sv s₀ + BitVec.ofNat 64 64) 64 = BitVec.ofNat 64 (NN s₀)

theorem word_sub (s₀ : State) {d : Nat} (h₂ : d + 8 ≤ 72) :
    Region.Sub ⟨sv s₀ + BitVec.ofNat 64 d, 8⟩ (keepR s₀) :=
  sub_off (by omega) (by omega)

theorem saved_offs {p : Reg × Nat} (hp : p ∈ rmSaved) : p.2 + 8 ≤ 64 := by
  simp only [rmSaved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem Kept.frame {s₀ : State} {m m' : Mem} {rs : List Region} (h : Kept s₀ m) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (keepR s₀).Disjoint r) : Kept s₀ m' := by
  refine ⟨fun p hp => ?_, ?_⟩
  · have ho := saved_offs hp
    rw [← h.1 p hp]
    exact hf.readW (r := ⟨sv s₀ + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (word_sub s₀ (by omega))) (by decide)
  · rw [← h.2]
    exact hf.readW (r := ⟨sv s₀ + BitVec.ofNat 64 64, 8⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (word_sub s₀ (by omega))) (by decide)

theorem keep_sub (s₀ : State) : Region.Sub (keepR s₀) (svR s₀) := Region.sub_prefix (by omega)
theorem bsv_sub (s₀ : State) : Region.Sub (bsvR s₀) (svR s₀) := s_sub s₀ (by omega)

theorem keep_bsv (s₀ : State) : (keepR s₀).Disjoint (bsvR s₀) := by
  have := disj_off (sv s₀) (o₁ := 0) (n₁ := 72) (o₂ := 72) (n₂ := 96) (by omega)
    (by omega) (by omega) (by omega) (by omega)
  simpa using this

section
variable {wide : Bool} {s₀ : State} (hp : Pre wide s₀)
include hp

theorem keep_b : (keepR s₀).Disjoint (bR s₀) := hp.b_s.symm.sub_left (keep_sub s₀)
theorem keep_v : (keepR s₀).Disjoint (vR s₀) := hp.v_s.symm.sub_left (keep_sub s₀)
theorem keep_t : (keepR s₀).Disjoint (tR s₀) := hp.t_s.symm.sub_left (keep_sub s₀)

omit hp in
theorem b_sub' : Region.Sub ⟨bP s₀, 128 * rr s₀⟩ (bR s₀) := by
  rw [Nat.mul_comm]; exact fun _ h => h

omit hp in
theorem t_sub' : Region.Sub ⟨tP s₀, 128 * rr s₀⟩ (tR s₀) := by
  rw [Nat.mul_comm]; exact fun _ h => h

end

theorem shr_ofNat {a : Nat} (n : Nat) (h : a < 2 ^ 64) :
    BitVec.ofNat 64 a >>> n = BitVec.ofNat 64 (a / 2 ^ n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, toNat_ofNat_lt h, toNat_ofNat_lt
    (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h), Nat.shiftRight_eq_div_pow]

/-! ## Instructions -/

theorem wp_mul {is : List Instr} {s : State} {Q : State → Prop} {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n * s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.mul d n m :: is)) s Q :=
  WP.cons exec_mul (k _ (Upd.write _ _ _))

theorem wp_and {is : List Instr} {s : State} {Q : State → Prop} {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n &&& s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .and d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _))

theorem ofNat_toNat' (x : BitVec 64) : x = BitVec.ofNat 64 x.toNat := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem shl7 {x : BitVec 64} (h : 128 * x.toNat < 2 ^ 64) : x <<< 7 = BitVec.ofNat 64 (128 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, show 2 ^ 7 = 128 from rfl, Nat.mul_comm,
    Nat.mod_eq_of_lt h, toNat_ofNat_lt h]

theorem dbl' (x : BitVec 64) : x + x = BitVec.ofNat 64 (2 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem add_sub64 (a : Addr) {n : Nat} (h : 64 ≤ n) :
    a + BitVec.ofNat 64 n - BitVec.ofNat 64 64 = a + BitVec.ofNat 64 (n - 64) := by
  rw [show n = (n - 64) + 64 by omega, BitVec.ofNat_add, ← BitVec.add_assoc, Nat.add_sub_cancel,
    BitVec.add_sub_cancel]

/-! ## A call of scryptBlockMix -/

theorem blockMix_noFrames (wide : Bool) : (Impl.Scrypt.RISCV64.blockMix wide).noFrames = true := by
  cases wide <;> lit_decide

/-- A call of scryptBlockMix from `a0` to `a2`, of `r = a1` chunks, saving
registers at `a3`. -/
theorem blockMixCall_ok (wide : Bool) {s : State} {src dst bs : Addr} {r : Nat}
    (h0 : s.gpr .a0 = src) (h1 : s.gpr .a1 = BitVec.ofNat 64 r) (h2 : s.gpr .a2 = dst)
    (h3 : s.gpr .a3 = bs) (hr : 0 < r) (hlt : 128 * r < 2 ^ 64)
    (hds : Region.Disjoint ⟨dst, r * 128⟩ ⟨bs, 96⟩) (hsd : Region.Disjoint ⟨src, r * 128⟩ ⟨dst, r * 128⟩)
    (hss : Region.Disjoint ⟨src, r * 128⟩ ⟨bs, 96⟩)
    (hsn : src.toNat + r * 128 ≤ 2 ^ 64) (hdn : dst.toNat + r * 128 ≤ 2 ^ 64)
    (hbn : bs.toNat + 96 ≤ 2 ^ 64) (hba : bs.toNat % 8 = 0)
    (hal : wide = true → src.toNat % 8 = 0 ∧ dst.toNat % 8 = 0)
    (hin : InRegions (s.rd ++ s.wr) src (r * 128)) (hout : InRegions s.wr dst (r * 128))
    (hbs : InRegions s.wr bs 96) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      Frame [⟨dst, r * 128⟩, ⟨bs, 96⟩] s.mem s'.mem →
      bytesAt s'.mem dst (128 * r) = blockMix r (bytesAt s.mem src (128 * r)) → Q s') :
    WP isa (.call (blockMixName wide) (Impl.Scrypt.RISCV64.blockMix wide)) s Q := by
  have c0 : s.callEntry.gpr .a0 = src := (State.callEntry_gpr _ (by decide)).trans h0
  have c1 : s.callEntry.gpr .a1 = BitVec.ofNat 64 r := (State.callEntry_gpr _ (by decide)).trans h1
  have c2 : s.callEntry.gpr .a2 = dst := (State.callEntry_gpr _ (by decide)).trans h2
  have c3 : s.callEntry.gpr .a3 = bs := (State.callEntry_gpr _ (by decide)).trans h3
  have er : (BitVec.ofNat 64 r).toNat = r := toNat_ofNat_lt (by omega)
  have hw : Covers [⟨dst, r * 128⟩, ⟨bs, 96⟩] s.wr := Covers.pair (Covers.one hout) (Covers.one hbs)
  refine WP.call (k := Proof.Scrypt.blockMixRISCV64 wide) (BlockMix.blockMix_verified wide).1
    (rd := [⟨src, r * 128⟩]) (wr := [⟨dst, r * 128⟩, ⟨bs, 96⟩]) ?_ ?_ hw ?_ (blockMix_noFrames wide)
  · simp only [Proof.Scrypt.blockMixRISCV64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, c0, c1, c2, c3, er]
    exact ⟨trivial, trivial, hds, hsd, hss, hsn, hdn, hbn, hr, hba, hal⟩
  · exact Covers.append_left (rs := [⟨src, r * 128⟩]) (Covers.one hin) hw.right
  · intro s' hrd hwr hsp hf hcs _ hpost
    simp only [Proof.Scrypt.blockMixRISCV64, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c0, c1, c2, er] at hpost
    exact hQ s' hrd hwr hsp hcs hf hpost

/-! ## The prologue -/

/-- The memory after the prologue's saves. -/
abbrev saveMem (s₀ : State) : Mem := Spill.saveMem s₀.mem (sv s₀) s₀.gpr rmSaved

theorem saveMem_saved (s₀ : State) : Saved s₀ (saveMem s₀) := Spill.saveMem_saved (by decide) _ _ _

theorem saveMem_frame (s₀ : State) : Frame [svR s₀] s₀.mem (saveMem s₀) :=
  Spill.saveMem_frame_base (by decide) (by decide) _ _ _

theorem prologue_eq : rmPrologue = Spill.saveCode .a5 rmSaved ++
    ([mov .s4 .a0, mov .s5 .a2, mov .s9 .a4, mov .s10 .a5, .shift .sll .d .s6 .a1 7,
      mov .t0 .a1, .li .t1 1, .add .t2 .a3 .a3] : List Instr) := rfl

theorem save_ok {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s₁, s₁.gpr = s₀.gpr → s₁.rd = s₀.rd → s₁.wr = s₀.wr → s₁.sp = s₀.sp →
      s₁.mem = saveMem s₀ → WP isa (.block rest) s₁ Q) :
    WP isa (.block (Spill.saveCode .a5 rmSaved ++ rest)) s₀ Q :=
  Spill.save_ok hp.s_al (by decide) (fun p hp' => by
    rw [hp.wr]; exact InRegions.of_mem (by simp) (in_s s₀ (by revert p; decide)))
    (k _ rfl rfl rfl rfl rfl)

/-- The callee-saved registers ROMix never writes, which the calls keep. -/
abbrev mid : List Reg := [.s0, .s1, .s2, .s3, .s11]

/-- The registers ROMix writes. -/
abbrev written : List Reg :=
  [.ra, .t0, .t1, .t2, .t3, .t4, .t5, .a0, .a1, .a2, .a3, .s4, .s5, .s6, .s7, .s8, .s9, .s10]

theorem mid_ne {r r' : Reg} (hr : r ∈ mid) (h' : r' ∈ written) : r ≠ r' := by
  have key : ∀ r ∈ mid, ∀ r' ∈ written, r ≠ r' := by decide
  exact key r hr r' h'

theorem mid_pres {r : Reg} (hr : r ∈ mid) : r ∈ preserved := by
  have key : ∀ r ∈ mid, r ∈ preserved := by decide
  exact key r hr

/-- After the prologue. -/
structure P1 (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  mem : s.mem = saveMem s₀
  s4 : s.gpr .s4 = bP s₀
  s5 : s.gpr .s5 = vP s₀
  s9 : s.gpr .s9 = tP s₀
  s10 : s.gpr .s10 = sv s₀
  s6 : s.gpr .s6 = BitVec.ofNat 64 (128 * rr s₀)
  t0 : s.gpr .t0 = BitVec.ofNat 64 (rr s₀)
  t1 : s.gpr .t1 = 1
  t2 : s.gpr .t2 = BitVec.ofNat 64 (2 * vl s₀)
  keep : ∀ r ∈ mid, s.gpr r = s₀.gpr r

theorem setup_ok {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {s₁ : State} (g₀ : s₁.gpr = s₀.gpr)
    (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr) (hsp : s₁.sp = s₀.sp) (hm : s₁.mem = saveMem s₀) :
    WP isa (.block [mov .s4 .a0, mov .s5 .a2, mov .s9 .a4, mov .s10 .a5, .shift .sll .d .s6 .a1 7,
      mov .t0 .a1, .li .t1 1, .add .t2 .a3 .a3]) s₁ (P1 s₀) := by
  have lt : 128 * (s₀.gpr .a1).toNat < 2 ^ 64 := r_lt hp
  refine wp_mv fun a ua => wp_mv fun b ub => wp_mv fun c uc => wp_mv fun c' uc' =>
    wp_sll (by decide) fun d ud => wp_mv fun e ue => wp_li (imm := 1) (by decide) fun f uf =>
    wp_add fun h uh => WP.block_nil ?_
  have g : ∀ r, s₁.gpr r = s₀.gpr r := fun r => by rw [g₀]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_⟩
  · rw [uh.rd, uf.rd, ue.rd, ud.rd, uc'.rd, uc.rd, ub.rd, ua.rd, hrd]
  · rw [uh.wr, uf.wr, ue.wr, ud.wr, uc'.wr, uc.wr, ub.wr, ua.wr, hwr]
  · rw [uh.sp, uf.sp, ue.sp, ud.sp, uc'.sp, uc.sp, ub.sp, ua.sp, hsp]
  · rw [uh.mem, uf.mem, ue.mem, ud.mem, uc'.mem, uc.mem, ub.mem, ua.mem, hm]
  · rw [uh.other _ (by decide), uf.other _ (by decide), ue.other _ (by decide),
      ud.other _ (by decide), uc'.other _ (by decide), uc.other _ (by decide),
      ub.other _ (by decide), ua.gpr, g]
  · rw [uh.other _ (by decide), uf.other _ (by decide), ue.other _ (by decide),
      ud.other _ (by decide), uc'.other _ (by decide), uc.other _ (by decide), ub.gpr,
      ua.other _ (by decide), g]
  · rw [uh.other _ (by decide), uf.other _ (by decide), ue.other _ (by decide),
      ud.other _ (by decide), uc'.other _ (by decide), uc.gpr, ub.other _ (by decide),
      ua.other _ (by decide), g]
  · rw [uh.other _ (by decide), uf.other _ (by decide), ue.other _ (by decide),
      ud.other _ (by decide), uc'.gpr, uc.other _ (by decide), ub.other _ (by decide),
      ua.other _ (by decide), g]
  · rw [uh.other _ (by decide), uf.other _ (by decide), ue.other _ (by decide), ud.gpr,
      uc'.other _ (by decide), uc.other _ (by decide), ub.other _ (by decide),
      ua.other _ (by decide), g, shl7 lt]
  · rw [uh.other _ (by decide), uf.other _ (by decide), ue.gpr, ud.other _ (by decide),
      uc'.other _ (by decide), uc.other _ (by decide), ub.other _ (by decide),
      ua.other _ (by decide), g]
    exact ofNat_toNat' _
  · rw [uh.other _ (by decide), uf.gpr]; rfl
  · rw [uh.gpr, uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide),
      uc'.other _ (by decide), uc.other _ (by decide), ub.other _ (by decide),
      ua.other _ (by decide), g, dbl']
  · rw [uh.other _ (mid_ne hr (by decide)), uf.other _ (mid_ne hr (by decide)),
      ue.other _ (mid_ne hr (by decide)), ud.other _ (mid_ne hr (by decide)),
      uc'.other _ (mid_ne hr (by decide)), uc.other _ (mid_ne hr (by decide)),
      ub.other _ (mid_ne hr (by decide)), ua.other _ (mid_ne hr (by decide)), g]

theorem prologue_ok {wide : Bool} {s₀ : State} (hp : Pre wide s₀) :
    WP isa (.block rmPrologue) s₀ (P1 s₀) := by
  rw [prologue_eq]
  exact save_ok hp fun _ g hrd hwr hsp hm => setup_ok hp g hrd hwr hsp hm

/-! ## Computing `N` -/

/-- After the loop computing `N`. -/
structure N1 (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  mem : s.mem = saveMem s₀
  s4 : s.gpr .s4 = bP s₀
  s5 : s.gpr .s5 = vP s₀
  s9 : s.gpr .s9 = tP s₀
  s10 : s.gpr .s10 = sv s₀
  s6 : s.gpr .s6 = BitVec.ofNat 64 (128 * rr s₀)
  t1 : s.gpr .t1 = BitVec.ofNat 64 (2 * NN s₀)
  keep : ∀ r ∈ mid, s.gpr r = s₀.gpr r

theorem nloop_ok {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {s : State} (h : P1 s₀ s) :
    WP isa nLoop s (N1 s₀) := by
  obtain ⟨e, he⟩ := hp.pow
  have lt := v_lt hp
  have e2 : rr s₀ * 2 ^ (e + 1) = 2 * vl s₀ := by
    rw [hp.vl_eq, he, Nat.pow_succ, Nat.mul_comm (2 ^ e) 2, Nat.mul_left_comm]
  have hNe : 2 * vl s₀ < 2 ^ 64 := by have := vl_mul hp; omega
  refine WP.mono (nLoop_ok (r := rr s₀) (e := e) hp.pos (by omega) h.t0 h.t1
    (by rw [h.t2, e2])) fun t ⟨rd, wr, sp, mem, oth, h1⟩ => ?_
  exact ⟨by rw [rd, h.rd], by rw [wr, h.wr], by rw [sp, h.sp], by rw [mem, h.mem],
    by rw [oth _ (by decide) (by decide) (by decide), h.s4],
    by rw [oth _ (by decide) (by decide) (by decide), h.s5],
    by rw [oth _ (by decide) (by decide) (by decide), h.s9],
    by rw [oth _ (by decide) (by decide) (by decide), h.s10],
    by rw [oth _ (by decide) (by decide) (by decide), h.s6],
    by rw [h1, he, Nat.pow_succ, Nat.mul_comm],
    fun r hr => by
      rw [oth _ (mid_ne hr (by decide)) (mid_ne hr (by decide)) (mid_ne hr (by decide)), h.keep r hr]⟩

/-! ## Step 2 -/

/-- After `i` iterations of step 2. -/
structure Inv2 (s₀ : State) (i : Nat) (s : State) : Prop where
  i_le : i ≤ NN s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  s4 : s.gpr .s4 = bP s₀
  s5 : s.gpr .s5 = vP s₀
  s9 : s.gpr .s9 = tP s₀
  s10 : s.gpr .s10 = sv s₀
  s6 : s.gpr .s6 = BitVec.ofNat 64 (128 * rr s₀)
  s7 : s.gpr .s7 = BitVec.ofNat 64 (NN s₀ - i)
  s8 : s.gpr .s8 = vAt s₀ i
  frame : Frame [bR s₀, vR s₀, tR s₀, svR s₀] s₀.mem s.mem
  kept : Kept s₀ s.mem
  x : bytesAt s.mem (bP s₀) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) i (B s₀)
  done : ∀ k < i, bytesAt s.mem (vAt s₀ k) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) k (B s₀)
  keep : ∀ r ∈ mid, s.gpr r = s₀.gpr r

theorem setupMem_kept (s₀ : State) :
    Kept s₀ ((saveMem s₀).writeW (sv s₀ + BitVec.ofNat 64 64) (BitVec.ofNat 64 (NN s₀))) := by
  refine ⟨fun p hp => ?_, Mem.readW_writeW_self64 _ _ _⟩
  have ho := saved_offs hp
  rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
  exact saveMem_saved s₀ p hp

theorem setup2_ok {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {s : State} (h : N1 s₀ s) :
    WP isa (.block rmSetup) s (Inv2 s₀ 0) := by
  have lt := v_lt hp
  have n1 := NN_pos hp
  have : 2 * NN s₀ < 2 ^ 64 := by
    have : 2 * NN s₀ ≤ 128 * rr s₀ * NN s₀ := by
      have := hp.pos
      have : 2 ≤ 128 * rr s₀ := by omega
      exact Nat.mul_le_mul_right _ this
    omega
  unfold rmSetup
  refine wp_srl (by decide) fun t1 u1 => ?_
  have hd : t1.gpr .t1 = BitVec.ofNat 64 (NN s₀) := by
    rw [u1.gpr, h.t1, shr_ofNat _ (by omega), Nat.pow_one, Nat.mul_div_cancel_left _ (by decide)]
  refine wp_sd (a := sv s₀ + BitVec.ofNat 64 64) (by decide) (by rw [u1.other _ (by decide), h.s10])
    (Spill.al8 hp.s_al (by decide))
    (by rw [u1.wr, h.wr, hp.wr]; exact InRegions.of_mem (by simp) (in_s s₀ (by omega)))
    fun t2 u2 => wp_mv fun t3 u3 => wp_mv fun t4 u4 => WP.block_nil ?_
  have g : ∀ r, r ≠ .t1 → r ≠ .s7 → r ≠ .s8 → t4.gpr r = s.gpr r := fun r b c d => by
    rw [u4.other _ d, u3.other _ c, u2.gpr, u1.other _ b]
  have hm : t4.mem = (saveMem s₀).writeW (sv s₀ + BitVec.ofNat 64 64) (BitVec.ofNat 64 (NN s₀)) := by
    rw [u4.mem, u3.mem, u2.mem, hd, u1.mem, h.mem]
  have fr : Frame [svR s₀] s₀.mem t4.mem := by
    rw [hm]; exact (saveMem_frame s₀).writeW (List.mem_singleton_self _) _ (in_s s₀ (by omega))
  refine ⟨Nat.zero_le _, by rw [u4.rd, u3.rd, u2.rd, u1.rd, h.rd],
    by rw [u4.wr, u3.wr, u2.wr, u1.wr, h.wr], by rw [u4.sp, u3.sp, u2.sp, u1.sp, h.sp],
    by rw [g _ (by decide) (by decide) (by decide), h.s4],
    by rw [g _ (by decide) (by decide) (by decide), h.s5],
    by rw [g _ (by decide) (by decide) (by decide), h.s9],
    by rw [g _ (by decide) (by decide) (by decide), h.s10],
    by rw [g _ (by decide) (by decide) (by decide), h.s6], ?_, ?_,
    fr.mono (by simp), by rw [hm]; exact setupMem_kept s₀, ?_, fun k hk => absurd hk (by omega),
    fun r hr => by
      rw [g _ (mid_ne hr (by decide)) (mid_ne hr (by decide)) (mid_ne hr (by decide)), h.keep r hr]⟩
  · rw [u4.other _ (by decide), u3.gpr, u2.gpr, hd]; rfl
  · rw [u4.gpr, u3.other _ (by decide), u2.gpr, u1.other _ (by decide), h.s5]
    simp
  · refine frame_bytesAt fr (fun r hr => ?_) (by have := r_lt hp; omega)
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.b_s.sub_left (b_sub' (s₀ := s₀))

/-! ## A call of scryptBlockMix into `b` -/

/-- The instructions before the call, after `a0` is set. -/
abbrev bmTail : List Instr := [.shift .srl .d .a1 .s6 7, mov .a2 .s4, .addi .a3 .s10 72]

theorem blockMixTo_eq (wide : Bool) (src : List Instr) :
    blockMixTo wide src = .seq (.block (src ++ bmTail))
      (.call (blockMixName wide) (Impl.Scrypt.RISCV64.blockMix wide)) := rfl

theorem b_in {wide : Bool} {s₀ : State} (hp : Pre wide s₀) : InRegions s₀.wr (bP s₀) (rr s₀ * 128) := by
  rw [hp.wr]
  refine InRegions.of_mem (R := bR s₀) (by simp) ?_
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega

theorem bsv_in {wide : Bool} {s₀ : State} (hp : Pre wide s₀) : InRegions s₀.wr (bsv s₀) 96 := by
  rw [hp.wr]
  exact InRegions.of_mem (R := svR s₀) (by simp) (in_s s₀ (by omega))

/-- The registers our loops keep are not the call's arguments. -/
theorem pres_ne : ∀ r ∈ preserved, r ≠ .a0 ∧ r ≠ .a1 ∧ r ≠ .a2 ∧ r ≠ .a3 ∧ r ≠ .t0 ∧ r ≠ .t1 ∧
    r ≠ .t2 ∧ r ≠ .t3 ∧ r ≠ .t4 ∧ r ≠ .t5 := by decide

theorem rmul (r : Nat) : r * 128 = 128 * r := Nat.mul_comm _ _

/-- Setting up and making the call, from `a0 = A`. -/
theorem bm_ok {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {s : State} {A : Addr}
    (hA : s.gpr .a0 = A) (h4 : s.gpr .s4 = bP s₀) (h10 : s.gpr .s10 = sv s₀)
    (h6 : s.gpr .s6 = BitVec.ofNat 64 (128 * rr s₀)) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hAb : Region.Disjoint ⟨A, 128 * rr s₀⟩ ⟨bP s₀, 128 * rr s₀⟩)
    (hAw : Region.Disjoint ⟨A, 128 * rr s₀⟩ (bsvR s₀)) (hAn : A.toNat + 128 * rr s₀ ≤ 2 ^ 64)
    (hAa : wide = true → A.toNat % 8 = 0)
    (hAi : InRegions (s₀.rd ++ s₀.wr) A (128 * rr s₀)) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      Frame [⟨bP s₀, 128 * rr s₀⟩, bsvR s₀] s.mem s'.mem →
      bytesAt s'.mem (bP s₀) (128 * rr s₀) = blockMix (rr s₀) (bytesAt s.mem A (128 * rr s₀)) →
      Q s') :
    WP isa (.block bmTail) s fun s' =>
      WP isa (.call (blockMixName wide) (Impl.Scrypt.RISCV64.blockMix wide)) s' Q := by
  have lt := r_lt hp
  refine wp_srl (by decide) fun a ua => wp_mv fun b ub => wp_addi (by decide) fun d ud =>
    WP.block_nil ?_
  have k : ∀ r, r ≠ .a1 → r ≠ .a2 → r ≠ .a3 → d.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [ud.other _ h3, ub.other _ h2, ua.other _ h1]
  have h1 : a.gpr .a1 = BitVec.ofNat 64 (rr s₀) := by
    rw [ua.gpr, h6, shr_ofNat _ lt]; exact congrArg (BitVec.ofNat _) (by omega)
  have hm : d.mem = s.mem := by rw [ud.mem, ub.mem, ua.mem]
  have hbs := (hp.b_s.sub_left (b_sub' (s₀ := s₀))).sub_right (bsv_sub s₀)
  refine blockMixCall_ok wide (src := A) (dst := bP s₀) (bs := bsv s₀) (r := rr s₀)
    (by rw [k _ (by decide) (by decide) (by decide), hA])
    (by rw [ud.other _ (by decide), ub.other _ (by decide), h1])
    (by rw [ud.other _ (by decide), ub.gpr, ua.other _ (by decide), h4])
    (by rw [ud.gpr, ub.other _ (by decide), ua.other _ (by decide), h10])
    hp.pos lt (by rw [rmul]; exact hbs) (by rw [rmul]; exact hAb) (by rw [rmul]; exact hAw)
    (by rw [rmul]; exact hAn) (by have := hp.b_nw; omega)
    (by have := hp.s_nw; rw [toNat_add_ofNat _ (by omega)]; omega)
    (Spill.al8 hp.s_al (by decide)) (fun hw => ⟨hAa hw, (hp.al hw).1⟩)
    (by rw [ud.rd, ub.rd, ua.rd, ud.wr, ub.wr, ua.wr, hrd, hwr, rmul]; exact hAi)
    (by rw [ud.wr, ub.wr, ua.wr, hwr]; exact b_in hp)
    (by rw [ud.wr, ub.wr, ua.wr, hwr]; exact bsv_in hp)
    fun s' rd' wr' sp' cs' f' b' => hQ s' (by rw [rd', ud.rd, ub.rd, ua.rd])
      (by rw [wr', ud.wr, ub.wr, ua.wr]) (by rw [sp', ud.sp, ub.sp, ua.sp])
      (fun r hr => by
        obtain ⟨-, n1, n2, n3, -⟩ := pres_ne r hr
        rw [cs' r hr, k r n1 n2 n3])
      (by rw [hm, rmul] at f'; exact f') (by rw [b', hm])

/-! ## The units of the copies -/

/-- The number of units in `128 r` bytes. -/
abbrev cnt (wide : Bool) (r : Nat) : Nat := if wide then 16 * r else 128 * r

theorem cnt_mul (wide : Bool) (r : Nat) : unitB wide * cnt wide r = 128 * r := by
  cases wide <;> simp [unitB, cnt] <;> omega

theorem cnt_pos {wide : Bool} {r : Nat} (hr : 0 < r) : 0 < cnt wide r := by
  cases wide <;> simp [cnt] <;> omega

theorem cnt_lt {wide : Bool} {r : Nat} (hr : 128 * r < 2 ^ 64) : cnt wide r < 2 ^ 64 := by
  cases wide <;> simp [cnt] <;> omega

theorem unit_le {wide : Bool} {r k : Nat} (hk : k < cnt wide r) :
    unitB wide * k + unitB wide ≤ 128 * r := by
  rw [← cnt_mul wide r, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hk

/-- `t ← ` the number of units in `128 r` bytes, from `s6 = 128 r`. -/
theorem count_ok {wide : Bool} {t : Reg} {s : State} {r : Nat} (h6 : s.gpr .s6 = BitVec.ofNat 64 (128 * r))
    (hlt : 128 * r < 2 ^ 64) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' t (BitVec.ofNat 64 (cnt wide r)) → WP isa (.block is) s' Q) :
    WP isa (.block ((if wide then .shift .srl .d t .s6 3 else mov t .s6) :: is)) s Q := by
  cases wide with
  | true =>
    refine wp_srl (by decide) fun s' u => k s' ?_
    have e : s.gpr .s6 >>> 3 = BitVec.ofNat 64 (cnt true r) := by
      rw [h6, shr_ofNat _ hlt]; exact congrArg (BitVec.ofNat _) (by simp [cnt]; omega)
    exact ⟨by rw [u.gpr, e], u.other, u.mem, u.rd, u.wr, u.sp⟩
  | false =>
    refine wp_mv fun s' u => k s' ?_
    exact ⟨by rw [u.gpr, h6]; rfl, u.other, u.mem, u.rd, u.wr, u.sp⟩

theorem unitCount_eq (wide : Bool) :
    unitCount wide = (if wide then .shift .srl .d .t2 .s6 3 else mov .t2 .s6) := by
  cases wide <;> rfl

section
variable {wide : Bool} {s₀ : State} (hp : Pre wide s₀)
include hp

theorem vAt_nw {i : Nat} (hi : i < NN s₀) : (vAt s₀ i).toNat + 128 * rr s₀ ≤ 2 ^ 64 := by
  have := v_lt hp
  have hv := hp.v_nw
  have e := vl_mul hp
  have := v_le hi
  have := hp.pos
  rw [toNat_add_ofNat _ (by omega)]
  omega

theorem vAt_in {i : Nat} (hi : i < NN s₀) : InRegions s₀.wr (vAt s₀ i) (128 * rr s₀) := by
  rw [hp.wr]
  have e := vl_mul hp
  have := v_le hi
  have lt := v_lt hp
  exact InRegions.of_mem (R := vR s₀) (by simp) (contains_off (by rw [e]; omega) (by omega))

/-- `V[i]` and the other regions. -/
theorem vAt_b {i : Nat} (hi : i < NN s₀) : Region.Disjoint ⟨vAt s₀ i, 128 * rr s₀⟩ (bR s₀) :=
  hp.b_v.symm.sub_left (vAt_sub hp hi)
theorem vAt_t {i : Nat} (hi : i < NN s₀) : Region.Disjoint ⟨vAt s₀ i, 128 * rr s₀⟩ (tR s₀) :=
  hp.v_t.sub_left (vAt_sub hp hi)
theorem vAt_s {i : Nat} (hi : i < NN s₀) : Region.Disjoint ⟨vAt s₀ i, 128 * rr s₀⟩ (svR s₀) :=
  hp.v_s.sub_left (vAt_sub hp hi)

omit hp in
/-- The frame of a call writing `b`, from the one we keep. -/
theorem call_frame {m m' : Mem} (hf : Frame [⟨bP s₀, 128 * rr s₀⟩, bsvR s₀] m m') :
    Frame [bR s₀, vR s₀, tR s₀, svR s₀] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨bR s₀, by simp, b_sub'⟩
    · exact ⟨svR s₀, by simp, bsv_sub s₀⟩

/-- What a call writing `b` keeps: `V[k]`. -/
theorem call_keeps_v {m m' : Mem} (hf : Frame [⟨bP s₀, 128 * rr s₀⟩, bsvR s₀] m m')
    {k : Nat} (hk : k < NN s₀) :
    bytesAt m' (vAt s₀ k) (128 * rr s₀) = bytesAt m (vAt s₀ k) (128 * rr s₀) := by
  refine frame_bytesAt hf (fun r hr => ?_) (by have := r_lt hp; omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (vAt_b hp hk).sub_right b_sub'
  · exact (vAt_s hp hk).sub_right (bsv_sub s₀)

theorem call_kept {m m' : Mem} (hf : Frame [⟨bP s₀, 128 * rr s₀⟩, bsvR s₀] m m')
    (h : Kept s₀ m) : Kept s₀ m' :=
  h.frame hf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (keep_b hp).sub_right b_sub'
    · exact keep_bsv s₀

/-- The memory after iteration `i` of step 2. -/
theorem mem2_ok {i : Nat} (hi : i < NN s₀) {s : State} (h : Inv2 s₀ i s) {m₃ : Mem}
    (f₃ : Frame [⟨bP s₀, 128 * rr s₀⟩, bsvR s₀]
      (writeBytes s.mem (vAt s₀ i) (bytesAt s.mem (bP s₀) (128 * rr s₀))) m₃)
    (b₃ : bytesAt m₃ (bP s₀) (128 * rr s₀) = blockMix (rr s₀)
      (bytesAt (writeBytes s.mem (vAt s₀ i) (bytesAt s.mem (bP s₀) (128 * rr s₀))) (vAt s₀ i)
        (128 * rr s₀))) :
    Frame [bR s₀, vR s₀, tR s₀, svR s₀] s₀.mem m₃ ∧ Kept s₀ m₃ ∧
    bytesAt m₃ (bP s₀) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) (i + 1) (B s₀) ∧
    ∀ k < i + 1, bytesAt m₃ (vAt s₀ k) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) k (B s₀) := by
  have lt := r_lt hp
  have hl : (bytesAt s.mem (bP s₀) (128 * rr s₀)).length = 128 * rr s₀ := bytesAt_length _ _ _
  have hself : bytesAt (writeBytes s.mem (vAt s₀ i) (bytesAt s.mem (bP s₀) (128 * rr s₀))) (vAt s₀ i)
      (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) i (B s₀) := by
    have := bytesAt_writeBytes_self s.mem (vAt s₀ i) (bytesAt s.mem (bP s₀) (128 * rr s₀))
      (by rw [hl]; exact lt)
    rw [hl] at this
    rw [this, h.x]
  have f₂ : Frame [⟨vAt s₀ i, 128 * rr s₀⟩] s.mem
      (writeBytes s.mem (vAt s₀ i) (bytesAt s.mem (bP s₀) (128 * rr s₀))) :=
    writeBytes_frame _ _ _ (by rw [hl]; exact Region.contains_self _ _)
  have f₂' : Frame [bR s₀, vR s₀, tR s₀, svR s₀] s.mem
      (writeBytes s.mem (vAt s₀ i) (bytesAt s.mem (bP s₀) (128 * rr s₀))) :=
    f₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨vR s₀, by simp, vAt_sub hp hi⟩
  refine ⟨(h.frame.trans f₂').trans (call_frame f₃), call_kept hp f₃ (h.kept.frame f₂ fun r hr => ?_),
    by rw [b₃, hself]; rfl, fun k hk => ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact (keep_v hp).sub_right (vAt_sub hp hi)
  · rw [call_keeps_v hp f₃ (by omega)]
    by_cases hki : k = i
    · subst hki; exact hself
    · rw [bytesAt_writeBytes_sep _ _ (by rw [hl]; exact vAt_disj hp (by omega) hi hki) lt]
      exact h.done k (by omega)

theorem b_unit {k : Nat} (hk : k < cnt wide (rr s₀)) :
    InRegions (s₀.rd ++ s₀.wr) (bP s₀ + BitVec.ofNat 64 (unitB wide * k)) (unitB wide) := by
  have := r_lt hp
  have := unit_le hk
  rw [hp.rd, hp.wr]
  exact InRegions.of_mem (R := bR s₀) (by simp) (contains_off (by omega) (by omega))

theorem v_unit {i k : Nat} (hi : i < NN s₀) (hk : k < cnt wide (rr s₀)) :
    InRegions s₀.wr (vAt s₀ i + BitVec.ofNat 64 (unitB wide * k)) (unitB wide) := by
  rw [hp.wr]
  have e := vl_mul hp
  have := v_le hi
  have lt := v_lt hp
  have := unit_le hk
  show InRegions _ (vP s₀ + BitVec.ofNat 64 (128 * rr s₀ * i) + BitVec.ofNat 64 (unitB wide * k)) _
  rw [add_ofNat]
  exact InRegions.of_mem (R := vR s₀) (by simp) (contains_off (by rw [e]; omega) (by omega))

theorem t_unit {k : Nat} (hk : k < cnt wide (rr s₀)) :
    InRegions s₀.wr (tP s₀ + BitVec.ofNat 64 (unitB wide * k)) (unitB wide) := by
  have := r_lt hp
  have := unit_le hk
  rw [hp.wr]
  exact InRegions.of_mem (R := tR s₀) (by simp) (contains_off (by omega) (by omega))

end

theorem vAt_succ (s₀ : State) (i : Nat) :
    vAt s₀ i + BitVec.ofNat 64 (128 * rr s₀) = vAt s₀ (i + 1) := by
  show _ = vP s₀ + BitVec.ofNat 64 (128 * rr s₀ * (i + 1))
  rw [add_ofNat, Nat.mul_succ]

/-- One iteration of step 2. -/
theorem step2_ok {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {i : Nat}
    (hi : i < NN s₀) {s : State} (h : Inv2 s₀ i s) :
    WP isa (step2 wide) s fun s' => Inv2 s₀ (i + 1) s' ∧ (s'.gpr .s7 != 0) = decide (i + 1 ≠ NN s₀) := by
  have lt := r_lt hp
  have pos := hp.pos
  have hN := NN_lt hp
  unfold step2
  rw [unitCount_eq]
  refine WP.seq (wp_mv fun a ua => wp_mv fun b ub => count_ok (wide := wide)
    (by rw [ub.other _ (by decide), ua.other _ (by decide), h.s6]) lt fun d ud => WP.block_nil ?_)
  have ke : ∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .t2 → d.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [ud.other _ h3, ub.other _ h2, ua.other _ h1]
  have erd : d.rd = s₀.rd := by rw [ud.rd, ub.rd, ua.rd, h.rd]
  have ewr : d.wr = s₀.wr := by rw [ud.wr, ub.wr, ua.wr, h.wr]
  have esp : d.sp = s₀.sp := by rw [ud.sp, ub.sp, ua.sp, h.sp]
  have hme : d.mem = s.mem := by rw [ud.mem, ub.mem, ua.mem]
  have e8 := cnt_mul wide (rr s₀)
  refine WP.seq (WP.mono (copyLoop_ok (wide := wide) (src := bP s₀) (dst := vAt s₀ i)
    (n := cnt wide (rr s₀)) (cnt_pos pos) (by rw [e8]; exact lt)
    (fun hw => ⟨(hp.al hw).1, vAt_al hp hw i⟩)
    (by rw [ud.other _ (by decide), ub.other _ (by decide), ua.gpr, h.s4])
    (by rw [ud.other _ (by decide), ub.gpr, ua.other _ (by decide), h.s8])
    ud.gpr
    (fun k hk => by rw [erd, ewr]; exact b_unit hp hk)
    (fun k hk => by rw [ewr]; exact v_unit hp hi hk)
    (by rw [e8]; exact (vAt_b hp hi).symm.sub_left b_sub'))
    fun t ⟨rdt, wrt, spt, gt, mt⟩ => ?_)
  rw [hme, e8] at mt
  have kt : ∀ r ∈ preserved, t.gpr r = s.gpr r := fun r hr => by
    obtain ⟨-, -, -, -, h0, h1, h2, h3, -⟩ := pres_ne r hr
    rw [gt r h0 h1 h2 h3, ke r h0 h1 h2]
  rw [blockMixTo_eq]
  refine WP.seq (WP.seq (wp_mv fun f uf => ?_))
  have kf : ∀ r ∈ preserved, f.gpr r = s.gpr r := fun r hr => by
    rw [uf.other _ (pres_ne r hr).1, kt r hr]
  refine bm_ok hp (A := vAt s₀ i) (by rw [uf.gpr, kt _ (by decide), h.s8])
    (by rw [kf _ (by decide), h.s4]) (by rw [kf _ (by decide), h.s10])
    (by rw [kf _ (by decide), h.s6]) (by rw [uf.rd, rdt, erd]) (by rw [uf.wr, wrt, ewr])
    ((vAt_b hp hi).sub_right b_sub') ((vAt_s hp hi).sub_right (bsv_sub s₀))
    (vAt_nw hp hi) (fun hw => vAt_al hp hw i) (InRegions.right (vAt_in hp hi))
    fun s4 rd4 wr4 sp4 cs4 f4 b4 => ?_
  rw [uf.mem, mt] at f4 b4
  obtain ⟨F, K, X, D⟩ := mem2_ok hp hi h f4 b4
  have k4 : ∀ r ∈ preserved, s4.gpr r = s.gpr r := fun r hr => by
    rw [cs4 r hr, kf r hr]
  refine wp_add fun s5 u5 => wp_subi (imm := 1) (by decide) fun s6 u6 => WP.block_nil ?_
  have k6 : ∀ r ∈ preserved, r ≠ .s7 → r ≠ .s8 → s6.gpr r = s.gpr r :=
    fun r hr h1 h2 => by rw [u6.other _ h1, u5.other _ h2, k4 r hr]
  have e7 : s6.gpr .s7 = BitVec.ofNat 64 (NN s₀ - (i + 1)) := by
    rw [u6.gpr, u5.other _ (by decide), k4 _ (by decide), h.s7, dec_count hi]
  refine ⟨⟨by omega, by rw [u6.rd, u5.rd, rd4, uf.rd, rdt, erd], by rw [u6.wr, u5.wr, wr4, uf.wr, wrt, ewr],
    by rw [u6.sp, u5.sp, sp4, uf.sp, spt, esp],
    by rw [k6 _ (by decide) (by decide) (by decide), h.s4],
    by rw [k6 _ (by decide) (by decide) (by decide), h.s5],
    by rw [k6 _ (by decide) (by decide) (by decide), h.s9],
    by rw [k6 _ (by decide) (by decide) (by decide), h.s10],
    by rw [k6 _ (by decide) (by decide) (by decide), h.s6], e7, ?_,
    by rw [u6.mem, u5.mem]; exact F, by rw [u6.mem, u5.mem]; exact K,
    by rw [u6.mem, u5.mem]; exact X, by rw [u6.mem, u5.mem]; exact D,
    fun r hr => by
      rw [k6 r (mid_pres hr) (mid_ne hr (by decide)) (mid_ne hr (by decide)), h.keep r hr]⟩, ?_⟩
  · rw [u6.other _ (by decide), u5.gpr, k4 _ (by decide), k4 _ (by decide), h.s8, h.s6, vAt_succ]
  · rw [e7, dec_ne hi hN]

theorem loop2_ok {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {s : State}
    (h : Inv2 s₀ 0 s) : WP isa (.loop (step2 wide) (.nonzero .s7)) s (Inv2 s₀ (NN s₀)) :=
  count_loop (NN_pos hp) (Inv2 s₀) (fun _ hi _ h => step2_ok hp hi h) h

/-! ## Step 3 -/

/-- After `i` iterations of step 3. -/
structure Inv3 (s₀ : State) (i : Nat) (s : State) : Prop where
  i_le : i ≤ NN s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  s4 : s.gpr .s4 = bP s₀
  s5 : s.gpr .s5 = vP s₀
  s9 : s.gpr .s9 = tP s₀
  s10 : s.gpr .s10 = sv s₀
  s6 : s.gpr .s6 = BitVec.ofNat 64 (128 * rr s₀)
  s7 : s.gpr .s7 = BitVec.ofNat 64 (NN s₀ - i)
  s8 : s.gpr .s8 = BitVec.ofNat 64 (NN s₀ - 1)
  frame : Frame [bR s₀, vR s₀, tR s₀, svR s₀] s₀.mem s.mem
  kept : Kept s₀ s.mem
  v : ∀ k < NN s₀, bytesAt s.mem (vAt s₀ k) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) k (B s₀)
  x : (Spec.Scrypt.mixLoop (rr s₀) (NN s₀) (vList (rr s₀) (NN s₀) (B s₀)) (NN s₀ - i)
    (bytesAt s.mem (bP s₀) (128 * rr s₀))).1 = roMix (rr s₀) (NN s₀) (B s₀)
  /-- The indices still to come. -/
  js : (Spec.Scrypt.mixLoop (rr s₀) (NN s₀) (vList (rr s₀) (NN s₀) (B s₀)) (NN s₀ - i)
    (bytesAt s.mem (bP s₀) (128 * rr s₀))).2 =
      (Spec.Scrypt.roMixIndices (rr s₀) (NN s₀) (B s₀)).drop i
  keep : ∀ r ∈ mid, s.gpr r = s₀.gpr r

theorem mid_ok {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {s : State} (h : Inv2 s₀ (NN s₀) s) :
    WP isa (.block rmMid) s (Inv3 s₀ 0) := by
  have n1 := NN_pos hp
  unfold rmMid
  refine wp_ld (a := sv s₀ + BitVec.ofNat 64 64) (by decide) (by rw [h.s10])
    (Spill.al8 hp.s_al (by decide))
    (by rw [h.rd, h.wr, hp.rd, hp.wr]
        exact InRegions.of_mem (R := svR s₀) (by simp) (in_s s₀ (by omega)))
    fun a ua => wp_subi (imm := 1) (by decide) fun b ub => WP.block_nil ?_
  have ka : a.gpr .s7 = BitVec.ofNat 64 (NN s₀) := by rw [ua.gpr, h.kept.2]
  have k : ∀ r, r ≠ .s7 → r ≠ .s8 → b.gpr r = s.gpr r := fun r h1 h2 => by
    rw [ub.other _ h2, ua.other _ h1]
  have hm : b.mem = s.mem := by rw [ub.mem, ua.mem]
  refine ⟨Nat.zero_le _, by rw [ub.rd, ua.rd, h.rd], by rw [ub.wr, ua.wr, h.wr],
    by rw [ub.sp, ua.sp, h.sp], by rw [k _ (by decide) (by decide), h.s4],
    by rw [k _ (by decide) (by decide), h.s5], by rw [k _ (by decide) (by decide), h.s9],
    by rw [k _ (by decide) (by decide), h.s10],
    by rw [k _ (by decide) (by decide), h.s6], by rw [ub.other _ (by decide), ka]; rfl, ?_,
    by rw [hm]; exact h.frame, by rw [hm]; exact h.kept, fun k hk => by rw [hm]; exact h.done k hk,
    ?_, ?_, fun r hr => by rw [k _ (mid_ne hr (by decide)) (mid_ne hr (by decide)), h.keep r hr]⟩
  · rw [ub.gpr, ka]
    have := dec_count (n := NN s₀) (k := 0) n1
    simpa using this
  · rw [hm, h.x, Nat.sub_zero]
    exact (roMix_eq _ _ _).symm
  · rw [hm, h.x, Nat.sub_zero, List.drop_zero]
    exact (roMixIndices_eq _ _ _).symm

/-- The index `j`. -/
abbrev jOf (s₀ : State) (m : Mem) : Nat :=
  Spec.Scrypt.integerify (rr s₀) (bytesAt m (bP s₀) (128 * rr s₀)) % NN s₀

theorem jOf_lt {wide : Bool} {s₀ : State} (hp : Pre wide s₀) (m : Mem) : jOf s₀ m < NN s₀ :=
  Nat.mod_lt _ (NN_pos hp)

/-- `j` as the code computes it. -/
theorem jOf_eq {wide : Bool} {s₀ : State} (hp : Pre wide s₀) (m : Mem) :
    m.readW (bP s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64)) 64 &&& BitVec.ofNat 64 (NN s₀ - 1) =
      BitVec.ofNat 64 (jOf s₀ m) := by
  obtain ⟨e, he⟩ := hp.pow
  have hN := NN_lt hp
  have he' : e ≤ 64 := by
    by_contra hc
    have : 2 ^ 64 < 2 ^ e := Nat.pow_lt_pow_right (by decide) (by omega)
    omega
  apply BitVec.eq_of_toNat_eq
  rw [toNat_ofNat_lt (by have := jOf_lt hp m; omega), he, and_mask _ he', jOf, he,
    integerify_mod _ _ hp.pos he']

/-- The address of the low word of `X`'s last 64-byte block. -/
theorem j_addr {wide : Bool} {s₀ : State} (hp : Pre wide s₀) :
    bP s₀ + BitVec.ofNat 64 (128 * rr s₀) - BitVec.ofNat 64 64 =
      bP s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64) :=
  add_sub64 _ (by have := hp.pos; omega)

theorem t_b {wide : Bool} {s₀ : State} (hp : Pre wide s₀) :
    Region.Disjoint ⟨tP s₀, 128 * rr s₀⟩ ⟨bP s₀, 128 * rr s₀⟩ :=
  (hp.b_t.symm.sub_left t_sub').sub_right b_sub'

theorem t_nw {wide : Bool} {s₀ : State} (hp : Pre wide s₀) : (tP s₀).toNat + 128 * rr s₀ ≤ 2 ^ 64 := by
  have := hp.t_nw; omega

theorem t_in {wide : Bool} {s₀ : State} (hp : Pre wide s₀) : InRegions s₀.wr (tP s₀) (128 * rr s₀) := by
  rw [hp.wr]
  refine InRegions.of_mem (R := tR s₀) (by simp) ?_
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; have := r_lt hp; omega

/-- The memory after iteration `i` of step 3. -/
theorem mem3_ok {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {i : Nat} (hi : i < NN s₀) {s : State}
    (h : Inv3 s₀ i s) {m₄ : Mem}
    (f₄ : Frame [⟨bP s₀, 128 * rr s₀⟩, bsvR s₀]
      (writeBytes s.mem (tP s₀) (Spec.Pbkdf2.xorBytes (bytesAt s.mem (bP s₀) (128 * rr s₀))
        (bytesAt s.mem (vAt s₀ (jOf s₀ s.mem)) (128 * rr s₀)))) m₄)
    (b₄ : bytesAt m₄ (bP s₀) (128 * rr s₀) = blockMix (rr s₀)
      (bytesAt (writeBytes s.mem (tP s₀) (Spec.Pbkdf2.xorBytes (bytesAt s.mem (bP s₀) (128 * rr s₀))
        (bytesAt s.mem (vAt s₀ (jOf s₀ s.mem)) (128 * rr s₀)))) (tP s₀) (128 * rr s₀))) :
    Frame [bR s₀, vR s₀, tR s₀, svR s₀] s₀.mem m₄ ∧ Kept s₀ m₄ ∧
    (∀ k < NN s₀, bytesAt m₄ (vAt s₀ k) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) k (B s₀)) ∧
    (Spec.Scrypt.mixLoop (rr s₀) (NN s₀) (vList (rr s₀) (NN s₀) (B s₀)) (NN s₀ - (i + 1))
      (bytesAt m₄ (bP s₀) (128 * rr s₀))).1 = roMix (rr s₀) (NN s₀) (B s₀) ∧
    (Spec.Scrypt.mixLoop (rr s₀) (NN s₀) (vList (rr s₀) (NN s₀) (B s₀)) (NN s₀ - (i + 1))
      (bytesAt m₄ (bP s₀) (128 * rr s₀))).2 =
        (Spec.Scrypt.roMixIndices (rr s₀) (NN s₀) (B s₀)).drop (i + 1) := by
  have lt := r_lt hp
  have hj := jOf_lt hp s.mem
  set T := Spec.Pbkdf2.xorBytes (bytesAt s.mem (bP s₀) (128 * rr s₀))
    (bytesAt s.mem (vAt s₀ (jOf s₀ s.mem)) (128 * rr s₀)) with hT
  have hl : T.length = 128 * rr s₀ := by
    rw [hT, xorBytes_length _ _ (by simp [bytesAt_length]), bytesAt_length]
  have hself : bytesAt (writeBytes s.mem (tP s₀) T) (tP s₀) (128 * rr s₀) = T := by
    have := bytesAt_writeBytes_self s.mem (tP s₀) T (by rw [hl]; exact lt)
    rwa [hl] at this
  have f₂ : Frame [⟨tP s₀, 128 * rr s₀⟩] s.mem (writeBytes s.mem (tP s₀) T) :=
    writeBytes_frame _ _ _ (by rw [hl]; exact Region.contains_self _ _)
  have f₂' : Frame [bR s₀, vR s₀, tR s₀, svR s₀] s.mem (writeBytes s.mem (tP s₀) T) :=
    f₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨tR s₀, by simp, t_sub'⟩
  have hv : ∀ k < NN s₀, bytesAt m₄ (vAt s₀ k) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) k (B s₀) :=
    fun k hk => by
      rw [call_keeps_v hp f₄ hk, bytesAt_writeBytes_sep _ _
        (by rw [hl]; exact (vAt_t hp hk).sub_right t_sub') lt]
      exact h.v k hk
  have e : NN s₀ - i = NN s₀ - (i + 1) + 1 := by omega
  refine ⟨(h.frame.trans f₂').trans (call_frame f₄),
    call_kept hp f₄ (h.kept.frame f₂ fun r hr => ?_), hv, ?_, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact (keep_t hp).sub_right t_sub'
  · rw [← h.x, e, mixLoop_succ_fst, b₄, hself, hT, vList_getD _ hj, h.v _ hj]
  · have hs := h.js
    rw [e, mixLoop_succ_snd, vList_getD _ hj, ← h.v _ hj] at hs
    rw [← List.tail_drop, ← hs, b₄, hself, hT]
    rfl

/-- `jBlock`: `t0 = j`. -/
theorem j_ok {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {s : State} (h4 : s.gpr .s4 = bP s₀)
    (h6 : s.gpr .s6 = BitVec.ofNat 64 (128 * rr s₀)) (h8 : s.gpr .s8 = BitVec.ofNat 64 (NN s₀ - 1))
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block (jBlock wide)) s fun s' => s'.gpr .t0 = BitVec.ofNat 64 (jOf s₀ s.mem) ∧
      (∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .t2 → r ≠ .t3 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have lt := r_lt hp
  have := hp.pos
  have hX : bP s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64) =
      bP s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64) + BitVec.ofNat 64 0 := (BitVec.add_zero _).symm
  have hin : ∀ o, o + 4 ≤ 64 → InRegions (s.rd ++ s.wr)
      (bP s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64) + BitVec.ofNat 64 o) 4 := fun o ho => by
    rw [hrd, hwr, hp.rd, hp.wr, add_ofNat]
    exact InRegions.of_mem (R := bR s₀) (by simp) (contains_off (by omega) (by omega))
  unfold jBlock
  rw [List.append_assoc, WP.block_append_iff]
  refine wp_add fun a ua => wp_subi (imm := 64) (by decide) fun b ub => WP.block_nil ?_
  have e1 : b.gpr .t1 = bP s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64) := by
    rw [ub.gpr, ua.gpr, h4, h6, j_addr hp]
  have kb : ∀ r, r ≠ .t1 → b.gpr r = s.gpr r := fun r hr => by rw [ub.other _ hr, ua.other _ hr]
  -- The doubleword, then the mask.
  suffices key : WP isa (.block ((if wide then [.load .d .t0 .t1 0] else
        Impl.Words.RISCV64.loadLE64 .t0 .t2 .t3 .t1 0) ++ ([.logic .and .t0 .t0 .s8] : List Instr))) b
      fun s' => s'.gpr .t0 = b.mem.readW (bP s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64)) 64 &&&
          BitVec.ofNat 64 (NN s₀ - 1) ∧
        (∀ r, r ≠ .t0 → r ≠ .t2 → r ≠ .t3 → s'.gpr r = b.gpr r) ∧
        s'.mem = b.mem ∧ s'.rd = b.rd ∧ s'.wr = b.wr ∧ s'.sp = b.sp by
    refine WP.mono key fun s' ⟨g0, go, gm, grd, gwr, gsp⟩ => ⟨?_, fun r h0 h1 h2 h3 => ?_, ?_, ?_, ?_, ?_⟩
    · rw [g0, ub.mem, ua.mem, jOf_eq hp]
    · rw [go r h0 h2 h3, kb r h1]
    · rw [gm, ub.mem, ua.mem]
    · rw [grd, ub.rd, ua.rd]
    · rw [gwr, ub.wr, ua.wr]
    · rw [gsp, ub.sp, ua.sp]
  have h8b : b.gpr .s8 = BitVec.ofNat 64 (NN s₀ - 1) := by rw [kb _ (by decide), h8]
  have hbr : b.rd = s.rd := by rw [ub.rd, ua.rd]
  have hbw : b.wr = s.wr := by rw [ub.wr, ua.wr]
  cases wide with
  | true =>
    simp only [↓reduceIte, List.cons_append, List.nil_append]
    refine wp_ld (a := bP s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64)) (by decide)
      (by rw [e1]; exact BitVec.add_zero _) (Spill.al8 (hp.al rfl).1 (by omega))
      (by
        rw [hbr, hbw, hrd, hwr, hp.rd, hp.wr]
        exact InRegions.of_mem (R := bR s₀) (by simp) (contains_off (by omega) (by omega)))
      fun d ud => wp_and fun e ue => WP.block_nil ?_
    refine ⟨?_, fun r h0 _ _ => ?_, by rw [ue.mem, ud.mem], by rw [ue.rd, ud.rd],
      by rw [ue.wr, ud.wr], by rw [ue.sp, ud.sp]⟩
    · rw [ue.gpr, ud.gpr, ud.other _ (by decide), h8b]
    · rw [ue.other _ h0, ud.other _ h0]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [WP.block_append_iff]
    refine WP.mono (VG.RISCV64.Bytes.loadLE64_ok (s := b) (d := .t0) (tmp := .t2) (hi := .t3) (n := .t1) (off := 0)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rw [e1, hbr, hbw]; exact hX ▸ hin 0 (by decide))
      (by rw [e1, hbr, hbw]; exact hin 4 (by decide)))
      fun d ⟨d0, dk, dm, drd, dwr, dsp⟩ => wp_and fun e ue => WP.block_nil ?_
    refine ⟨?_, fun r h0 h2 h3 => ?_, by rw [ue.mem, dm], by rw [ue.rd, drd],
      by rw [ue.wr, dwr], by rw [ue.sp, dsp]⟩
    · rw [ue.gpr, d0, e1, dk _ (by decide) (by decide) (by decide), h8b, BitVec.add_zero]
    · rw [ue.other _ h0, dk r h0 h2 h3]

/-- The address of `V[j]`. -/
theorem vAt_mul (s₀ : State) (j : Nat) :
    BitVec.ofNat 64 j * BitVec.ofNat 64 (128 * rr s₀) + vP s₀ = vAt s₀ j := by
  rw [← BitVec.ofNat_mul, BitVec.add_comm, Nat.mul_comm]

/-- One iteration of step 3. -/
theorem step3_ok {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {i : Nat}
    (hi : i < NN s₀) {s : State} (h : Inv3 s₀ i s) :
    WP isa (step3 wide) s fun s' => Inv3 s₀ (i + 1) s' ∧ (s'.gpr .s7 != 0) = decide (i + 1 ≠ NN s₀) := by
  have lt := r_lt hp
  have pos := hp.pos
  have hN := NN_lt hp
  have hj := jOf_lt hp s.mem
  have e8 := cnt_mul wide (rr s₀)
  unfold step3
  refine WP.seq (WP.mono (j_ok hp h.s4 h.s6 h.s8 h.rd h.wr) fun a ⟨a0, ak, am, ard, awr, asp⟩ => ?_)
  refine WP.seq (wp_mul fun b ub => wp_add fun c uc => wp_mv fun d ud => wp_mv fun e ue =>
    count_ok (wide := wide) (t := .t3) (r := rr s₀)
      (by rw [ue.other _ (by decide), ud.other _ (by decide), uc.other _ (by decide),
        ub.other _ (by decide), ak _ (by decide) (by decide) (by decide) (by decide), h.s6]) lt
      fun f uf => WP.block_nil ?_)
  have rdf : f.rd = s₀.rd := by rw [uf.rd, ue.rd, ud.rd, uc.rd, ub.rd, ard, h.rd]
  have wrf : f.wr = s₀.wr := by rw [uf.wr, ue.wr, ud.wr, uc.wr, ub.wr, awr, h.wr]
  have spf : f.sp = s₀.sp := by rw [uf.sp, ue.sp, ud.sp, uc.sp, ub.sp, asp, h.sp]
  have mf : f.mem = s.mem := by rw [uf.mem, ue.mem, ud.mem, uc.mem, ub.mem, am]
  have kf : ∀ r ∈ preserved, f.gpr r = s.gpr r := fun r hr => by
    obtain ⟨-, -, -, -, h0, h1, h2, h3, -⟩ := pres_ne r hr
    rw [uf.other _ h3, ue.other _ h2, ud.other _ h0, uc.other _ h1, ub.other _ h1, ak r h0 h1 h2 h3]
  have h1 : f.gpr .t1 = vAt s₀ (jOf s₀ s.mem) := by
    rw [uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide), uc.gpr, ub.gpr,
      ub.other _ (by decide), a0, ak _ (by decide) (by decide) (by decide) (by decide),
      ak _ (by decide) (by decide) (by decide) (by decide), h.s5, h.s6, vAt_mul]
  refine WP.seq (WP.mono (xorLoop_ok (wide := wide) (x := bP s₀) (y := vAt s₀ (jOf s₀ s.mem))
    (d := tP s₀) (n := cnt wide (rr s₀)) (cnt_pos pos) (by rw [e8]; exact lt)
    (fun hw => ⟨(hp.al hw).1, vAt_al hp hw _, (hp.al hw).2.2⟩)
    (by rw [uf.other _ (by decide), ue.other _ (by decide), ud.gpr, uc.other _ (by decide),
      ub.other _ (by decide), ak _ (by decide) (by decide) (by decide) (by decide), h.s4])
    h1
    (by rw [uf.other _ (by decide), ue.gpr, ud.other _ (by decide), uc.other _ (by decide),
      ub.other _ (by decide), ak _ (by decide) (by decide) (by decide) (by decide), h.s9])
    uf.gpr
    (fun k hk => by rw [rdf, wrf]; exact b_unit hp hk)
    (fun k hk => by rw [rdf, wrf]; exact InRegions.right (v_unit hp hj hk))
    (fun k hk => by rw [wrf]; exact t_unit hp hk)
    (by rw [e8]; exact t_b hp) (by rw [e8]; exact (vAt_t hp hj).symm.sub_left t_sub'))
    fun t ⟨rdt, wrt, spt, gt, mt⟩ => ?_)
  rw [mf, e8] at mt
  have kt : ∀ r ∈ preserved, t.gpr r = s.gpr r := fun r hr => by
    obtain ⟨-, -, -, -, h0, h1, h2, h3, h4, h5⟩ := pres_ne r hr
    rw [gt r h0 h1 h2 h3 h4 h5, kf r hr]
  rw [blockMixTo_eq]
  refine WP.seq (WP.seq (wp_mv fun q1 v1 => ?_))
  have kq : ∀ r ∈ preserved, q1.gpr r = s.gpr r := fun r hr => by
    rw [v1.other _ (pres_ne r hr).1, kt r hr]
  refine bm_ok hp (A := tP s₀) (by rw [v1.gpr, kt _ (by decide), h.s9])
    (by rw [kq _ (by decide), h.s4]) (by rw [kq _ (by decide), h.s10])
    (by rw [kq _ (by decide), h.s6]) (by rw [v1.rd, rdt, rdf]) (by rw [v1.wr, wrt, wrf])
    (t_b hp) ((hp.t_s.sub_left t_sub').sub_right (bsv_sub s₀)) (t_nw hp)
    (fun hw => (hp.al hw).2.2) (InRegions.right (t_in hp)) fun s4 rd4 wr4 sp4 cs4 f4 b4 => ?_
  rw [v1.mem, mt] at f4 b4
  obtain ⟨F, K, V, X, J⟩ := mem3_ok hp hi h f4 b4
  have k4 : ∀ r ∈ preserved, s4.gpr r = s.gpr r := fun r hr => by
    rw [cs4 r hr, kq r hr]
  refine wp_subi (imm := 1) (by decide) fun s5 u5 => WP.block_nil ?_
  have k5 : ∀ r ∈ preserved, r ≠ .s7 → s5.gpr r = s.gpr r := fun r hr h1 => by
    rw [u5.other _ h1, k4 r hr]
  have e7 : s5.gpr .s7 = BitVec.ofNat 64 (NN s₀ - (i + 1)) := by
    rw [u5.gpr, k4 _ (by decide), h.s7, dec_count hi]
  refine ⟨⟨by omega, by rw [u5.rd, rd4, v1.rd, rdt, rdf], by rw [u5.wr, wr4, v1.wr, wrt, wrf],
    by rw [u5.sp, sp4, v1.sp, spt, spf],
    by rw [k5 _ (by decide) (by decide), h.s4],
    by rw [k5 _ (by decide) (by decide), h.s5],
    by rw [k5 _ (by decide) (by decide), h.s9],
    by rw [k5 _ (by decide) (by decide), h.s10],
    by rw [k5 _ (by decide) (by decide), h.s6], e7,
    by rw [k5 _ (by decide) (by decide), h.s8],
    by rw [u5.mem]; exact F, by rw [u5.mem]; exact K, by rw [u5.mem]; exact V,
    by rw [u5.mem]; exact X, by rw [u5.mem]; exact J,
    fun r hr => by
      rw [k5 r (mid_pres hr) (mid_ne hr (by decide)), h.keep r hr]⟩,
    by rw [e7, dec_ne hi hN]⟩

theorem loop3_ok {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {s : State}
    (h : Inv3 s₀ 0 s) : WP isa (.loop (step3 wide) (.nonzero .s7)) s (Inv3 s₀ (NN s₀)) :=
  count_loop (NN_pos hp) (Inv3 s₀) (fun _ hi _ h => step3_ok hp hi h) h

/-! ## The epilogue -/

theorem restore_ok {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {s : State} (h : Inv3 s₀ (NN s₀) s) :
    WP isa (.block rmEpilogue) s fun s' => s'.mem = s.mem ∧ s'.sp = s.sp ∧
      (∀ p ∈ rmSaved, s'.gpr p.1 = s₀.gpr p.1) ∧
      ∀ r, r ∉ rmSaved.map Prod.fst → s'.gpr r = s.gpr r :=
  WP.mono (Spill.restore_wp (b := .s10) hp.s_al h.s10 (by decide) (by decide) (fun p hp' => by
      rw [h.rd, h.wr, hp.rd, hp.wr]
      exact InRegions.of_mem (R := svR s₀) (by simp) (in_s s₀ (by revert p; decide)))
    h.kept.1) fun _ h' => ⟨h'.mem, h'.sp, h'.gpr, h'.other⟩

/-! ## The whole function -/

theorem correct {wide : Bool} {s₀ : State} (hp : Pre wide s₀) :
    WP isa (Impl.Scrypt.RISCV64.roMix wide) s₀ fun s' =>
      (∀ p ∈ rmSaved, s'.gpr p.1 = s₀.gpr p.1) ∧ s'.sp = s₀.sp ∧
      (∀ r ∈ mid, s'.gpr r = s₀.gpr r) ∧ (Proof.Scrypt.roMixRISCV64 wide).post s₀ s' := by
  unfold Impl.Scrypt.RISCV64.roMix
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (nloop_ok hp h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (setup2_ok hp h₂) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (loop2_ok hp h₃) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (mid_ok hp h₄) fun s₅ h₅ => ?_)
  refine WP.seq (WP.mono (loop3_ok hp h₅) fun s₆ h₆ => ?_)
  refine WP.mono (restore_ok hp h₆) fun s' ⟨hm', hsp', hg', ho'⟩ => ⟨hg', hsp'.trans h₆.sp,
    fun r hr => by
      rw [ho' r (by revert r; decide), h₆.keep r hr], ?_⟩
  show bytesAt s'.mem (bP s₀) (128 * rr s₀) = roMix (rr s₀) (NN s₀) (B s₀)
  rw [hm', ← h₆.x, Nat.sub_self]
  rfl

/-! # Constant time, up to the indices `j`

As on PPC64LE: we relate two runs (`RelCT`). Correctness determines our
registers from the public arguments, so they agree between the calls, where
the taint analysis proves each piece constant time; the calls are constant
time by scryptBlockMix's own proof. In step 3, the address of `V[j]` depends
on `j`, which the contract declares public: the two runs compute the same
`j`, since both compute their indices in order (`Inv3.js`) and agree on the
whole list. -/

/-! ## What each run knows -/

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  a0 : s₀.gpr .a0 = s₀'.gpr .a0
  a1 : s₀.gpr .a1 = s₀'.gpr .a1
  a2 : s₀.gpr .a2 = s₀'.gpr .a2
  a3 : s₀.gpr .a3 = s₀'.gpr .a3
  a4 : s₀.gpr .a4 = s₀'.gpr .a4
  a5 : s₀.gpr .a5 = s₀'.gpr .a5
  sp : s₀.sp = s₀'.sp

section
variable {s₀ s₀' : State} (hq : PubEq s₀ s₀')
include hq

theorem PubEq.rr : rr s₀ = rr s₀' := by simp only [RoMix.rr, hq.a1]
theorem PubEq.NN : NN s₀ = NN s₀' := by simp only [RoMix.NN, RoMix.vl, RoMix.rr, hq.a1, hq.a3]
theorem PubEq.vAt (i : Nat) : vAt s₀ i = vAt s₀' i := by
  simp only [RoMix.vAt, RoMix.vP, RoMix.rr, hq.a1, hq.a2]
theorem PubEq.tP : tP s₀ = tP s₀' := by simp only [RoMix.tP, hq.a4]

end

/-- The registers the loops keep, with `s8 = bp` and `s7 = q`. -/
structure KR (s₀ : State) (bp q : Addr) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  s4 : s.gpr .s4 = bP s₀
  s5 : s.gpr .s5 = vP s₀
  s9 : s.gpr .s9 = tP s₀
  s10 : s.gpr .s10 = sv s₀
  s6 : s.gpr .s6 = BitVec.ofNat 64 (128 * rr s₀)
  s7 : s.gpr .s7 = q
  s8 : s.gpr .s8 = bp

/-- The registers `KR` fixes. -/
abbrev kRegs : List Reg := [.s4, .s5, .s9, .s10, .s6, .s7, .s8]

theorem kRegs_ne : ∀ r ∈ kRegs, r ≠ .a0 ∧ r ≠ .a1 ∧ r ≠ .a2 ∧ r ≠ .a3 ∧ r ≠ .t0 ∧ r ≠ .t1 := by
  decide

theorem kRegs_pres : ∀ r ∈ kRegs, r ∈ preserved ∧ r ∉ linkRegs := by decide

theorem KR.keep {s₀ : State} {bp q : Addr} {s s' : State} (h : KR s₀ bp q s)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp)
    (hk : ∀ r ∈ kRegs, s'.gpr r = s.gpr r) : KR s₀ bp q s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, (hk _ (by decide)).trans h.s4,
    (hk _ (by decide)).trans h.s5, (hk _ (by decide)).trans h.s9, (hk _ (by decide)).trans h.s10,
    (hk _ (by decide)).trans h.s6, (hk _ (by decide)).trans h.s7, (hk _ (by decide)).trans h.s8⟩

/-- Whether an instruction writes none of `kRegs`. -/
def kFree (i : Instr) : Bool := kRegs.all fun r => dstOf i != some r

/-- `KR` survives code that writes none of its registers. -/
theorem KR.exec {c : Prog isa} (hc : c.allInstrs kFree = true) {s₀ : State} {bp q : Addr}
    {s s' : State} {t : List Leak} (he : Exec isa c s t s') (h : KR s₀ bp q s) : KR s₀ bp q s' := by
  obtain ⟨rd, wr, sp⟩ := Exec.rdwr he
  rw [Code.allInstrs_eq, List.all_eq_true] at hc
  refine h.keep rd wr sp fun r hr => Exec.gpr (fun i hi => ?_) he (.inr (kRegs_pres r hr).2)
  have := hc i hi
  simp only [kFree, List.all_eq_true] at this
  simpa using this r hr

theorem Inv2.kr {s₀ : State} {i : Nat} {s : State} (h : Inv2 s₀ i s) :
    KR s₀ (vAt s₀ i) (BitVec.ofNat 64 (NN s₀ - i)) s :=
  ⟨h.rd, h.wr, h.sp, h.s4, h.s5, h.s9, h.s10, h.s6, h.s7, h.s8⟩

theorem Inv3.kr {s₀ : State} {i : Nat} {s : State} (h : Inv3 s₀ i s) :
    KR s₀ (BitVec.ofNat 64 (NN s₀ - 1)) (BitVec.ofNat 64 (NN s₀ - i)) s :=
  ⟨h.rd, h.wr, h.sp, h.s4, h.s5, h.s9, h.s10, h.s6, h.s7, h.s8⟩

theorem agree_of {rs : List Reg} {s₁ s₂ : State} (hsp : s₁.sp = s₂.sp)
    (h : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) :
    VG.RISCV64.Taint.Agree (VG.RISCV64.Taint.ofRegs rs) s₁ s₂ :=
  ⟨hsp, fun r hr => h r (VG.RISCV64.Taint.mem_ofRegs.mp hr)⟩

/-- The registers `KR` fixes, and the stack pointer, agree in two runs. -/
theorem agree_K {s₀ s₀' : State} (hq : PubEq s₀ s₀') {bp q bp' q' : Addr} {s s' : State}
    (h : KR s₀ bp q s) (h' : KR s₀' bp' q' s') (hbp : bp = bp') (hq' : q = q') {extra : List Reg}
    (hx : ∀ r ∈ extra, s.gpr r = s'.gpr r) :
    VG.RISCV64.Taint.Agree (VG.RISCV64.Taint.ofRegs (extra ++ kRegs)) s s' := by
  refine agree_of (by rw [h.sp, h'.sp, hq.sp]) fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · exact hx r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.s4, h'.s4, bP, bP, hq.a0]
  · rw [h.s5, h'.s5, vP, vP, hq.a2]
  · rw [h.s9, h'.s9, hq.tP]
  · rw [h.s10, h'.s10, sv, sv, hq.a5]
  · rw [h.s6, h'.s6, hq.rr]
  · rw [h.s7, h'.s7, hq']
  · rw [h.s8, h'.s8, hbp]

/-- The arguments of a call of scryptBlockMix from `A` into `b`. -/
structure Args (s₀ : State) (A : Addr) (s : State) : Prop where
  a0 : s.gpr .a0 = A
  a1 : s.gpr .a1 = BitVec.ofNat 64 (rr s₀)
  a2 : s.gpr .a2 = bP s₀
  a3 : s.gpr .a3 = bsv s₀

/-- A block that may be the source of such a call. -/
structure SrcOK (wide : Bool) (s₀ : State) (A : Addr) : Prop where
  b : Region.Disjoint ⟨A, 128 * rr s₀⟩ ⟨bP s₀, 128 * rr s₀⟩
  w : Region.Disjoint ⟨A, 128 * rr s₀⟩ (bsvR s₀)
  nw : A.toNat + 128 * rr s₀ ≤ 2 ^ 64
  al : wide = true → A.toNat % 8 = 0
  inr : InRegions (s₀.rd ++ s₀.wr) A (128 * rr s₀)

theorem srcOK_v {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {i : Nat} (hi : i < NN s₀) :
    SrcOK wide s₀ (vAt s₀ i) :=
  ⟨(vAt_b hp hi).sub_right b_sub', (vAt_s hp hi).sub_right (bsv_sub s₀), vAt_nw hp hi,
    fun hw => vAt_al hp hw i, InRegions.right (vAt_in hp hi)⟩

theorem srcOK_t {wide : Bool} {s₀ : State} (hp : Pre wide s₀) : SrcOK wide s₀ (tP s₀) :=
  ⟨t_b hp, (hp.t_s.sub_left t_sub').sub_right (bsv_sub s₀), t_nw hp, fun hw => (hp.al hw).2.2,
    InRegions.right (t_in hp)⟩

theorem call_pre {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {A : Addr} (hA : SrcOK wide s₀ A)
    {bp q : Addr} {s : State} (h : KR s₀ bp q s) (ha : Args s₀ A s) :
    (Proof.Scrypt.blockMixRISCV64 wide).pre (s.callEntry.withRegions [⟨A, rr s₀ * 128⟩]
      [⟨bP s₀, rr s₀ * 128⟩, ⟨bsv s₀, 96⟩]) ∧
    Covers ([⟨A, rr s₀ * 128⟩] ++ [⟨bP s₀, rr s₀ * 128⟩, ⟨bsv s₀, 96⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨bP s₀, rr s₀ * 128⟩, ⟨bsv s₀, 96⟩] s.wr := by
  have lt := r_lt hp
  have er : (BitVec.ofNat 64 (rr s₀)).toNat = rr s₀ := toNat_ofNat_lt (by omega)
  have hw : Covers [⟨bP s₀, rr s₀ * 128⟩, ⟨bsv s₀, 96⟩] s.wr :=
    Covers.pair (Covers.one (by rw [h.wr]; exact b_in hp)) (Covers.one (by rw [h.wr]; exact bsv_in hp))
  refine ⟨?_, Covers.append_left (rs := [⟨A, rr s₀ * 128⟩])
    (Covers.one (by rw [h.rd, h.wr, rmul]; exact hA.inr)) hw.right, hw⟩
  simp only [Proof.Scrypt.blockMixRISCV64, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.callEntry_gpr _ (by decide : Reg.a0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.a2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.a3 ∉ linkRegs), ha.a0, ha.a1, ha.a2, ha.a3, er]
  exact ⟨trivial, trivial, by rw [rmul]; exact (hp.b_s.sub_left b_sub').sub_right (bsv_sub s₀),
    by rw [rmul]; exact hA.b, by rw [rmul]; exact hA.w, by rw [rmul]; exact hA.nw, hp.b_nw,
    by have := hp.s_nw; rw [toNat_add_ofNat _ (by omega)]; omega, hp.pos,
    Spill.al8 hp.s_al (by decide), fun hw => ⟨hA.al hw, (hp.al hw).1⟩⟩

theorem call_wp {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {A : Addr} (hA : SrcOK wide s₀ A)
    {bp q : Addr} {s : State} (h : KR s₀ bp q s) (ha : Args s₀ A s) :
    WP isa (.call (blockMixName wide) (Impl.Scrypt.RISCV64.blockMix wide)) s (KR s₀ bp q) := by
  have lt := r_lt hp
  exact blockMixCall_ok wide ha.a0 ha.a1 ha.a2 ha.a3 hp.pos lt
    (by rw [rmul]; exact (hp.b_s.sub_left b_sub').sub_right (bsv_sub s₀))
    (by rw [rmul]; exact hA.b) (by rw [rmul]; exact hA.w) (by rw [rmul]; exact hA.nw) hp.b_nw
    (by have := hp.s_nw; rw [toNat_add_ofNat _ (by omega)]; omega)
    (Spill.al8 hp.s_al (by decide)) (fun hw => ⟨hA.al hw, (hp.al hw).1⟩)
    (by rw [h.rd, h.wr, rmul]; exact hA.inr) (by rw [h.wr]; exact b_in hp)
    (by rw [h.wr]; exact bsv_in hp) fun _ rd wr sp cs _ _ =>
      h.keep rd wr sp fun r hr => cs r (kRegs_pres r hr).1

theorem call_rel {wide : Bool} {s₀ s₀' : State} (hp : Pre wide s₀) (hp' : Pre wide s₀')
    (hq : PubEq s₀ s₀') {A A' : Addr} (hA : SrcOK wide s₀ A) (hA' : SrcOK wide s₀' A') (hAA : A = A')
    {bp q bp' q' : Addr} :
    RelCT isa (fun s s' => (KR s₀ bp q s ∧ Args s₀ A s) ∧ (KR s₀' bp' q' s' ∧ Args s₀' A' s'))
      (.call (blockMixName wide) (Impl.Scrypt.RISCV64.blockMix wide))
      fun s s' => KR s₀ bp q s ∧ KR s₀' bp' q' s' := by
  subst hAA
  have eb : bP s₀' = bP s₀ := hq.a0.symm
  have es : bsv s₀' = bsv s₀ := by simp only [bsv, sv, hq.a5]
  have er : rr s₀' = rr s₀ := hq.rr.symm
  have call := RelCT.call (n := blockMixName wide) (P := fun s s' =>
      (KR s₀ bp q s ∧ Args s₀ A s) ∧ (KR s₀' bp' q' s' ∧ Args s₀' A s'))
    (BlockMix.blockMix_verified wide).1 (BlockMix.blockMix_verified wide).2.1 [⟨A, rr s₀ * 128⟩]
    [⟨bP s₀, rr s₀ * 128⟩, ⟨bsv s₀, 96⟩] fun s s' ⟨⟨h, ha⟩, ⟨h', ha'⟩⟩ => by
      obtain ⟨p₁, c₁, w₁⟩ := call_pre hp hA h ha
      obtain ⟨p₂, c₂, w₂⟩ := call_pre hp' hA' h' ha'
      rw [eb, es, er] at p₂ c₂ w₂
      refine ⟨p₁, p₂, ?_, c₁, w₁, c₂, w₂⟩
      simp only [Proof.Scrypt.blockMixRISCV64, State.withRegions_gpr, State.withRegions_sp,
        State.callEntry_sp, State.callEntry_gpr _ (by decide : Reg.a0 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.a1 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.a2 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.a3 ∉ linkRegs), ha.a0, ha.a1, ha.a2, ha.a3,
        ha'.a0, ha'.a1, ha'.a2, ha'.a3, eb, es, er, h.sp, h'.sp, hq.sp]
      exact ⟨trivial, trivial, trivial, trivial, trivial⟩
  exact (call.wp fun s s' h => ⟨call_wp hp hA h.1.1 h.1.2, call_wp hp' hA' h.2.1 h.2.2⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

/-! ## Relating pieces of code -/

/-- Code that writes none of `kRegs` keeps `KR` in both runs. -/
theorem RelCT.keepK {P : State → State → Prop} {c : Prog isa} (h : RelCT isa P c fun _ _ => True)
    (hc : c.allInstrs kFree = true) {s₀ s₀' : State} {bp q bp' q' : Addr}
    (hk : ∀ s s', P s s' → KR s₀ bp q s ∧ KR s₀' bp' q' s') :
    RelCT isa P c fun s s' => KR s₀ bp q s ∧ KR s₀' bp' q' s' :=
  fun _ _ _ _ _ _ hp e e' =>
    ⟨(h _ _ _ _ _ _ hp e e').1, KR.exec hc e (hk _ _ hp).1, KR.exec hc e' (hk _ _ hp).2⟩

theorem RelCT.assoc {P Q : State → State → Prop} {a b c : Prog isa}
    (h : RelCT isa P (.seq (.seq a b) c) Q) : RelCT isa P (.seq a (.seq b c)) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq a₁ bc₁ =>
    cases bc₁ with
    | seq b₁ c₁ =>
      cases e₂ with
      | seq a₂ bc₂ =>
        cases bc₂ with
        | seq b₂ c₂ =>
          obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq (.seq a₁ b₁) c₁) (.seq (.seq a₂ b₂) c₂)
          simp only [List.append_assoc] at ht
          exact ⟨ht, hq⟩

theorem RelCT.exists' {α : Type} {P : α → State → State → Prop} {c : Prog isa}
    {Q : State → State → Prop} (h : ∀ a, RelCT isa (P a) c Q) :
    RelCT isa (fun s s' => ∃ a, P a s s') c Q :=
  fun _ _ _ _ _ _ ⟨a, hp⟩ e e' => h a _ _ _ _ _ _ hp e e'

/-! ## Setting up the calls -/

theorem tail_wp {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {bp q A : Addr} {s : State}
    (h : KR s₀ bp q s) (hA : s.gpr .a0 = A) :
    WP isa (.block bmTail) s fun s' => KR s₀ bp q s' ∧ Args s₀ A s' := by
  have lt := r_lt hp
  refine wp_srl (by decide) fun a ua => wp_mv fun b ub => wp_addi (by decide) fun d ud =>
    WP.block_nil ⟨?_, ?_⟩
  · exact h.keep (by rw [ud.rd, ub.rd, ua.rd]) (by rw [ud.wr, ub.wr, ua.wr])
      (by rw [ud.sp, ub.sp, ua.sp]) fun r hr => by
        obtain ⟨-, h1, h2, h3, -⟩ := kRegs_ne r hr
        rw [ud.other _ h3, ub.other _ h2, ua.other _ h1]
  have h1 : a.gpr .a1 = BitVec.ofNat 64 (rr s₀) := by
    rw [ua.gpr, h.s6, shr_ofNat _ lt]; exact congrArg (BitVec.ofNat _) (by omega)
  exact ⟨by rw [ud.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide), hA],
    by rw [ud.other _ (by decide), ub.other _ (by decide), h1],
    by rw [ud.other _ (by decide), ub.gpr, ua.other _ (by decide), h.s4],
    by rw [ud.gpr, ub.other _ (by decide), ua.other _ (by decide), h.s10]⟩

theorem args2_wp {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {bp q : Addr} {s : State}
    (h : KR s₀ bp q s) :
    WP isa (.block ([mov .a0 .s8] ++ bmTail)) s fun s' => KR s₀ bp q s' ∧ Args s₀ bp s' :=
  wp_mv fun a ua => tail_wp hp
    (h.keep ua.rd ua.wr ua.sp fun r hr => ua.other r (kRegs_ne r hr).1) (by rw [ua.gpr, h.s8])

theorem args3_wp {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {bp q : Addr} {s : State}
    (h : KR s₀ bp q s) :
    WP isa (.block ([mov .a0 .s9] ++ bmTail)) s fun s' => KR s₀ bp q s' ∧ Args s₀ (tP s₀) s' :=
  wp_mv fun a ua => tail_wp hp
    (h.keep ua.rd ua.wr ua.sp fun r hr => ua.other r (kRegs_ne r hr).1) (by rw [ua.gpr, h.s9])

/-! ## The pieces the taint analysis proves, for both widths -/

theorem rel_ac (wide : Bool) {P : State → State → Prop}
    (hP : ∀ s s', P s s' → VG.RISCV64.Taint.Agree (VG.RISCV64.Taint.ofRegs ([] ++ kRegs)) s s') :
    RelCT isa P (.seq (.block [mov .t0 .s4, mov .t1 .s8, unitCount wide]) (copyLoop wide))
      fun _ _ => True := by
  cases wide
  · exact RelCT.taint (A := taint) _ hP (by taint_decide)
  · exact RelCT.taint (A := taint) _ hP (by taint_decide)

theorem rel_jb (wide : Bool) {P : State → State → Prop}
    (hP : ∀ s s', P s s' → VG.RISCV64.Taint.Agree (VG.RISCV64.Taint.ofRegs ([] ++ kRegs)) s s') :
    RelCT isa P (.block (jBlock wide)) fun _ _ => True := by
  cases wide
  · exact RelCT.taint (A := taint) _ hP (by taint_decide)
  · exact RelCT.taint (A := taint) _ hP (by taint_decide)

theorem rel_mx (wide : Bool) {P : State → State → Prop}
    (hP : ∀ s s', P s s' → VG.RISCV64.Taint.Agree (VG.RISCV64.Taint.ofRegs (([.t0] : List Reg) ++ kRegs)) s s') :
    RelCT isa P (.seq (.block [.mul .t1 .t0 .s6, .add .t1 .t1 .s5, mov .t0 .s4, mov .t2 .s9,
        if wide then .shift .srl .d .t3 .s6 3 else mov .t3 .s6]) (xorLoop wide)) fun _ _ => True := by
  cases wide
  · exact RelCT.taint (A := taint) _ hP (by taint_decide)
  · exact RelCT.taint (A := taint) _ hP (by taint_decide)

/-! ## Step 2, in two runs -/

theorem eval_s7 (s : State) : isa.eval (.nonzero .s7) s = some (s.gpr .s7 != 0) :=
  eval_nonzero s .s7

theorem step2_kFree (wide : Bool) :
    (Code.seq (.block [mov .t0 .s4, mov .t1 .s8, unitCount wide]) (copyLoop wide) : Prog isa).allInstrs
      kFree = true := by
  cases wide <;> decide

section
variable {wide : Bool} {s₀ s₀' : State} (hp : Pre wide s₀) (hp' : Pre wide s₀') (hq : PubEq s₀ s₀')
include hp hp' hq

theorem body2_rel {i : Nat} (hi : i < NN s₀) :
    RelCT isa (fun s s' => Inv2 s₀ i s ∧ Inv2 s₀' i s') (step2 wide)
      fun s s' => (Inv2 s₀ (i + 1) s ∧ (s.gpr .s7 != 0) = decide (i + 1 ≠ NN s₀)) ∧
        (Inv2 s₀' (i + 1) s' ∧ (s'.gpr .s7 != 0) = decide (i + 1 ≠ NN s₀')) := by
  have hi' : i < NN s₀' := hq.NN ▸ hi
  have ev : vAt s₀ i = vAt s₀' i := hq.vAt i
  have e15 : BitVec.ofNat 64 (NN s₀ - i) = BitVec.ofNat 64 (NN s₀' - i) := by rw [hq.NN]
  let K (t₀ t : State) : Prop := KR t₀ (vAt t₀ i) (BitVec.ofNat 64 (NN t₀ - i)) t
  have ac : RelCT isa (fun s s' => Inv2 s₀ i s ∧ Inv2 s₀' i s')
      (.seq (.block [mov .t0 .s4, mov .t1 .s8, unitCount wide]) (copyLoop wide))
      fun s s' => K s₀ s ∧ K s₀' s' :=
    RelCT.keepK (rel_ac wide (fun _ _ h => agree_K hq h.1.kr h.2.kr ev e15 (by simp)))
      (step2_kFree wide) fun _ _ h => ⟨h.1.kr, h.2.kr⟩
  have x : RelCT isa (fun s s' => K s₀ s ∧ K s₀' s')
      (.block ([mov .a0 .s8] ++ bmTail)) fun s s' =>
        (K s₀ s ∧ Args s₀ (vAt s₀ i) s) ∧ (K s₀' s' ∧ Args s₀' (vAt s₀' i) s') :=
    ((RelCT.taint (A := taint) (VG.RISCV64.Taint.ofRegs ([] ++ kRegs))
      (fun _ _ h => agree_K hq h.1 h.2 ev e15 (by simp)) (by taint_decide)).wp
      fun _ _ h => ⟨args2_wp hp h.1, args2_wp hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have cl := call_rel hp hp' hq (srcOK_v hp hi) (srcOK_v hp' hi') ev
    (bp := vAt s₀ i) (q := BitVec.ofNat 64 (NN s₀ - i)) (bp' := vAt s₀' i)
    (q' := BitVec.ofNat 64 (NN s₀' - i))
  have e : RelCT isa (fun s s' => K s₀ s ∧ K s₀' s')
      (.block [.add .s8 .s8 .s6, .addi .s7 .s7 (-1)]) fun _ _ => True :=
    RelCT.taint (A := taint) (VG.RISCV64.Taint.ofRegs ([] ++ kRegs))
      (fun _ _ h => agree_K hq h.1 h.2 ev e15 (by simp)) (by taint_decide)
  have body := RelCT.assoc (ac.seq ((x.seq cl).seq e))
  rw [← blockMixTo_eq] at body
  exact (body.wp fun _ _ h => ⟨step2_ok hp hi h.1, step2_ok hp' hi' h.2⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

theorem loop2_rel :
    RelCT isa (fun s s' => Inv2 s₀ 0 s ∧ Inv2 s₀' 0 s')
      (.loop (step2 wide) (.nonzero .s7))
      fun s s' => Inv2 s₀ (NN s₀) s ∧ Inv2 s₀' (NN s₀') s' := by
  have lp := RelCT.loop (M := isa) (body := step2 wide)
    (c := .nonzero .s7) (Q := fun s s' => Inv2 s₀ (NN s₀) s ∧ Inv2 s₀' (NN s₀') s')
    (fun n s s' => ∃ i, n = NN s₀ - i ∧ i < NN s₀ ∧ Inv2 s₀ i s ∧ Inv2 s₀' i s') (fun n => by
      intro s s' t t' u u' ⟨i, hn, hi, h, h'⟩ e e'
      obtain ⟨ht, ⟨j, z⟩, ⟨j', z'⟩⟩ := body2_rel hp hp' hq hi _ _ _ _ _ _ ⟨h, h'⟩ e e'
      beta_reduce
      rw [eval_s7, eval_s7, z, z', ← hq.NN]
      refine ⟨ht, rfl, fun hf => ?_, fun ht' => ?_⟩
      · have hl : i + 1 = NN s₀ := by simpa using hf
        exact ⟨hl ▸ j, hl ▸ j'⟩
      · have hl : i + 1 ≠ NN s₀ := by simpa using ht'
        exact ⟨NN s₀ - (i + 1), by omega, i + 1, rfl, by omega, j, j'⟩) (NN s₀)
  exact lp.mono (fun _ _ h => ⟨0, rfl, NN_pos hp, h.1, h.2⟩) fun _ _ h => h

end

/-! ## Step 3, in two runs -/

theorem j_wp {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {q : Addr} {s : State}
    (h : KR s₀ (BitVec.ofNat 64 (NN s₀ - 1)) q s) {j : Nat} (hj : jOf s₀ s.mem = j) :
    WP isa (.block (jBlock wide)) s fun s' =>
      KR s₀ (BitVec.ofNat 64 (NN s₀ - 1)) q s' ∧ s'.gpr .t0 = BitVec.ofNat 64 j :=
  WP.mono (j_ok hp h.s4 h.s6 h.s8 h.rd h.wr) fun _ ⟨u0, uk, _, urd, uwr, usp⟩ =>
    ⟨h.keep urd uwr usp fun r hr => by
        obtain ⟨-, -, -, -, h0, h1⟩ := kRegs_ne r hr
        exact uk r h0 h1 (by revert r hr; decide) (by revert r hr; decide),
      by rw [u0, hj]⟩

/-- The next index, from the ones still to come. -/
theorem drop_js {s₀ : State} {i : Nat} (hi : i < NN s₀) {s : State} (h : Inv3 s₀ i s) :
    ∃ rest, (Spec.Scrypt.roMixIndices (rr s₀) (NN s₀) (B s₀)).drop i = jOf s₀ s.mem :: rest := by
  have e : NN s₀ - i = NN s₀ - (i + 1) + 1 := by omega
  have hs := h.js
  rw [e, mixLoop_succ_snd] at hs
  exact ⟨_, hs.symm⟩

theorem step3_kFree (wide : Bool) :
    (Code.seq (.block [.mul .t1 .t0 .s6, .add .t1 .t1 .s5, mov .t0 .s4, mov .t2 .s9,
      if wide then .shift .srl .d .t3 .s6 3 else mov .t3 .s6]) (xorLoop wide) : Prog isa).allInstrs
      kFree = true := by
  cases wide <;> decide

section
variable {wide : Bool} {s₀ s₀' : State} (hp : Pre wide s₀) (hp' : Pre wide s₀') (hq : PubEq s₀ s₀')
include hp hp' hq

theorem body3_rel_j {i : Nat} (hi : i < NN s₀) (j : Nat) :
    RelCT isa (fun s s' => (Inv3 s₀ i s ∧ jOf s₀ s.mem = j) ∧ (Inv3 s₀' i s' ∧ jOf s₀' s'.mem = j))
      (step3 wide)
      fun s s' => (Inv3 s₀ (i + 1) s ∧ (s.gpr .s7 != 0) = decide (i + 1 ≠ NN s₀)) ∧
        (Inv3 s₀' (i + 1) s' ∧ (s'.gpr .s7 != 0) = decide (i + 1 ≠ NN s₀')) := by
  have hi' : i < NN s₀' := hq.NN ▸ hi
  have e1 : BitVec.ofNat 64 (NN s₀ - 1) = BitVec.ofNat 64 (NN s₀' - 1) := by rw [hq.NN]
  have e15 : BitVec.ofNat 64 (NN s₀ - i) = BitVec.ofNat 64 (NN s₀' - i) := by rw [hq.NN]
  let K (t₀ t : State) : Prop :=
    KR t₀ (BitVec.ofNat 64 (NN t₀ - 1)) (BitVec.ofNat 64 (NN t₀ - i)) t
  have jb : RelCT isa (fun s s' => (Inv3 s₀ i s ∧ jOf s₀ s.mem = j) ∧
        (Inv3 s₀' i s' ∧ jOf s₀' s'.mem = j)) (.block (jBlock wide)) fun s s' =>
        (K s₀ s ∧ s.gpr .t0 = BitVec.ofNat 64 j) ∧ (K s₀' s' ∧ s'.gpr .t0 = BitVec.ofNat 64 j) :=
    ((rel_jb wide (fun _ _ h => agree_K hq h.1.1.kr h.2.1.kr e1 e15 (by simp))).wp
      fun _ _ h => ⟨j_wp hp h.1.1.kr h.1.2, j_wp hp' h.2.1.kr h.2.2⟩).mono (fun _ _ h => h)
      fun _ _ h => h.2
  have mx : RelCT isa (fun s s' => (K s₀ s ∧ s.gpr .t0 = BitVec.ofNat 64 j) ∧
        (K s₀' s' ∧ s'.gpr .t0 = BitVec.ofNat 64 j))
      (.seq (.block [.mul .t1 .t0 .s6, .add .t1 .t1 .s5, mov .t0 .s4, mov .t2 .s9,
        if wide then .shift .srl .d .t3 .s6 3 else mov .t3 .s6]) (xorLoop wide))
      fun s s' => K s₀ s ∧ K s₀' s' :=
    RelCT.keepK (rel_mx wide
      (fun _ _ h => agree_K hq h.1.1 h.2.1 e1 e15 fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h.1.2, h.2.2]))
      (step3_kFree wide) fun _ _ h => ⟨h.1.1, h.2.1⟩
  have x : RelCT isa (fun s s' => K s₀ s ∧ K s₀' s')
      (.block ([mov .a0 .s9] ++ bmTail)) fun s s' =>
        (K s₀ s ∧ Args s₀ (tP s₀) s) ∧ (K s₀' s' ∧ Args s₀' (tP s₀') s') :=
    ((RelCT.taint (A := taint) (VG.RISCV64.Taint.ofRegs ([] ++ kRegs))
      (fun _ _ h => agree_K hq h.1 h.2 e1 e15 (by simp)) (by taint_decide)).wp
      fun _ _ h => ⟨args3_wp hp h.1, args3_wp hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have cl := call_rel hp hp' hq (srcOK_t hp) (srcOK_t hp') hq.tP
    (bp := BitVec.ofNat 64 (NN s₀ - 1)) (q := BitVec.ofNat 64 (NN s₀ - i))
    (bp' := BitVec.ofNat 64 (NN s₀' - 1)) (q' := BitVec.ofNat 64 (NN s₀' - i))
  have e : RelCT isa (fun s s' => K s₀ s ∧ K s₀' s') (.block [.addi .s7 .s7 (-1)])
      fun _ _ => True :=
    RelCT.taint (A := taint) (VG.RISCV64.Taint.ofRegs ([] ++ kRegs))
      (fun _ _ h => agree_K hq h.1 h.2 e1 e15 (by simp)) (by taint_decide)
  have body := jb.seq (RelCT.assoc (mx.seq ((x.seq cl).seq e)))
  rw [← blockMixTo_eq] at body
  exact (body.wp fun _ _ h => ⟨step3_ok hp hi h.1.1, step3_ok hp' hi' h.2.1⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

variable (hL : Spec.Scrypt.roMixIndices (rr s₀) (NN s₀) (B s₀) =
  Spec.Scrypt.roMixIndices (rr s₀') (NN s₀') (B s₀'))
include hL

theorem body3_rel {i : Nat} (hi : i < NN s₀) :
    RelCT isa (fun s s' => Inv3 s₀ i s ∧ Inv3 s₀' i s') (step3 wide)
      fun s s' => (Inv3 s₀ (i + 1) s ∧ (s.gpr .s7 != 0) = decide (i + 1 ≠ NN s₀)) ∧
        (Inv3 s₀' (i + 1) s' ∧ (s'.gpr .s7 != 0) = decide (i + 1 ≠ NN s₀')) := by
  have hi' : i < NN s₀' := hq.NN ▸ hi
  refine (RelCT.exists' fun (j : Nat) => body3_rel_j hp hp' hq hi j).mono
    (fun s s' ⟨h, h'⟩ => ?_) fun _ _ h => h
  obtain ⟨r, hr⟩ := drop_js hi h
  obtain ⟨r', hr'⟩ := drop_js hi' h'
  rw [← hL, hr] at hr'
  have e := (List.cons.inj hr').1
  exact ⟨jOf s₀ s.mem, ⟨h, rfl⟩, ⟨h', e.symm⟩⟩

theorem loop3_rel :
    RelCT isa (fun s s' => Inv3 s₀ 0 s ∧ Inv3 s₀' 0 s')
      (.loop (step3 wide) (.nonzero .s7))
      fun s s' => Inv3 s₀ (NN s₀) s ∧ Inv3 s₀' (NN s₀') s' := by
  have lp := RelCT.loop (M := isa) (body := step3 wide)
    (c := .nonzero .s7) (Q := fun s s' => Inv3 s₀ (NN s₀) s ∧ Inv3 s₀' (NN s₀') s')
    (fun n s s' => ∃ i, n = NN s₀ - i ∧ i < NN s₀ ∧ Inv3 s₀ i s ∧ Inv3 s₀' i s') (fun n => by
      intro s s' t t' u u' ⟨i, hn, hi, h, h'⟩ e e'
      obtain ⟨ht, ⟨j, z⟩, ⟨j', z'⟩⟩ := body3_rel hp hp' hq hL hi _ _ _ _ _ _ ⟨h, h'⟩ e e'
      beta_reduce
      rw [eval_s7, eval_s7, z, z', ← hq.NN]
      refine ⟨ht, rfl, fun hf => ?_, fun ht' => ?_⟩
      · have hl : i + 1 = NN s₀ := by simpa using hf
        exact ⟨hl ▸ j, hl ▸ j'⟩
      · have hl : i + 1 ≠ NN s₀ := by simpa using ht'
        exact ⟨NN s₀ - (i + 1), by omega, i + 1, rfl, by omega, j, j'⟩) (NN s₀)
  exact lp.mono (fun _ _ h => ⟨0, rfl, NN_pos hp, h.1, h.2⟩) fun _ _ h => h

theorem roMix_rel :
    RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (Impl.Scrypt.RISCV64.roMix wide) fun _ _ => True := by
  unfold Impl.Scrypt.RISCV64.roMix
  have pro : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block rmPrologue)
      fun s s' => P1 s₀ s ∧ P1 s₀' s' :=
    ((RelCT.taint (A := taint) (VG.RISCV64.Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5])
      (P := fun s s' => s = s₀ ∧ s' = s₀') (fun _ _ ⟨e, e'⟩ => by
        rw [e, e']
        refine agree_of hq.sp fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · exact hq.a0
        · exact hq.a1
        · exact hq.a2
        · exact hq.a3
        · exact hq.a4
        · exact hq.a5) (c := .block rmPrologue) (by taint_decide)).wp
      (F₁ := P1 s₀) (F₂ := P1 s₀') fun _ _ ⟨e, e'⟩ => by
        rw [e, e']; exact ⟨prologue_ok hp, prologue_ok hp'⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have nl : RelCT isa (fun s s' => P1 s₀ s ∧ P1 s₀' s') nLoop fun s s' => N1 s₀ s ∧ N1 s₀' s' :=
    ((RelCT.taint (A := taint) (VG.RISCV64.Taint.ofRegs [.t0, .t1, .t2])
      (fun _ _ ⟨h, h'⟩ => agree_of (by rw [h.sp, h'.sp, hq.sp]) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h.t0, h'.t0, hq.rr]
        · rw [h.t1, h'.t1]
        · rw [h.t2, h'.t2, RoMix.vl, RoMix.vl, hq.a3]) (c := nLoop) (by taint_decide)).wp
      fun _ _ h => ⟨nloop_ok hp h.1, nloop_ok hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have st : RelCT isa (fun s s' => N1 s₀ s ∧ N1 s₀' s') (.block rmSetup)
      fun s s' => Inv2 s₀ 0 s ∧ Inv2 s₀' 0 s' :=
    ((RelCT.taint (A := taint) (VG.RISCV64.Taint.ofRegs [.t1, .s5, .s10])
      (fun _ _ ⟨h, h'⟩ => agree_of (by rw [h.sp, h'.sp, hq.sp]) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h.t1, h'.t1, hq.NN]
        · rw [h.s5, h'.s5, vP, vP, hq.a2]
        · rw [h.s10, h'.s10, sv, sv, hq.a5]) (c := .block rmSetup) (by taint_decide)).wp
      fun _ _ h => ⟨setup2_ok hp h.1, setup2_ok hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have md : RelCT isa (fun s s' => Inv2 s₀ (NN s₀) s ∧ Inv2 s₀' (NN s₀') s') (.block rmMid)
      fun s s' => Inv3 s₀ 0 s ∧ Inv3 s₀' 0 s' :=
    ((RelCT.taint (A := taint) (VG.RISCV64.Taint.ofRegs [.s10])
      (fun _ _ ⟨h, h'⟩ => agree_of (by rw [h.sp, h'.sp, hq.sp]) fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [h.s10, h'.s10, sv, sv, hq.a5]) (c := .block rmMid) (by taint_decide)).wp
      fun _ _ h => ⟨mid_ok hp h.1, mid_ok hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have epi : RelCT isa (fun s s' => Inv3 s₀ (NN s₀) s ∧ Inv3 s₀' (NN s₀') s') (.block rmEpilogue)
      fun _ _ => True :=
    RelCT.taint (A := taint) (VG.RISCV64.Taint.ofRegs [.s10])
      (fun _ _ h => agree_of (by rw [h.1.sp, h.2.sp, hq.sp]) fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [h.1.s10, h.2.s10, sv, sv, hq.a5]) (by taint_decide)
  exact pro.seq (nl.seq (st.seq ((loop2_rel hp hp' hq).seq
    (md.seq ((loop3_rel hp hp' hq hL).seq epi)))))

end

/-! ## Verified -/

theorem pubEq_of {wide : Bool} {s₁ s₂ : State} (h : (Proof.Scrypt.roMixRISCV64 wide).pub s₁ s₂) :
    PubEq s₁ s₂ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1⟩

theorem preserved_cases : ∀ r ∈ preserved, r ∈ rmSaved.map Prod.fst ∨ r ∈ mid := by
  decide

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 1 | .a2 => 0x2000 | .a3 => 1 | .a4 => 0x3000 | .a5 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 128⟩, ⟨0x2000, 128⟩, ⟨0x3000, 128⟩, ⟨0x4000, 168⟩]

theorem roMix_correct {wide : Bool} (s : State) (hs : (Proof.Scrypt.roMixRISCV64 wide).pre s) :
    ∃ t s', Exec isa (Impl.Scrypt.RISCV64.roMix wide) s t s' ∧ abiPreserved s s' ∧
      (Proof.Scrypt.roMixRISCV64 wide).post s s' := by
  obtain ⟨t, s', he, hk, hsp, hm, hpost⟩ := correct (pre_of hs)
  refine ⟨t, s', he, ⟨fun r hr => ?_, hsp, hk (.ra, 0) (by decide)⟩, hpost⟩
  rcases preserved_cases r hr with h | h
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
    exact hk p hp
  · exact hm r h

theorem roMix_ct (wide : Bool) : ConstantTime isa (Proof.Scrypt.roMixRISCV64 wide).pre
    (Proof.Scrypt.roMixRISCV64 wide).pub (Impl.Scrypt.RISCV64.roMix wide) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂
  exact (roMix_rel (pre_of h₁) (pre_of h₂) (pubEq_of hpub) hpub.2.2.2.2.2.2.2
    _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem roMix_verified (wide : Bool) :
    Verified RISCV64.target (Impl.Scrypt.RISCV64.roMix wide) (Proof.Scrypt.roMixRISCV64 wide) :=
  ⟨roMix_correct, roMix_ct wide, ⟨satState, rfl, rfl, Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), by decide, by decide, by decide, by decide, by decide,
    by decide, ⟨0, rfl⟩, by decide, fun _ => by decide⟩⟩

end VG.Proof.Scrypt.RISCV64.RoMix
