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

end VG.Proof.Scrypt.RISCV64.RoMix
