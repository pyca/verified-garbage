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

end VG.Proof.Scrypt.RISCV64.RoMix
