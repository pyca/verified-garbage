module

public import VerifiedGarbage.Proof.Scrypt.BlockMix
public import VerifiedGarbage.Proof.Scrypt.RISCV64.Common
public import VerifiedGarbage.Proof.Scrypt.RISCV64.Salsa
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
import VerifiedGarbage.Proof.Scrypt.Memory
import VerifiedGarbage.Proof.Scrypt.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Scrypt.BlockMix
meta import VerifiedGarbage.Proof.Scrypt.RISCV64.Common
meta import VerifiedGarbage.Proof.Scrypt.RISCV64.Salsa
meta import VerifiedGarbage.Proof.Framework.RISCV64.Spill
meta import VerifiedGarbage.Proof.Framework.RISCV64.Call
meta import VerifiedGarbage.Proof.Scrypt.Memory
meta import VerifiedGarbage.Proof.Scrypt.RISCV64.Lit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# scryptBlockMix on RISC-V

Untrusted: everything here is checked by Lean. The structure of the PPC64LE
proof (`Proof/Scrypt/PPC64LE/BlockMix.lean`), for both widths of the
accesses: the calls of Salsa20/8 by `WP.call` from its proof
(`salsaCall_ok`), the loop over the pairs (`Inv`), and the registers saved
in `save` (`Spill`). There is no stack frame: the return address is saved
with the callee-saved registers.
-/

@[expose] public section

namespace VG.Proof.Scrypt.RISCV64.BlockMix

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Scrypt.RISCV64 VG.WriteBytes
open VG.Spec.Scrypt (bytesAt blk salsa blockMix)
open VG.Spec.Pbkdf2 (xorBytes)
open VG.Proof.Scrypt (yAt xBefore yAt_eq xBefore_succ blockMix_eq flatMap_congr)
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt add_ofNat toNat_add_ofNat contains_off sub_off disj_off
  InRegions.of_mem frame_bytesAt bytesAt_writeBytes_self xorBytes_length bytesAt_length blk_bytesAt
  bytesAt_add bytesAt_blocks bytesAt_congr)

/-! ## A call of Salsa20/8 -/

theorem salsa_noFrames (wide : Bool) : (Impl.Scrypt.RISCV64.salsa wide).noFrames = true := by
  cases wide <;> lit_decide

/-- A call of Salsa20/8 on the block at `a0`, saving registers at `a1`. -/
theorem salsaCall_ok (wide : Bool) {s : State} {d sv : Addr} (hd : s.gpr .a0 = d)
    (hs : s.gpr .a1 = sv) (hds : Region.Disjoint ⟨d, 64⟩ ⟨sv, 40⟩) (hsa : sv.toNat % 8 = 0)
    (hda : wide = true → d.toNat % 4 = 0) (hind : InRegions s.wr d 64) (hins : InRegions s.wr sv 40)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      Frame [⟨d, 64⟩, ⟨sv, 40⟩] s.mem s'.mem →
      bytesAt s'.mem d 64 = salsa (bytesAt s.mem d 64) → Q s') :
    WP isa (.call (salsaName wide) (Impl.Scrypt.RISCV64.salsa wide)) s Q := by
  have c0 : s.callEntry.gpr .a0 = d := (State.callEntry_gpr _ (by decide)).trans hd
  have c1 : s.callEntry.gpr .a1 = sv := (State.callEntry_gpr _ (by decide)).trans hs
  have hw : Covers [⟨d, 64⟩, ⟨sv, 40⟩] s.wr := Covers.pair (Covers.one hind) (Covers.one hins)
  refine WP.call (k := Proof.Scrypt.salsaRISCV64 wide) (salsa_verified wide).1
    (rd := []) (wr := [⟨d, 64⟩, ⟨sv, 40⟩]) ?_ ?_ hw ?_ (salsa_noFrames wide)
  · simp only [Proof.Scrypt.salsaRISCV64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, c0, c1]
    exact ⟨trivial, trivial, hds, hsa, hda⟩
  · intro a n h
    obtain ⟨R, hR, hc⟩ := hw a n (by simpa using h)
    exact ⟨R, List.mem_append_right _ hR, hc⟩
  · intro s' hrd hwr hsp hf hcs _ hpost
    simp only [Proof.Scrypt.salsaRISCV64, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c0] at hpost
    exact hQ s' hrd hwr hsp hcs hf hpost

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev bP : Addr := s₀.gpr .a0
abbrev rr : Nat := (s₀.gpr .a1).toNat
abbrev yP : Addr := s₀.gpr .a2
abbrev sv : Addr := s₀.gpr .a3
abbrev bR : Region := ⟨bP s₀, rr s₀ * 128⟩
abbrev yR : Region := ⟨yP s₀, rr s₀ * 128⟩
abbrev svR : Region := ⟨sv s₀, 96⟩
/-- The input. -/
abbrev B : List Byte := bytesAt s₀.mem (bP s₀) (128 * rr s₀)

/-- `Y[2i]` goes to `y + 64 i`. -/
abbrev yE (i : Nat) : Addr := yP s₀ + BitVec.ofNat 64 (64 * i)
/-- `Y[2i + 1]` goes to `y + 64 (r + i)`. -/
abbrev yO (i : Nat) : Addr := yP s₀ + BitVec.ofNat 64 (64 * (rr s₀ + i))
/-- `B[2i]`. -/
abbrev bB (i : Nat) : Addr := bP s₀ + BitVec.ofNat 64 (128 * i)
/-- Where `X` is before the pair `(2k, 2k + 1)`. -/
def xP : Nat → Addr
  | 0 => bP s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64)
  | k + 1 => yO s₀ k

/-- Our return address and our caller's `s5`–`s10` are saved in `save`. -/
abbrev Saved (m : Mem) : Prop := Spill.Saved (sv s₀) s₀.gpr bmSaved m

/-- Where Salsa20/8 saves its caller's registers. -/
abbrev ssv : Addr := sv s₀ + BitVec.ofNat 64 56

end

/-- The callee-saved registers the code never writes. -/
def others : List Reg := [.s0, .s1, .s2, .s3, .s4, .s11]

structure Pre (wide : Bool) (s₀ : State) : Prop where
  rd : s₀.rd = [bR s₀]
  wr : s₀.wr = [yR s₀, svR s₀]
  y_s : (yR s₀).Disjoint (svR s₀)
  b_y : (bR s₀).Disjoint (yR s₀)
  b_s : (bR s₀).Disjoint (svR s₀)
  b_nw : (bP s₀).toNat + rr s₀ * 128 ≤ 2 ^ 64
  y_nw : (yP s₀).toNat + rr s₀ * 128 ≤ 2 ^ 64
  s_nw : (sv s₀).toNat + 96 ≤ 2 ^ 64
  pos : 0 < rr s₀
  s_al : (sv s₀).toNat % 8 = 0
  al : wide = true → (bP s₀).toNat % 8 = 0 ∧ (yP s₀).toNat % 8 = 0

theorem pre_of {wide : Bool} {s₀ : State} (h : (Proof.Scrypt.blockMixRISCV64 wide).pre s₀) :
    Pre wide s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

/-- An offset that is a multiple of 8 of an address that is one. -/
theorem al8 {p : Addr} (hp : p.toNat % 8 = 0) {o : Nat} (ho : o % 8 = 0) :
    (p + BitVec.ofNat 64 o).toNat % 8 = 0 := Spill.al8 hp ho

section
variable {wide : Bool} {s₀ : State} (hp : Pre wide s₀)
include hp

/-- `y` is not the whole address space, since `save` is not in it. -/
theorem r_lt : 128 * rr s₀ < 2 ^ 64 := by
  by_contra hc
  refine hp.y_s (sv s₀) ?_ (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega)
  simp only [Region.Contains]
  have := (sv s₀ - yP s₀).isLt
  omega

theorem in_y {o n : Nat} (h : o + n ≤ 128 * rr s₀) :
    (yR s₀).Contains (yP s₀ + BitVec.ofNat 64 o) n :=
  contains_off (by omega) (by have := r_lt hp; omega)

theorem in_b {o n : Nat} (h : o + n ≤ 128 * rr s₀) :
    (bR s₀).Contains (bP s₀ + BitVec.ofNat 64 o) n :=
  contains_off (by omega) (by have := r_lt hp; omega)

/-- Two parts of `y`. -/
theorem y_disj {o₁ n₁ o₂ n₂ : Nat} (h : o₁ + n₁ ≤ o₂ ∨ o₂ + n₂ ≤ o₁) (h₁ : o₁ + n₁ ≤ 128 * rr s₀)
    (h₂ : o₂ + n₂ ≤ 128 * rr s₀) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) :
    Region.Disjoint ⟨yP s₀ + BitVec.ofNat 64 o₁, n₁⟩ ⟨yP s₀ + BitVec.ofNat 64 o₂, n₂⟩ :=
  have := r_lt hp
  disj_off _ h (by omega) (by omega) (by omega) (by omega)

theorem y_sub {o n : Nat} (h : o + n ≤ 128 * rr s₀) : Region.Sub ⟨yP s₀ + BitVec.ofNat 64 o, n⟩ (yR s₀) :=
  sub_off (by omega) (by have := r_lt hp; omega)

theorem b_sub {o n : Nat} (h : o + n ≤ 128 * rr s₀) : Region.Sub ⟨bP s₀ + BitVec.ofNat 64 o, n⟩ (bR s₀) :=
  sub_off (by omega) (by have := r_lt hp; omega)

/-- A part of `y` and a part of `b`. -/
theorem yb_disj {o₁ n₁ o₂ n₂ : Nat} (h₁ : o₁ + n₁ ≤ 128 * rr s₀) (h₂ : o₂ + n₂ ≤ 128 * rr s₀) :
    Region.Disjoint ⟨yP s₀ + BitVec.ofNat 64 o₁, n₁⟩ ⟨bP s₀ + BitVec.ofNat 64 o₂, n₂⟩ :=
  (hp.b_y.symm.sub_left (y_sub hp h₁)).sub_right (b_sub hp h₂)

end

theorem in_s (s₀ : State) {o n : Nat} (h : o + n ≤ 96) :
    (svR s₀).Contains (sv s₀ + BitVec.ofNat 64 o) n :=
  contains_off h (by omega)

theorem s_sub (s₀ : State) {o n : Nat} (h : o + n ≤ 96) :
    Region.Sub ⟨sv s₀ + BitVec.ofNat 64 o, n⟩ (svR s₀) :=
  sub_off h (by omega)

/-! ## The loop invariant -/

/-- After `k` pairs. -/
structure Inv (s₀ : State) (k : Nat) (s : State) : Prop where
  k_le : k ≤ rr s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  s5 : s.gpr .s5 = bB s₀ k
  s6 : s.gpr .s6 = yE s₀ k
  s7 : s.gpr .s7 = yO s₀ k
  s10 : s.gpr .s10 = sv s₀
  s8 : s.gpr .s8 = BitVec.ofNat 64 (rr s₀ - k)
  s9 : s.gpr .s9 = xP s₀ k
  keep : ∀ r ∈ others, s.gpr r = s₀.gpr r
  frame : Frame [yR s₀, svR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem
  done : ∀ i < k, bytesAt s.mem (yE s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i) ∧
    bytesAt s.mem (yO s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i + 1)
  x : bytesAt s.mem (xP s₀ k) 64 = xBefore (B s₀) (rr s₀) (2 * k)

/-- The input is unchanged in any memory that differs from the initial one
only in `y` and `save`. -/
theorem b_frame {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {m : Mem}
    (hf : Frame [yR s₀, svR s₀] s₀.mem m) {o n : Nat} (ho : o + n ≤ 128 * rr s₀) :
    bytesAt m (bP s₀ + BitVec.ofNat 64 o) n = bytesAt s₀.mem (bP s₀ + BitVec.ofNat 64 o) n := by
  refine frame_bytesAt hf (fun r hr => ?_) (by have := r_lt hp; omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.b_y.sub_left (b_sub hp ho)
  · exact hp.b_s.sub_left (b_sub hp ho)

/-- Block `i` of the input. -/
theorem blk_B (s₀ : State) {i : Nat} (hi : i < 2 * rr s₀) :
    blk (B s₀) i = bytesAt s₀.mem (bP s₀ + BitVec.ofNat 64 (64 * i)) 64 :=
  blk_bytesAt _ _ (by omega)

/-! ## A call of Salsa20/8 on a block of `y` -/

theorem pres_ne : ∀ r ∈ preserved, r ≠ .a0 ∧ r ≠ .a1 ∧ r ≠ .t0 ∧ r ≠ .t1 := by decide

/-- A 64-byte slot of `y` at offset `o`. -/
abbrev slot (s₀ : State) (o : Nat) : Region := ⟨yP s₀ + BitVec.ofNat 64 o, 64⟩

/-- Where Salsa20/8 saves registers. -/
abbrev ssvR (s₀ : State) : Region := ⟨ssv s₀, 40⟩

theorem ssv_sub (s₀ : State) : Region.Sub (ssvR s₀) (svR s₀) := s_sub s₀ (by decide)

theorem salsaAt_ok {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {dR : Reg}
    {s : State} {o : Nat} (ho : o + 64 ≤ 128 * rr s₀) (ho8 : o % 8 = 0)
    (hd : s.gpr dR = yP s₀ + BitVec.ofNat 64 o)
    (h9 : s.gpr .s10 = sv s₀) (hwr : s.wr = s₀.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      Frame [slot s₀ o, ssvR s₀] s.mem s'.mem →
      bytesAt s'.mem (yP s₀ + BitVec.ofNat 64 o) 64 =
        salsa (bytesAt s.mem (yP s₀ + BitVec.ofNat 64 o) 64) → Q s') :
    WP isa (salsaAt wide dR) s Q := by
  unfold salsaAt
  refine WP.seq (wp_mv fun s₁ u₁ => wp_addi (by decide) fun s₂ u₂ => WP.block_nil ?_)
  have e₁ : s₂.gpr .a0 = yP s₀ + BitVec.ofNat 64 o := by rw [u₂.other _ (by decide), u₁.gpr, hd]
  have e₂ : s₂.gpr .a1 = ssv s₀ := by rw [u₂.gpr, u₁.other _ (by decide), h9]
  have e₃ : ∀ r ∈ preserved, s₂.gpr r = s.gpr r := fun r hr => by
    rw [u₂.other _ (pres_ne r hr).2.1, u₁.other _ (pres_ne r hr).1]
  have hsub : Region.Sub (slot s₀ o) (yR s₀) := y_sub hp ho
  have hw₂ : s₂.wr = [yR s₀, svR s₀] := by rw [u₂.wr, u₁.wr, hwr, hp.wr]
  have hin₁ : InRegions s₂.wr (yP s₀ + BitVec.ofNat 64 o) 64 := by
    rw [hw₂]; exact InRegions.of_mem (by simp) (in_y hp ho)
  have hin₂ : InRegions s₂.wr (ssv s₀) 40 := by
    rw [hw₂]; exact InRegions.of_mem (by simp) (in_s s₀ (by decide))
  refine salsaCall_ok wide e₁ e₂ (hp.y_s.sub_left hsub |>.sub_right (ssv_sub s₀))
    (al8 hp.s_al (by decide))
    (fun hw => by have := al8 (hp.al hw).2 ho8; omega) hin₁ hin₂
    fun s' hrd hwr' hsp hcs hf hb => hQ s' (by rw [hrd, u₂.rd, u₁.rd]) (by rw [hwr', u₂.wr, u₁.wr])
      (by rw [hsp, u₂.sp, u₁.sp]) (fun r hr => by rw [hcs r hr, e₃ r hr])
      (by rw [u₂.mem, u₁.mem] at hf; exact hf) (by rw [hb, u₂.mem, u₁.mem])

/-! ## One pair -/

theorem slot_s {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {o : Nat} (ho : o + 64 ≤ 128 * rr s₀) :
    (slot s₀ o).Disjoint (ssvR s₀) :=
  (hp.y_s.sub_left (y_sub hp ho)).sub_right (ssv_sub s₀)

/-- Where `X` is. -/
theorem xP_in {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {k : Nat} (hk : k < rr s₀) {s : State}
    (hrd : s.rd = [bR s₀]) (hwr : s.wr = [yR s₀, svR s₀]) :
    ∀ i < units wide, InRegions (s.rd ++ s.wr) (xP s₀ k + BitVec.ofNat 64 (unitB wide * i))
      (unitB wide) := by
  intro i hi
  have hu := units_mul wide
  have hle : unitB wide * i + unitB wide ≤ 64 := by
    rw [← hu, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
  rw [hrd, hwr]
  cases k with
  | zero =>
    simp only [xP]
    rw [add_ofNat]
    exact InRegions.of_mem (by simp) (in_b hp (by have := hp.pos; omega))
  | succ j =>
    simp only [xP]
    rw [add_ofNat]
    exact InRegions.of_mem (by simp) (in_y hp (by omega))

theorem xP_disj {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {k : Nat} (hk : k < rr s₀) :
    Region.Disjoint (slot s₀ (64 * k)) ⟨xP s₀ k, 64⟩ := by
  cases k with
  | zero => exact yb_disj hp (by omega) (by have := hp.pos; omega)
  | succ j => exact y_disj hp (by omega) (by omega) (by omega) (by omega) (by omega)

theorem xP_al {wide : Bool} {s₀ : State} (hp : Pre wide s₀) (hw : wide = true) (k : Nat) :
    (xP s₀ k).toNat % 8 = 0 := by
  cases k with
  | zero =>
    simp only [xP]
    exact al8 (hp.al hw).1 (by omega)
  | succ j =>
    simp only [xP]
    exact al8 (hp.al hw).2 (by omega)

/-- What a call keeps: our caller's saved registers. -/
theorem saved_keep {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {o : Nat} (ho : o + 64 ≤ 128 * rr s₀)
    {m m' : Mem} (hf : Frame [slot s₀ o, ssvR s₀] m m') (h : Saved s₀ m) : Saved s₀ m' :=
  Spill.Saved.frame h hf fun p hp' r hr => by
  have hp8 : p.2 + 8 ≤ 56 := by revert p; decide
  have hsub : Region.Sub ⟨sv s₀ + BitVec.ofNat 64 p.2, 8⟩ (svR s₀) := s_sub s₀ (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (hp.y_s.sub_left (y_sub hp ho)).sub_right hsub |>.symm
  · exact disj_off (sv s₀) (o₁ := p.2) (n₁ := 8) (o₂ := 56) (n₂ := 40) (by omega) (by omega)
      (by omega) (by omega) (by omega)

/-- What a call keeps: the other blocks of `y`. -/
theorem slot_keep {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {o o' : Nat} (ho : o + 64 ≤ 128 * rr s₀)
    (ho' : o' + 64 ≤ 128 * rr s₀) (hd : o' + 64 ≤ o ∨ o + 64 ≤ o') {m m' : Mem}
    (hf : Frame [slot s₀ o, ssvR s₀] m m') :
    bytesAt m' (yP s₀ + BitVec.ofNat 64 o') 64 = bytesAt m (yP s₀ + BitVec.ofNat 64 o') 64 := by
  refine frame_bytesAt hf (fun r hr => ?_) (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact y_disj hp hd ho' ho (by omega) (by omega)
  · exact slot_s hp ho'

theorem frame_big {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {o : Nat} (ho : o + 64 ≤ 128 * rr s₀)
    {m m' : Mem} (hf : Frame [slot s₀ o, ssvR s₀] m m') : Frame [yR s₀, svR s₀] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨yR s₀, List.mem_cons_self, y_sub hp ho⟩
    · exact ⟨svR s₀, List.mem_cons_of_mem _ List.mem_cons_self, ssv_sub s₀⟩

/-- Half a pair: `T = X xor B[i]` into block `o` of `y`, then Salsa20/8 of it. -/
theorem half_ok {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {dR xR sR : Reg}
    (hd : dR ≠ .t0 ∧ dR ≠ .t1) (hx : xR ≠ .t0 ∧ xR ≠ .t1) (hs : sR ≠ .t0 ∧ sR ≠ .t1)
    {o : Nat} (ho : o + 64 ≤ 128 * rr s₀) (ho8 : o % 8 = 0)
    {x : Addr} {ob : Nat} (hob : ob + 64 ≤ 128 * rr s₀) (hob8 : ob % 8 = 0) {s : State}
    (hrd : s.rd = [bR s₀]) (hwr : s.wr = [yR s₀, svR s₀])
    (gd : s.gpr dR = yP s₀ + BitVec.ofNat 64 o) (gx : s.gpr xR = x)
    (gs : s.gpr sR = bP s₀ + BitVec.ofNat 64 ob) (h9 : s.gpr .s10 = sv s₀)
    (hdx : Region.Disjoint (slot s₀ o) ⟨x, 64⟩) (hxa : wide = true → x.toNat % 8 = 0)
    (hinx : ∀ i < units wide,
      InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 (unitB wide * i)) (unitB wide))
    {P : Prog isa} {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      Frame [slot s₀ o, ssvR s₀] s.mem s'.mem →
      bytesAt s'.mem (yP s₀ + BitVec.ofNat 64 o) 64 =
        salsa (xorBytes (bytesAt s.mem x 64) (bytesAt s.mem (bP s₀ + BitVec.ofNat 64 ob) 64)) →
      WP isa P s' Q) :
    WP isa (.block (xor64 wide dR xR sR)) s fun s' => WP isa (.seq (salsaAt wide dR) P) s' Q := by
  have lt := r_lt hp
  have hu := units_mul wide
  have hle : ∀ i < units wide, unitB wide * i + unitB wide ≤ 64 := fun i hi => by
    rw [← hu, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
  rw [← List.append_nil (xor64 wide dR xR sR), xor64_eq]
  refine xor64_ok hd hx hs hdx (yb_disj hp ho hob)
    (fun hw => ⟨hxa hw, al8 (hp.al hw).1 hob8, al8 (hp.al hw).2 ho8⟩) (units wide)
    (Nat.le_refl _) [] s _ gd gx gs hinx
    (fun i hi => by
      rw [hrd, hwr, add_ofNat]
      exact InRegions.of_mem (by simp) (in_b hp (by have := hle i hi; omega)))
    (fun i hi => by
      rw [hwr, add_ofNat]; exact InRegions.of_mem (by simp) (in_y hp (by have := hle i hi; omega)))
    fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => WP.block_nil ?_
  rw [hu] at m₁
  have l1 : (xorBytes (bytesAt s.mem x 64) (bytesAt s.mem (bP s₀ + BitVec.ofNat 64 ob) 64)).length
      = 64 := by
    rw [xorBytes_length _ _ (by simp [bytesAt_length]), bytesAt_length]
  have f₁ : Frame [slot s₀ o] s.mem s₁.mem := by
    rw [m₁]; exact writeBytes_frame _ _ _ (by rw [l1]; exact Region.contains_self _ _)
  have hw := bytesAt_writeBytes_self s.mem (yP s₀ + BitVec.ofNat 64 o) _ (by rw [l1]; omega)
  rw [l1] at hw
  refine WP.seq (salsaAt_ok hp ho ho8 (by rw [g₁ _ hd.1 hd.2, gd])
    (by rw [g₁ _ (by decide) (by decide), h9]) (by rw [wr₁, hwr, hp.wr])
    fun s₂ rd₂ wr₂ sp₂ cs₂ f₂ b₂ => ?_)
  refine hQ s₂ (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]) (by rw [sp₂, sp₁])
    (fun r hr => by rw [cs₂ r hr, g₁ r (pres_ne r hr).2.2.1 (pres_ne r hr).2.2.2])
    ((f₁.mono (by simp)).trans f₂) ?_
  rw [b₂, m₁, hw]

/-- The state after both halves of pair `k`. -/
structure Mid (s₀ : State) (k : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  s5 : s.gpr .s5 = bP s₀ + BitVec.ofNat 64 (64 * (2 * k + 1))
  s6 : s.gpr .s6 = yE s₀ k
  s7 : s.gpr .s7 = yO s₀ k
  s10 : s.gpr .s10 = sv s₀
  s8 : s.gpr .s8 = BitVec.ofNat 64 (rr s₀ - k)
  keep : ∀ r ∈ others, s.gpr r = s₀.gpr r
  frame : Frame [yR s₀, svR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem
  done : ∀ i < k + 1, bytesAt s.mem (yE s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i) ∧
    bytesAt s.mem (yO s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i + 1)

/-- The memory after pair `k`. -/
theorem mem_ok {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {k : Nat} (hk : k < rr s₀)
    {s s₂ s₅ : State} (h : Inv s₀ k s)
    (f₂ : Frame [slot s₀ (64 * k), ssvR s₀] s.mem s₂.mem)
    (b₂ : bytesAt s₂.mem (yE s₀ k) 64 =
      salsa (xorBytes (bytesAt s.mem (xP s₀ k) 64) (bytesAt s.mem (bB s₀ k) 64)))
    (f₅ : Frame [slot s₀ (64 * (rr s₀ + k)), ssvR s₀] s₂.mem s₅.mem)
    (b₅ : bytesAt s₅.mem (yO s₀ k) 64 = salsa (xorBytes (bytesAt s₂.mem (yE s₀ k) 64)
      (bytesAt s₂.mem (bP s₀ + BitVec.ofNat 64 (64 * (2 * k + 1))) 64))) :
    Frame [yR s₀, svR s₀] s₀.mem s₅.mem ∧ Saved s₀ s₅.mem ∧
    ∀ i < k + 1, bytesAt s₅.mem (yE s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i) ∧
      bytesAt s₅.mem (yO s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i + 1) := by
  have lt := r_lt hp
  have oE : 64 * k + 64 ≤ 128 * rr s₀ := by omega
  have oO : 64 * (rr s₀ + k) + 64 ≤ 128 * rr s₀ := by omega
  have F₂ := h.frame.trans (frame_big hp oE f₂)
  have yE_eq : bytesAt s₂.mem (yE s₀ k) 64 = yAt (B s₀) (rr s₀) (2 * k) := by
    rw [b₂, h.x, b_frame hp h.frame (by omega : 128 * k + 64 ≤ 128 * rr s₀),
      show 128 * k = 64 * (2 * k) by omega, ← blk_B s₀ (by omega), yAt_eq]
  have hb : bytesAt s₂.mem (bP s₀ + BitVec.ofNat 64 (64 * (2 * k + 1))) 64 =
      blk (B s₀) (2 * k + 1) := by
    rw [blk_B s₀ (by omega)]
    exact b_frame hp F₂ (by omega)
  refine ⟨F₂.trans (frame_big hp oO f₅), saved_keep hp oO f₅ (saved_keep hp oE f₂ h.saved),
    fun i hi => ?_⟩
  by_cases hik : i = k
  · subst i
    refine ⟨?_, ?_⟩
    · rw [slot_keep hp oO oE (by omega) f₅, yE_eq]
    · rw [b₅, yE_eq, hb, yAt_eq (B s₀) (rr s₀) (2 * k + 1), xBefore_succ]
  · have hi' : i < k := by omega
    obtain ⟨d₁, d₂⟩ := h.done i hi'
    refine ⟨?_, ?_⟩
    · rw [slot_keep hp oO (by omega) (by omega) f₅, slot_keep hp oE (by omega) (by omega) f₂, d₁]
    · rw [slot_keep hp oO (by omega) (by omega) f₅, slot_keep hp oE (by omega) (by omega) f₂, d₂]

theorem others_pres : ∀ r ∈ others, r ∈ preserved ∧ r ≠ .s5 := by decide

/-- Both halves of pair `k`. -/
theorem halves_ok {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {k : Nat}
    (hk : k < rr s₀) {s : State} (h : Inv s₀ k s) {P : Prog isa} {Q : State → Prop}
    (hQ : ∀ s', Mid s₀ k s' → WP isa P s' Q) :
    WP isa (.seq (.block (xor64 wide .s6 .s9 .s5)) <| .seq (salsaAt wide .s6) <|
      .seq (.block (.addi .s5 .s5 64 :: xor64 wide .s7 .s6 .s5)) <| .seq (salsaAt wide .s7) P)
      s Q := by
  have lt := r_lt hp
  have hrd : s.rd = [bR s₀] := by rw [h.rd, hp.rd]
  have hwr : s.wr = [yR s₀, svR s₀] := by rw [h.wr, hp.wr]
  have oE : 64 * k + 64 ≤ 128 * rr s₀ := by omega
  have oO : 64 * (rr s₀ + k) + 64 ≤ 128 * rr s₀ := by omega
  refine WP.seq (half_ok hp (by decide) (by decide) (by decide) oE (by omega) (ob := 128 * k)
    (by omega) (by omega) hrd hwr h.s6 h.s9 h.s5 h.s10 (xP_disj hp hk)
    (fun hw => xP_al hp hw k) (xP_in hp hk hrd hwr)
    fun s₂ rd₂ wr₂ sp₂ cs₂ f₂ b₂ => ?_)
  refine WP.seq (wp_addi (by decide) fun s₃ u₃ => ?_)
  have k3 : ∀ r, r ≠ .s5 → r ∈ preserved → s₃.gpr r = s.gpr r := fun r h1 h2 => by
    rw [u₃.other _ h1, cs₂ r h2]
  have e3 : s₃.gpr .s5 = bP s₀ + BitVec.ofNat 64 (64 * (2 * k + 1)) := by
    rw [u₃.gpr, cs₂ _ (by decide), h.s5, add_ofNat, show 128 * k + 64 = 64 * (2 * k + 1) by omega]
  have hrd₃ : s₃.rd = [bR s₀] := by rw [u₃.rd, rd₂, hrd]
  have hwr₃ : s₃.wr = [yR s₀, svR s₀] := by rw [u₃.wr, wr₂, hwr]
  have e5 : s₃.gpr .s6 = yE s₀ k := by rw [k3 _ (by decide) (by decide), h.s6]
  have hu := units_mul wide
  refine half_ok hp (by decide) (by decide) (by decide) oO (by omega) (ob := 64 * (2 * k + 1))
    (by omega) (by omega) hrd₃ hwr₃ (by rw [k3 _ (by decide) (by decide), h.s7]) e5 e3
    (by rw [k3 _ (by decide) (by decide), h.s10])
    (y_disj hp (by omega) oO oE (by omega) (by omega))
    (fun hw => al8 (hp.al hw).2 (by omega))
    (fun i hi => by
      have hle : unitB wide * i + unitB wide ≤ 64 := by
        rw [← hu, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
      rw [hrd₃, hwr₃, add_ofNat]; exact InRegions.of_mem (by simp) (in_y hp (by omega)))
    fun s₅ rd₅ wr₅ sp₅ cs₅ f₅ b₅ => ?_
  rw [u₃.mem] at f₅ b₅
  obtain ⟨F, S, D⟩ := mem_ok hp hk h f₂ b₂ f₅ b₅
  have k5 : ∀ r, r ≠ .s5 → r ∈ preserved → s₅.gpr r = s.gpr r := fun r h1 h2 => by
    rw [cs₅ r h2, k3 r h1 h2]
  exact hQ s₅ ⟨by rw [rd₅, hrd₃, hp.rd], by rw [wr₅, hwr₃, hp.wr],
    by rw [sp₅, u₃.sp, sp₂, h.sp],
    by rw [cs₅ _ (by decide), e3],
    by rw [k5 _ (by decide) (by decide), h.s6],
    by rw [k5 _ (by decide) (by decide), h.s7],
    by rw [k5 _ (by decide) (by decide), h.s10],
    by rw [k5 _ (by decide) (by decide), h.s8],
    fun r hr => by
      rw [k5 r (others_pres r hr).2 (others_pres r hr).1, h.keep r hr],
    F, S, D⟩

theorem sub_ofNat' {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 64 := by omega) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- The pointers move on. -/
theorem regs_ok {s₀ : State} {wide : Bool} (hp : Pre wide s₀) {k : Nat} (hk : k < rr s₀)
    {s : State} (h : Mid s₀ k s) :
    WP isa (.block [mov .s9 .s7, .addi .s5 .s5 64, .addi .s6 .s6 64,
      .addi .s7 .s7 64, .addi .s8 .s8 (-1)]) s (Inv s₀ (k + 1)) := by
  have lt := r_lt hp
  refine wp_mv fun s₆ u₆ => wp_addi (by decide) fun s₇ u₇ => wp_addi (by decide) fun s₈ u₈ =>
    wp_addi (by decide) fun s₉ u₉ => wp_subi (imm := 1) (by decide) fun s₁₀ u₁₀ => WP.block_nil ?_
  have m₁₀ : s₁₀.mem = s.mem := by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem]
  have g : ∀ r, r ≠ .s5 → r ≠ .s6 → r ≠ .s7 → r ≠ .s8 → r ≠ .s9 → s₁₀.gpr r = s.gpr r :=
    fun r h4 h5 h6 h7 h8 => by
      rw [u₁₀.other _ h7, u₉.other _ h6, u₈.other _ h5, u₇.other _ h4, u₆.other _ h8]
  refine ⟨(by omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, h.rd]
  · rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, h.wr]
  · rw [u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, h.sp]
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr,
      u₆.other _ (by decide), h.s5, add_ofNat, show 64 * (2 * k + 1) + 64 = 128 * (k + 1) by omega]
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide),
      u₆.other _ (by decide), h.s6, add_ofNat, show 64 * k + 64 = 64 * (k + 1) by omega]
  · rw [u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), h.s7, add_ofNat,
      show 64 * (rr s₀ + k) + 64 = 64 * (rr s₀ + (k + 1)) by omega]
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), h.s10]
  · rw [u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), h.s8, sub_ofNat' (by omega)]
    congr 1
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), u₆.gpr, h.s7]
    rfl
  · intro r hr
    have : r ≠ .s5 ∧ r ≠ .s6 ∧ r ≠ .s7 ∧ r ≠ .s8 ∧ r ≠ .s9 := by
      revert r; decide
    rw [g r this.1 this.2.1 this.2.2.1 this.2.2.2.1 this.2.2.2.2, h.keep r hr]
  · rw [m₁₀]; exact h.frame
  · rw [m₁₀]; exact h.saved
  · rw [m₁₀]; exact h.done
  · rw [m₁₀]
    show bytesAt s.mem (yO s₀ k) 64 = _
    rw [(h.done k (by omega)).2]
    rfl

theorem body_ok {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {k : Nat}
    (hk : k < rr s₀) {s : State} (h : Inv s₀ k s) : WP isa (bmBody wide) s (Inv s₀ (k + 1)) :=
  halves_ok hp hk h fun _ hm => regs_ok hp hk hm

/-! ## The prologue -/

/-- The memory after the prologue's stores. -/
abbrev saveMem (s₀ : State) : Mem := Spill.saveMem s₀.mem (sv s₀) s₀.gpr bmSaved

theorem saveMem_saved (s₀ : State) : Saved s₀ (saveMem s₀) := Spill.saveMem_saved (by decide) _ _ _

theorem saveMem_frame (s₀ : State) : Frame [svR s₀] s₀.mem (saveMem s₀) :=
  Spill.saveMem_frame_base (by decide) (by decide) _ _ _

theorem prologue_eq : bmPrologue = Spill.saveCode .a3 bmSaved ++
    ([mov .s8 .a1, mov .s5 .a0, mov .s6 .a2, mov .s10 .a3,
      .shift .sll .d .t1 .a1 6, .add .s7 .a2 .t1,
      .shift .sll .d .t1 .a1 7, .add .s9 .a0 .t1, .addi .s9 .s9 (-64)] : List Instr) := rfl

theorem save_ok {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s₁, s₁.gpr = s₀.gpr → s₁.rd = s₀.rd → s₁.wr = s₀.wr → s₁.sp = s₀.sp →
      s₁.mem = saveMem s₀ → WP isa (.block rest) s₁ Q) :
    WP isa (.block (Spill.saveCode .a3 bmSaved ++ rest)) s₀ Q :=
  Spill.save_ok hp.s_al (by decide) (fun p hp' => by
    rw [hp.wr]; exact InRegions.of_mem (by simp) (in_s s₀ (by revert p; decide)))
    (k _ rfl rfl rfl rfl rfl)

theorem shl_eq {x : BitVec 64} {n : Nat} (h : x.toNat * 2 ^ n < 2 ^ 64) :
    x <<< n = BitVec.ofNat 64 (x.toNat * 2 ^ n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, toNat_ofNat_lt h, Nat.shiftLeft_eq, Nat.mod_eq_of_lt h]

theorem add_sub64 (a : Addr) {n : Nat} (h : 64 ≤ n) :
    a + BitVec.ofNat 64 n - BitVec.ofNat 64 64 = a + BitVec.ofNat 64 (n - 64) := by
  rw [show n = (n - 64) + 64 by omega, BitVec.ofNat_add, ← BitVec.add_assoc, Nat.add_sub_cancel,
    BitVec.add_sub_cancel]

/-- The registers the loop starts with. -/
theorem setup_ok {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {s₁ : State} (g : s₁.gpr = s₀.gpr)
    (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr) (hsp : s₁.sp = s₀.sp) (hm : s₁.mem = saveMem s₀) :
    WP isa (.block [mov .s8 .a1, mov .s5 .a0, mov .s6 .a2, mov .s10 .a3,
      .shift .sll .d .t1 .a1 6, .add .s7 .a2 .t1,
      .shift .sll .d .t1 .a1 7, .add .s9 .a0 .t1, .addi .s9 .s9 (-64)]) s₁ (Inv s₀ 0) := by
  have lt : 128 * (s₀.gpr .a1).toNat < 2 ^ 64 := r_lt hp
  have pos := hp.pos
  refine wp_mv fun a ua => wp_mv fun b ub => wp_mv fun c uc => wp_mv fun d ud =>
    wp_sll (by decide) fun e ue => wp_add fun f uf => wp_sll (by decide) fun g' ug =>
    wp_add fun h uh => wp_subi (imm := 64) (by decide) fun i ui => WP.block_nil ?_
  have r1 : d.gpr .a1 = s₀.gpr .a1 := by
    rw [ud.other _ (by decide), uc.other _ (by decide), ub.other _ (by decide),
      ua.other _ (by decide), g]
  have e1 : e.gpr .t1 = BitVec.ofNat 64 (64 * rr s₀) := by
    rw [ue.gpr, r1, shl_eq (by simp; omega), Nat.mul_comm]
  have g1 : g'.gpr .t1 = BitVec.ofNat 64 (128 * rr s₀) := by
    rw [ug.gpr, uf.other _ (by decide), ue.other _ (by decide), r1, shl_eq (by simp; omega),
      Nat.mul_comm]
  have hm' : i.mem = saveMem s₀ := by
    rw [ui.mem, uh.mem, ug.mem, uf.mem, ue.mem, ud.mem, uc.mem, ub.mem, ua.mem, hm]
  have k : ∀ r, r ≠ .t1 → r ≠ .s5 → r ≠ .s6 → r ≠ .s7 → r ≠ .s10 → r ≠ .s8 → r ≠ .s9 →
      i.gpr r = s₀.gpr r := fun r h1 h4 h5 h6 h9 h7 h8 => by
    rw [ui.other _ h8, uh.other _ h8, ug.other _ h1, uf.other _ h6, ue.other _ h1,
      ud.other _ h9, uc.other _ h5, ub.other _ h4, ua.other _ h7, g]
  refine ⟨Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun i hi => absurd hi (by omega), ?_⟩
  · rw [ui.rd, uh.rd, ug.rd, uf.rd, ue.rd, ud.rd, uc.rd, ub.rd, ua.rd, hrd]
  · rw [ui.wr, uh.wr, ug.wr, uf.wr, ue.wr, ud.wr, uc.wr, ub.wr, ua.wr, hwr]
  · rw [ui.sp, uh.sp, ug.sp, uf.sp, ue.sp, ud.sp, uc.sp, ub.sp, ua.sp, hsp]
  · rw [ui.other _ (by decide), uh.other _ (by decide), ug.other _ (by decide),
      uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide),
      uc.other _ (by decide), ub.gpr, ua.other _ (by decide), g]
    simp
  · rw [ui.other _ (by decide), uh.other _ (by decide), ug.other _ (by decide),
      uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide), uc.gpr,
      ub.other _ (by decide), ua.other _ (by decide), g]
    simp
  · rw [ui.other _ (by decide), uh.other _ (by decide), ug.other _ (by decide), uf.gpr, e1,
      ue.other _ (by decide), ud.other _ (by decide), uc.other _ (by decide),
      ub.other _ (by decide), ua.other _ (by decide), g]
    simp
  · rw [ui.other _ (by decide), uh.other _ (by decide), ug.other _ (by decide),
      uf.other _ (by decide), ue.other _ (by decide), ud.gpr, uc.other _ (by decide),
      ub.other _ (by decide), ua.other _ (by decide), g]
  · rw [ui.other _ (by decide), uh.other _ (by decide), ug.other _ (by decide),
      uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide),
      uc.other _ (by decide), ub.other _ (by decide), ua.gpr, g]
    simp
  · rw [ui.gpr, uh.gpr, g1, ug.other _ (by decide), uf.other _ (by decide),
      ue.other _ (by decide), ud.other _ (by decide), uc.other _ (by decide),
      ub.other _ (by decide), ua.other _ (by decide), g, add_sub64 _ (by omega)]
    rfl
  · intro r hr
    have : r ≠ .t1 ∧ r ≠ .s5 ∧ r ≠ .s6 ∧ r ≠ .s7 ∧ r ≠ .s10 ∧ r ≠ .s8 ∧ r ≠ .s9 := by
      revert r; decide
    obtain ⟨h1, h4, h5, h6, h9, h7, h8⟩ := this
    exact k r h1 h4 h5 h6 h9 h7 h8
  · rw [hm']; exact (saveMem_frame s₀).mono (by simp)
  · rw [hm']; exact saveMem_saved s₀
  · rw [hm']
    show bytesAt (saveMem s₀) (bP s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64)) 64 =
      blk (B s₀) (2 * rr s₀ - 1)
    rw [blk_B s₀ (by omega), show 64 * (2 * rr s₀ - 1) = 128 * rr s₀ - 64 by omega]
    refine frame_bytesAt (saveMem_frame s₀) (fun r hr => ?_) (by omega)
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.b_s.sub_left (b_sub hp (by omega))

/-! ## The loop -/

theorem loop_ok {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {s : State}
    (h : Inv s₀ 0 s) : WP isa (.loop (bmBody wide) (.nonzero .s8)) s (Inv s₀ (rr s₀)) := by
  have lt := r_lt hp
  refine WP.loop (M := isa) (fun n s => ∃ k, n = rr s₀ - k ∧ k < rr s₀ ∧ Inv s₀ k s) ?_ (rr s₀) s
    ⟨0, rfl, hp.pos, h⟩
  rintro n s ⟨k, rfl, hk, hi⟩
  refine WP.mono (body_ok hp hk hi) fun s' hi' => ?_
  have hz : isa.eval (.nonzero .s8) s' = some (decide (rr s₀ - (k + 1) ≠ 0)) :=
    eval_nonzero_ofNat s' .s8 (by omega) hi'.s8
  by_cases hl : rr s₀ - (k + 1) = 0
  · refine .inl ⟨by rw [hz]; simp [hl], ?_⟩
    rwa [show k + 1 = rr s₀ by omega] at hi'
  · exact .inr ⟨by rw [hz]; simp [hl], rr s₀ - (k + 1), by omega, k + 1, rfl, by omega, hi'⟩

/-! ## The epilogue -/

theorem preserved_cases : ∀ r ∈ preserved, r ∈ bmSaved.map Prod.fst ∨ r ∈ others := by
  decide

theorem restore_ok {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {s : State} (h : Inv s₀ (rr s₀) s) :
    WP isa (.block bmEpilogue) s fun s' => s'.mem = s.mem ∧ s'.sp = s.sp ∧
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra :=
  WP.mono (Spill.restore_wp (b := .s10) hp.s_al h.s10 (by decide) (by decide) (fun p hp' => by
      rw [h.rd, h.wr, hp.rd, hp.wr]; exact InRegions.of_mem (by simp) (in_s s₀ (by revert p; decide)))
    h.saved) fun s' h' => ⟨h'.mem, h'.sp, fun r hr =>
      h'.gpr_of ((preserved_cases r hr).imp id (h.keep r)), h'.gpr_of (.inl (by decide))⟩

/-! ## The whole function -/

/-- The output, from the blocks the loop wrote. -/
theorem post_of {s₀ : State} {m : Mem}
    (h : ∀ i < rr s₀, bytesAt m (yE s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i) ∧
      bytesAt m (yO s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i + 1)) :
    bytesAt m (yP s₀) (128 * rr s₀) = blockMix (rr s₀) (B s₀) := by
  rw [blockMix_eq, show 128 * rr s₀ = 64 * rr s₀ + 64 * rr s₀ by omega, bytesAt_add,
    bytesAt_blocks, bytesAt_blocks]
  congr 1
  · refine flatMap_congr fun i hi => ?_
    rw [List.mem_range] at hi
    exact (h i hi).1
  · refine flatMap_congr fun i hi => ?_
    rw [List.mem_range] at hi
    rw [add_ofNat, ← Nat.mul_add]
    exact (h i hi).2

theorem correct {wide : Bool} {s₀ : State} (hp : Pre wide s₀) :
    WP isa (Impl.Scrypt.RISCV64.blockMix wide) s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧
      s'.sp = s₀.sp ∧ s'.gpr .ra = s₀.gpr .ra ∧
      bytesAt s'.mem (yP s₀) (128 * rr s₀) = Spec.Scrypt.blockMix (rr s₀) (B s₀) := by
  unfold Impl.Scrypt.RISCV64.blockMix
  refine WP.seq ?_
  rw [prologue_eq]
  refine save_ok hp fun s₁ g hrd hwr hsp hm => ?_
  refine WP.mono (setup_ok hp g hrd hwr hsp hm) fun s₂ h₂ => ?_
  refine WP.seq (WP.mono (loop_ok hp h₂) fun s₃ h₃ => ?_)
  refine WP.mono (restore_ok hp h₃) fun s' ⟨hm', hsp', hg', hra⟩ =>
    ⟨hg', hsp'.trans h₃.sp, hra, ?_⟩
  rw [hm']
  exact post_of fun i hi => h₃.done i hi

theorem blockMix_correct {wide : Bool} (s : State) (hs : (Proof.Scrypt.blockMixRISCV64 wide).pre s) :
    ∃ t s', Exec isa (Impl.Scrypt.RISCV64.blockMix wide) s t s' ∧ abiPreserved s s' ∧
      (Proof.Scrypt.blockMixRISCV64 wide).post s s' := by
  obtain ⟨t, s', he, hk, hsp, hra, hpost⟩ := correct (pre_of hs)
  exact ⟨t, s', he, ⟨hk, hsp, hra⟩, hpost⟩

theorem agree₀ {wide : Bool} {s₁ s₂ : State} (hpub : (Proof.Scrypt.blockMixRISCV64 wide).pub s₁ s₂) :
    VG.RISCV64.Taint.Agree (VG.RISCV64.Taint.ofRegs [.a0, .a1, .a2, .a3]) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.RISCV64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem blockMix_ct (wide : Bool) : ConstantTime isa (Proof.Scrypt.blockMixRISCV64 wide).pre
    (Proof.Scrypt.blockMixRISCV64 wide).pub (Impl.Scrypt.RISCV64.blockMix wide) := by
  cases wide
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
      (fun _ _ _ _ hp => agree₀ hp) (by taint_decide)
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
      (fun _ _ _ _ hp => agree₀ hp) (by taint_decide)

/-- A state satisfying the precondition (with no data). -/
def bmSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 1 | .a2 => 0x2000 | .a3 => 0x3000 | _ => 0
  sp := 0x5000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 128⟩, ⟨0x3000, 96⟩]

theorem blockMix_verified (wide : Bool) :
    Verified RISCV64.target (Impl.Scrypt.RISCV64.blockMix wide)
      (Proof.Scrypt.blockMixRISCV64 wide) :=
  ⟨blockMix_correct, blockMix_ct wide, ⟨bmSat, rfl, rfl, Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), by decide, by decide,
    by decide, by decide, by decide, fun _ => by decide⟩⟩

end VG.Proof.Scrypt.RISCV64.BlockMix
