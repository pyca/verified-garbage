import VerifiedGarbage.Proof.Scrypt.Whole
import VerifiedGarbage.Proof.MdStream.AArch64.Words
import VerifiedGarbage.Impl.Scrypt.AArch64.BlockMix
import VerifiedGarbage.Spec.Scrypt.Contract
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Scrypt.AArch64.Salsa
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Spill

/- Proofs formerly in `VerifiedGarbage.Proof.Scrypt.AArch64.Common`. -/
section

/-!
# scrypt on AArch64: common lemmas

The target-independent lemmas about addresses and bytes are in
`Proof/Scrypt/Memory.lean`; here are the weakest-precondition rules for the
AArch64 forms, and the 64-byte exclusive-or.
-/

namespace VG.Proof.Scrypt

open Spec.Scrypt

open VG.AArch64 in
/-- AArch64 contract for `vg_scrypt_blockmix(b = x0, r = x1, y = x2, ry = x3,
scratch = x4)`: if `ry = r > 0`, writes scryptBlockMix of the `128 r` bytes at
`b` to `y`. Its frame (saving `x30`) is the 16 bytes below the stack pointer. -/
def blockMixAArch64 : Contract AArch64.isa where
  pre s :=
    let r := (s.gpr .x1).toNat
    let b : Region := ⟨s.gpr .x0, r * 128⟩
    let y : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat * 128⟩
    let scratch : Region := ⟨s.gpr .x4, 128⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [b] ∧ s.wr = [y, scratch] ∧
    y.Disjoint scratch ∧ b.Disjoint y ∧ b.Disjoint scratch ∧
    16 ≤ s.sp.toNat ∧ stack.Disjoint b ∧ stack.Disjoint y ∧ stack.Disjoint scratch ∧
    (s.gpr .x0).toNat + r * 128 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat * 128 ≤ 2 ^ 64 ∧
    (s.gpr .x4).toNat + 128 ≤ 2 ^ 64 ∧
    s.gpr .x3 = s.gpr .x1 ∧ 0 < r
  post s s' := let r := (s.gpr .x1).toNat
    bytesAt s'.mem (s.gpr .x2) (128 * r) = blockMix r (bytesAt s.mem (s.gpr .x0) (128 * r))
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

open VG.AArch64 in
/-- AArch64 contract for `vg_scrypt_romix(b = x0, r = x1, v = x2, vlen = x3,
scratch = x4, slen = x5)`: if `r > 0`, `vlen = N r` for a power of two `N`,
and `slen = r + 2`, replaces the `128 r` bytes at `b` by their scryptROMix. It
has no frame (it saves `x30` in `scratch`); its calls of `vg_scrypt_blockmix`
use the 16 bytes below the stack pointer. The indices `j` of step 3 are
public. -/
def roMixAArch64 : Contract AArch64.isa where
  pre s :=
    let r := (s.gpr .x1).toNat
    let b : Region := ⟨s.gpr .x0, r * 128⟩
    let v : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat * 128⟩
    let scratch : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat * 128⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [] ∧ s.wr = [b, v, scratch] ∧
    b.Disjoint v ∧ b.Disjoint scratch ∧ v.Disjoint scratch ∧
    16 ≤ s.sp.toNat ∧ stack.Disjoint b ∧ stack.Disjoint v ∧ stack.Disjoint scratch ∧
    (s.gpr .x0).toNat + r * 128 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat * 128 ≤ 2 ^ 64 ∧
    (s.gpr .x4).toNat + (s.gpr .x5).toNat * 128 ≤ 2 ^ 64 ∧
    0 < r ∧ (s.gpr .x3).toNat % r = 0 ∧ ((s.gpr .x3).toNat / r).isPowerOfTwo ∧
    (s.gpr .x5).toNat = r + 2
  post s s' := let r := (s.gpr .x1).toNat
    bytesAt s'.mem (s.gpr .x0) (128 * r) =
      roMix r ((s.gpr .x3).toNat / r) (bytesAt s.mem (s.gpr .x0) (128 * r))
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
    s₁.sp = s₂.sp ∧
    roMixIndices (s₁.gpr .x1).toNat ((s₁.gpr .x3).toNat / (s₁.gpr .x1).toNat)
        (bytesAt s₁.mem (s₁.gpr .x0) (128 * (s₁.gpr .x1).toNat)) =
      roMixIndices (s₂.gpr .x1).toNat ((s₂.gpr .x3).toNat / (s₂.gpr .x1).toNat)
        (bytesAt s₂.mem (s₂.gpr .x0) (128 * (s₂.gpr .x1).toNat))

end VG.Proof.Scrypt

namespace VG.Proof.Scrypt.AArch64.BlockMix

open VG VG.AArch64 VG.Impl.Scrypt.AArch64
open VG.Spec.Scrypt (bytesAt blk salsa)
open VG.Spec.Pbkdf2 (xorBytes)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_append writeBytes_nil writeBytes_frame)
open VG.Proof.MdStream.AArch64 (Upd Mupd wp_ldr wp_str)
open VG.Proof.Scrypt.Memory (sub_off writeW_xor xorBytes_length bytesAt_length
  bytesAt_add bytesAt_writeBytes_sep)

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_eor {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n ^^^ s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .eor .x d n m :: is)) s Q :=
  Proof.MdStream.AArch64.WP.cons (s' := s.write .x d (s.gpr n ^^^ s.gpr m))
    (by simp [exec, State.read]) (k _ (Upd.write64 _ _ _))

theorem wp_lsl {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Upd s s' d (s.gpr n <<< sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.lsl .x d n sh :: is)) s Q :=
  Proof.MdStream.AArch64.WP.cons (s' := s.write .x d (s.gpr n <<< sh))
    (by simp [exec, h, State.read]) (k _ (Upd.write64 _ _ _))

end

/-- The first `n` words of `[dst] ← [x] xor [src]`, for 64-byte blocks `d`,
`x`, `y` in memory, where `d` overlaps neither of the others. The code uses
`x9` and `x10`. -/
theorem xor64_ok {dR xR sR : Reg} (hd : dR ≠ .x9 ∧ dR ≠ .x10) (hx : xR ≠ .x9 ∧ xR ≠ .x10)
    (hs : sR ≠ .x9 ∧ sR ≠ .x10)
    {d x y : Addr} (hdx : Region.Disjoint ⟨d, 64⟩ ⟨x, 64⟩) (hdy : Region.Disjoint ⟨d, 64⟩ ⟨y, 64⟩) :
    ∀ n ≤ 8, ∀ (rest : List Instr) (s : State) (Q : State → Prop),
    s.gpr dR = d → s.gpr xR = x → s.gpr sR = y →
    (∀ k < 8, InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 (8 * k)) 8) →
    (∀ k < 8, InRegions (s.rd ++ s.wr) (y + BitVec.ofNat 64 (8 * k)) 8) →
    (∀ k < 8, InRegions s.wr (d + BitVec.ofNat 64 (8 * k)) 8) →
    (∀ s', (∀ r, r ≠ .x9 → r ≠ .x10 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.sp = s.sp →
      s'.mem = VG.WriteBytes.writeBytes s.mem d (xorBytes (bytesAt s.mem x (8 * n)) (bytesAt s.mem y (8 * n))) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap (xorW dR xR sR) ++ rest)) s Q := by
  intro n
  induction n with
  | zero =>
    intro _ rest s Q _ _ _ _ _ _ k
    exact k s (fun _ _ _ => rfl) rfl rfl rfl (by simp [bytesAt, xorBytes, VG.WriteBytes.writeBytes_nil])
  | succ n ih =>
    intro hn rest s Q gd gx gy hinx hiny hout k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih (by omega) _ s Q gd gx gy hinx hiny hout fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
    simp only [xorW, List.cons_append, List.nil_append]
    refine wp_ldr (a := x + BitVec.ofNat 64 (8 * n)) ⟨by omega, by omega⟩
      (by rw [g₁ _ hx.1 hx.2, gx]) (by rw [rd₁, wr₁]; exact hinx n (by omega)) fun s₂ u₂ => ?_
    refine wp_ldr (a := y + BitVec.ofNat 64 (8 * n)) ⟨by omega, by omega⟩
      (by rw [u₂.other _ hs.1, g₁ _ hs.1 hs.2, gy])
      (by rw [u₂.rd, u₂.wr, rd₁, wr₁]; exact hiny n (by omega)) fun s₃ u₃ => ?_
    refine VG.Proof.Scrypt.AArch64.BlockMix.wp_eor fun s₄ u₄ => ?_
    refine wp_str (a := d + BitVec.ofNat 64 (8 * n)) ⟨by omega, by omega⟩
      (by rw [u₄.other _ hd.1, u₃.other _ hd.2, u₂.other _ hd.1, g₁ _ hd.1 hd.2, gd])
      (by rw [u₄.wr, u₃.wr, u₂.wr, wr₁]; exact hout n (by omega))
      fun s₅ u₅ => k s₅ (fun r h9 h10 => by
          rw [u₅.gpr, u₄.other r h9, u₃.other r h10, u₂.other r h9, g₁ r h9 h10])
        (by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]) (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁])
        (by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]) ?_
    have hl : (xorBytes (bytesAt s.mem x (8 * n)) (bytesAt s.mem y (8 * n))).length = 8 * n := by
      rw [xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]
    have sx : Region.Disjoint ⟨x + BitVec.ofNat 64 (8 * n), 8⟩ ⟨d, (xorBytes (bytesAt s.mem x (8 * n))
        (bytesAt s.mem y (8 * n))).length⟩ := by
      rw [hl]; exact (hdx.symm.sub_left (sub_off (by omega) (by omega))).sub_right
        (Region.sub_prefix (by omega))
    have sy : Region.Disjoint ⟨y + BitVec.ofNat 64 (8 * n), 8⟩ ⟨d, (xorBytes (bytesAt s.mem x (8 * n))
        (bytesAt s.mem y (8 * n))).length⟩ := by
      rw [hl]; exact (hdy.symm.sub_left (sub_off (by omega) (by omega))).sub_right
        (Region.sub_prefix (by omega))
    rw [u₅.mem, u₄.gpr, u₄.mem, u₃.gpr, u₃.other _ (by decide), u₂.gpr, u₃.mem, u₂.mem, writeW_xor,
      m₁, bytesAt_writeBytes_sep _ _ sx (by omega), bytesAt_writeBytes_sep _ _ sy (by omega)]
    have e := VG.WriteBytes.writeBytes_append s.mem d _ (xorBytes (bytesAt s.mem (x + BitVec.ofNat 64 (8 * n)) 8)
      (bytesAt s.mem (y + BitVec.ofNat 64 (8 * n)) 8))
      (by rw [hl, xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]; omega)
    rw [hl] at e
    rw [e, Nat.mul_succ, bytesAt_add, bytesAt_add, xorBytes, xorBytes, xorBytes,
      List.zipWith_append (by simp [bytesAt])]

end VG.Proof.Scrypt.AArch64.BlockMix

end

/- Proofs formerly in `VerifiedGarbage.Proof.Scrypt.AArch64.BlockMixVerified`. -/
section

/-!
# scryptBlockMix on AArch64: correctness of the loop

As on x86-64 (`Proof/Scrypt/X86_64/BlockMixCT.lean`), the calls of
`vg_salsa20_8` are used through `SalsaSpec`, what its proof says about a call;
the proof of this file holds for any code meeting it.

The function's body runs inside a frame saving `x30`; the state `s₀` here is
the one the body starts in, and the frame is handled in
this file.
-/

namespace VG.Proof.Scrypt.AArch64.BlockMix

open VG VG.AArch64 VG.Impl.Scrypt.AArch64
open VG.Spec.Scrypt (bytesAt blk salsa)
open VG.Spec.Pbkdf2 (xorBytes)
open VG.Proof.Scrypt (yAt xBefore yAt_eq xBefore_succ)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame)
open VG.Proof.MdStream.AArch64 (Upd wp_mov wp_addImm wp_subImm sub_ofNat)
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt add_ofNat toNat_add_ofNat contains_off sub_off disj_off
  InRegions.of_mem frame_bytesAt bytesAt_writeBytes_self xorBytes_length bytesAt_length blk_bytesAt)

/-! ## What a call of `vg_salsa20_8` does -/

/-- A call of `c` replaces the 64 bytes at `x0` by their Salsa20/8 Core,
with the 64 bytes at `x1` as working space. -/
def SalsaSpec (c : Prog isa) : Prop :=
  ∀ (s : State) (d sc : Addr), s.gpr .x0 = d → s.gpr .x1 = sc →
    Region.Disjoint ⟨d, 64⟩ ⟨sc, 64⟩ → InRegions s.wr d 64 → InRegions s.wr sc 64 →
    ∀ Q : State → Prop, (∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
        (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) →
        Frame [⟨d, 64⟩, ⟨sc, 64⟩] s.mem s'.mem →
        bytesAt s'.mem d 64 = salsa (bytesAt s.mem d 64) → Q s') →
    WP isa (.call "vg_salsa20_8" c) s Q

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev bP : Addr := s₀.gpr .x0
abbrev rr : Nat := (s₀.gpr .x1).toNat
abbrev yP : Addr := s₀.gpr .x2
abbrev sc : Addr := s₀.gpr .x4
abbrev bR : Region := ⟨VG.Proof.Scrypt.AArch64.BlockMix.bP s₀, VG.Proof.Scrypt.AArch64.BlockMix.rr s₀ * 128⟩
abbrev yR : Region := ⟨VG.Proof.Scrypt.AArch64.BlockMix.yP s₀, VG.Proof.Scrypt.AArch64.BlockMix.rr s₀ * 128⟩
abbrev scR : Region := ⟨VG.Proof.Scrypt.AArch64.BlockMix.sc s₀, 128⟩
/-- The input. -/
abbrev B : List Byte := bytesAt s₀.mem (VG.Proof.Scrypt.AArch64.BlockMix.bP s₀) (128 * VG.Proof.Scrypt.AArch64.BlockMix.rr s₀)

/-- `Y[2i]` goes to `y + 64 i`. -/
abbrev yE (i : Nat) : Addr := VG.Proof.Scrypt.AArch64.BlockMix.yP s₀ + BitVec.ofNat 64 (64 * i)
/-- `Y[2i + 1]` goes to `y + 64 (r + i)`. -/
abbrev yO (i : Nat) : Addr := VG.Proof.Scrypt.AArch64.BlockMix.yP s₀ + BitVec.ofNat 64 (64 * (VG.Proof.Scrypt.AArch64.BlockMix.rr s₀ + i))
/-- `B[2i]`. -/
abbrev bB (i : Nat) : Addr := VG.Proof.Scrypt.AArch64.BlockMix.bP s₀ + BitVec.ofNat 64 (128 * i)
/-- Where `X` is before the pair `(2k, 2k + 1)`. -/
def xP : Nat → Addr
  | 0 => VG.Proof.Scrypt.AArch64.BlockMix.bP s₀ + BitVec.ofNat 64 (128 * VG.Proof.Scrypt.AArch64.BlockMix.rr s₀ - 64)
  | k + 1 => VG.Proof.Scrypt.AArch64.BlockMix.yO s₀ k

/-- The caller's `x19`–`x24` are saved in the scratch space. -/
abbrev Saved (m : Mem) : Prop := Spill.Saved (VG.Proof.Scrypt.AArch64.BlockMix.sc s₀) s₀.gpr bmSaved m

end

/-- The callee-saved registers the code never writes (`x30` aside). -/
def others : List Reg := [.x25, .x26, .x27, .x28]

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.Scrypt.AArch64.BlockMix.bR s₀]
  wr : s₀.wr = [VG.Proof.Scrypt.AArch64.BlockMix.yR s₀, VG.Proof.Scrypt.AArch64.BlockMix.scR s₀]
  y_s : (VG.Proof.Scrypt.AArch64.BlockMix.yR s₀).Disjoint (VG.Proof.Scrypt.AArch64.BlockMix.scR s₀)
  b_y : (VG.Proof.Scrypt.AArch64.BlockMix.bR s₀).Disjoint (VG.Proof.Scrypt.AArch64.BlockMix.yR s₀)
  b_s : (VG.Proof.Scrypt.AArch64.BlockMix.bR s₀).Disjoint (VG.Proof.Scrypt.AArch64.BlockMix.scR s₀)
  b_nw : (VG.Proof.Scrypt.AArch64.BlockMix.bP s₀).toNat + VG.Proof.Scrypt.AArch64.BlockMix.rr s₀ * 128 ≤ 2 ^ 64
  y_nw : (VG.Proof.Scrypt.AArch64.BlockMix.yP s₀).toNat + VG.Proof.Scrypt.AArch64.BlockMix.rr s₀ * 128 ≤ 2 ^ 64
  s_nw : (VG.Proof.Scrypt.AArch64.BlockMix.sc s₀).toNat + 128 ≤ 2 ^ 64
  x3 : s₀.gpr .x3 = s₀.gpr .x1
  pos : 0 < VG.Proof.Scrypt.AArch64.BlockMix.rr s₀

section
variable {s₀ : State} (hp : VG.Proof.Scrypt.AArch64.BlockMix.Pre s₀)
include hp

/-- `y` is not the whole address space, since `scratch` is not in it. -/
theorem r_lt : 128 * VG.Proof.Scrypt.AArch64.BlockMix.rr s₀ < 2 ^ 64 := by
  by_contra hc
  refine hp.y_s (VG.Proof.Scrypt.AArch64.BlockMix.sc s₀) ?_ (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega)
  simp only [Region.Contains]
  have := (VG.Proof.Scrypt.AArch64.BlockMix.sc s₀ - VG.Proof.Scrypt.AArch64.BlockMix.yP s₀).isLt
  omega

theorem in_y {o n : Nat} (h : o + n ≤ 128 * VG.Proof.Scrypt.AArch64.BlockMix.rr s₀) :
    (VG.Proof.Scrypt.AArch64.BlockMix.yR s₀).Contains (VG.Proof.Scrypt.AArch64.BlockMix.yP s₀ + BitVec.ofNat 64 o) n :=
  contains_off (by omega) (by have := VG.Proof.Scrypt.AArch64.BlockMix.r_lt hp; omega)

theorem in_b {o n : Nat} (h : o + n ≤ 128 * VG.Proof.Scrypt.AArch64.BlockMix.rr s₀) :
    (VG.Proof.Scrypt.AArch64.BlockMix.bR s₀).Contains (VG.Proof.Scrypt.AArch64.BlockMix.bP s₀ + BitVec.ofNat 64 o) n :=
  contains_off (by omega) (by have := VG.Proof.Scrypt.AArch64.BlockMix.r_lt hp; omega)

/-- Two parts of `y`. -/
theorem y_disj {o₁ n₁ o₂ n₂ : Nat} (h : o₁ + n₁ ≤ o₂ ∨ o₂ + n₂ ≤ o₁) (h₁ : o₁ + n₁ ≤ 128 * VG.Proof.Scrypt.AArch64.BlockMix.rr s₀)
    (h₂ : o₂ + n₂ ≤ 128 * VG.Proof.Scrypt.AArch64.BlockMix.rr s₀) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) :
    Region.Disjoint ⟨VG.Proof.Scrypt.AArch64.BlockMix.yP s₀ + BitVec.ofNat 64 o₁, n₁⟩ ⟨VG.Proof.Scrypt.AArch64.BlockMix.yP s₀ + BitVec.ofNat 64 o₂, n₂⟩ :=
  have := VG.Proof.Scrypt.AArch64.BlockMix.r_lt hp
  disj_off _ h (by omega) (by omega) (by omega) (by omega)

theorem y_sub {o n : Nat} (h : o + n ≤ 128 * VG.Proof.Scrypt.AArch64.BlockMix.rr s₀) : Region.Sub ⟨VG.Proof.Scrypt.AArch64.BlockMix.yP s₀ + BitVec.ofNat 64 o, n⟩ (VG.Proof.Scrypt.AArch64.BlockMix.yR s₀) :=
  sub_off (by omega) (by have := VG.Proof.Scrypt.AArch64.BlockMix.r_lt hp; omega)

theorem b_sub {o n : Nat} (h : o + n ≤ 128 * VG.Proof.Scrypt.AArch64.BlockMix.rr s₀) : Region.Sub ⟨VG.Proof.Scrypt.AArch64.BlockMix.bP s₀ + BitVec.ofNat 64 o, n⟩ (VG.Proof.Scrypt.AArch64.BlockMix.bR s₀) :=
  sub_off (by omega) (by have := VG.Proof.Scrypt.AArch64.BlockMix.r_lt hp; omega)

/-- A part of `y` and a part of `b`. -/
theorem yb_disj {o₁ n₁ o₂ n₂ : Nat} (h₁ : o₁ + n₁ ≤ 128 * VG.Proof.Scrypt.AArch64.BlockMix.rr s₀) (h₂ : o₂ + n₂ ≤ 128 * VG.Proof.Scrypt.AArch64.BlockMix.rr s₀) :
    Region.Disjoint ⟨VG.Proof.Scrypt.AArch64.BlockMix.yP s₀ + BitVec.ofNat 64 o₁, n₁⟩ ⟨VG.Proof.Scrypt.AArch64.BlockMix.bP s₀ + BitVec.ofNat 64 o₂, n₂⟩ :=
  (hp.b_y.symm.sub_left (VG.Proof.Scrypt.AArch64.BlockMix.y_sub hp h₁)).sub_right (VG.Proof.Scrypt.AArch64.BlockMix.b_sub hp h₂)

end

theorem in_s (s₀ : State) {o n : Nat} (h : o + n ≤ 128) :
    (VG.Proof.Scrypt.AArch64.BlockMix.scR s₀).Contains (VG.Proof.Scrypt.AArch64.BlockMix.sc s₀ + BitVec.ofNat 64 o) n :=
  contains_off h (by omega)

theorem s_sub (s₀ : State) {o n : Nat} (h : o + n ≤ 128) :
    Region.Sub ⟨VG.Proof.Scrypt.AArch64.BlockMix.sc s₀ + BitVec.ofNat 64 o, n⟩ (VG.Proof.Scrypt.AArch64.BlockMix.scR s₀) :=
  sub_off h (by omega)

/-! ## The loop invariant -/

/-- After `k` pairs. -/
structure Inv (s₀ : State) (k : Nat) (s : State) : Prop where
  k_le : k ≤ VG.Proof.Scrypt.AArch64.BlockMix.rr s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x19 : s.gpr .x19 = VG.Proof.Scrypt.AArch64.BlockMix.bB s₀ k
  x20 : s.gpr .x20 = VG.Proof.Scrypt.AArch64.BlockMix.yE s₀ k
  x21 : s.gpr .x21 = VG.Proof.Scrypt.AArch64.BlockMix.yO s₀ k
  x22 : s.gpr .x22 = VG.Proof.Scrypt.AArch64.BlockMix.sc s₀
  x23 : s.gpr .x23 = BitVec.ofNat 64 (VG.Proof.Scrypt.AArch64.BlockMix.rr s₀ - k)
  x24 : s.gpr .x24 = VG.Proof.Scrypt.AArch64.BlockMix.xP s₀ k
  keep : ∀ r ∈ VG.Proof.Scrypt.AArch64.BlockMix.others, s.gpr r = s₀.gpr r
  frame : Frame [VG.Proof.Scrypt.AArch64.BlockMix.yR s₀, VG.Proof.Scrypt.AArch64.BlockMix.scR s₀] s₀.mem s.mem
  saved : VG.Proof.Scrypt.AArch64.BlockMix.Saved s₀ s.mem
  done : ∀ i < k, bytesAt s.mem (VG.Proof.Scrypt.AArch64.BlockMix.yE s₀ i) 64 = yAt (VG.Proof.Scrypt.AArch64.BlockMix.B s₀) (VG.Proof.Scrypt.AArch64.BlockMix.rr s₀) (2 * i) ∧
    bytesAt s.mem (VG.Proof.Scrypt.AArch64.BlockMix.yO s₀ i) 64 = yAt (VG.Proof.Scrypt.AArch64.BlockMix.B s₀) (VG.Proof.Scrypt.AArch64.BlockMix.rr s₀) (2 * i + 1)
  x : bytesAt s.mem (VG.Proof.Scrypt.AArch64.BlockMix.xP s₀ k) 64 = xBefore (VG.Proof.Scrypt.AArch64.BlockMix.B s₀) (VG.Proof.Scrypt.AArch64.BlockMix.rr s₀) (2 * k)

/-- The input is unchanged in any memory that differs from the initial one
only in `y` and `scratch`. -/
theorem b_frame {s₀ : State} (hp : VG.Proof.Scrypt.AArch64.BlockMix.Pre s₀) {m : Mem} (hf : Frame [VG.Proof.Scrypt.AArch64.BlockMix.yR s₀, VG.Proof.Scrypt.AArch64.BlockMix.scR s₀] s₀.mem m)
    {o n : Nat} (ho : o + n ≤ 128 * VG.Proof.Scrypt.AArch64.BlockMix.rr s₀) :
    bytesAt m (VG.Proof.Scrypt.AArch64.BlockMix.bP s₀ + BitVec.ofNat 64 o) n = bytesAt s₀.mem (VG.Proof.Scrypt.AArch64.BlockMix.bP s₀ + BitVec.ofNat 64 o) n := by
  refine frame_bytesAt hf (fun r hr => ?_) (by have := VG.Proof.Scrypt.AArch64.BlockMix.r_lt hp; omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.b_y.sub_left (VG.Proof.Scrypt.AArch64.BlockMix.b_sub hp ho)
  · exact hp.b_s.sub_left (VG.Proof.Scrypt.AArch64.BlockMix.b_sub hp ho)

/-- Block `i` of the input. -/
theorem blk_B (s₀ : State) {i : Nat} (hi : i < 2 * VG.Proof.Scrypt.AArch64.BlockMix.rr s₀) :
    blk (VG.Proof.Scrypt.AArch64.BlockMix.B s₀) i = bytesAt s₀.mem (VG.Proof.Scrypt.AArch64.BlockMix.bP s₀ + BitVec.ofNat 64 (64 * i)) 64 :=
  blk_bytesAt _ _ (by omega)

/-! ## A call of `vg_salsa20_8` on a block of `y` -/

theorem pres_ne : ∀ r ∈ preserved, r ≠ .x0 ∧ r ≠ .x1 ∧ r ≠ .x9 ∧ r ≠ .x10 := by decide

/-- A 64-byte slot of `y` at offset `o`. -/
abbrev slot (s₀ : State) (o : Nat) : Region := ⟨VG.Proof.Scrypt.AArch64.BlockMix.yP s₀ + BitVec.ofNat 64 o, 64⟩

theorem salsaAt_ok {c : Prog isa} (hS : VG.Proof.Scrypt.AArch64.BlockMix.SalsaSpec c) {s₀ : State} (hp : VG.Proof.Scrypt.AArch64.BlockMix.Pre s₀) {dR : Reg}
    {s : State} {o : Nat} (ho : o + 64 ≤ 128 * VG.Proof.Scrypt.AArch64.BlockMix.rr s₀) (hd : s.gpr dR = VG.Proof.Scrypt.AArch64.BlockMix.yP s₀ + BitVec.ofNat 64 o)
    (h22 : s.gpr .x22 = VG.Proof.Scrypt.AArch64.BlockMix.sc s₀) (hwr : s.wr = s₀.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) →
      Frame [VG.Proof.Scrypt.AArch64.BlockMix.slot s₀ o, ⟨VG.Proof.Scrypt.AArch64.BlockMix.sc s₀, 64⟩] s.mem s'.mem →
      bytesAt s'.mem (VG.Proof.Scrypt.AArch64.BlockMix.yP s₀ + BitVec.ofNat 64 o) 64 =
        salsa (bytesAt s.mem (VG.Proof.Scrypt.AArch64.BlockMix.yP s₀ + BitVec.ofNat 64 o) 64) → Q s') :
    WP isa (salsaAt c dR) s Q := by
  unfold salsaAt
  refine WP.seq (wp_mov fun s₁ u₁ => wp_mov fun s₂ u₂ => WP.block_nil ?_)
  have e₁ : s₂.gpr .x0 = VG.Proof.Scrypt.AArch64.BlockMix.yP s₀ + BitVec.ofNat 64 o := by rw [u₂.other _ (by decide), u₁.gpr, hd]
  have e₂ : s₂.gpr .x1 = VG.Proof.Scrypt.AArch64.BlockMix.sc s₀ := by rw [u₂.gpr, u₁.other _ (by decide), h22]
  have e₃ : ∀ r ∈ preserved, s₂.gpr r = s.gpr r := fun r hr => by
    rw [u₂.other _ (VG.Proof.Scrypt.AArch64.BlockMix.pres_ne r hr).2.1, u₁.other _ (VG.Proof.Scrypt.AArch64.BlockMix.pres_ne r hr).1]
  have hsub : Region.Sub (VG.Proof.Scrypt.AArch64.BlockMix.slot s₀ o) (VG.Proof.Scrypt.AArch64.BlockMix.yR s₀) := VG.Proof.Scrypt.AArch64.BlockMix.y_sub hp ho
  have hsub' : Region.Sub ⟨VG.Proof.Scrypt.AArch64.BlockMix.sc s₀, 64⟩ (VG.Proof.Scrypt.AArch64.BlockMix.scR s₀) := Region.sub_prefix (by omega)
  have hsc : (VG.Proof.Scrypt.AArch64.BlockMix.scR s₀).Contains (VG.Proof.Scrypt.AArch64.BlockMix.sc s₀) 64 := by
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  refine hS s₂ _ _ e₁ e₂ (hp.y_s.sub_left hsub |>.sub_right hsub')
    (by rw [u₂.wr, u₁.wr, hwr, hp.wr]; exact InRegions.of_mem (by simp) (VG.Proof.Scrypt.AArch64.BlockMix.in_y hp ho))
    (by rw [u₂.wr, u₁.wr, hwr, hp.wr]; exact InRegions.of_mem (R := VG.Proof.Scrypt.AArch64.BlockMix.scR s₀) (by simp) hsc)
    _ fun s' hrd hwr' hsp hcs hf hb => hQ s' (by rw [hrd, u₂.rd, u₁.rd]) (by rw [hwr', u₂.wr, u₁.wr])
      (by rw [hsp, u₂.sp, u₁.sp]) (fun r hr h30 => by rw [hcs r hr h30, e₃ r hr])
      (by rw [u₂.mem, u₁.mem] at hf; exact hf) (by rw [hb, u₂.mem, u₁.mem])

/-! ## One pair -/

theorem slot_s {s₀ : State} (hp : VG.Proof.Scrypt.AArch64.BlockMix.Pre s₀) {o : Nat} (ho : o + 64 ≤ 128 * VG.Proof.Scrypt.AArch64.BlockMix.rr s₀) :
    (VG.Proof.Scrypt.AArch64.BlockMix.slot s₀ o).Disjoint ⟨VG.Proof.Scrypt.AArch64.BlockMix.sc s₀, 64⟩ :=
  (hp.y_s.sub_left (VG.Proof.Scrypt.AArch64.BlockMix.y_sub hp ho)).sub_right (Region.sub_prefix (by omega))

/-- Where `X` is. -/
theorem xP_in {s₀ : State} (hp : VG.Proof.Scrypt.AArch64.BlockMix.Pre s₀) {k : Nat} (hk : k < VG.Proof.Scrypt.AArch64.BlockMix.rr s₀) {s : State}
    (hrd : s.rd = [VG.Proof.Scrypt.AArch64.BlockMix.bR s₀]) (hwr : s.wr = [VG.Proof.Scrypt.AArch64.BlockMix.yR s₀, VG.Proof.Scrypt.AArch64.BlockMix.scR s₀]) :
    ∀ i < 8, InRegions (s.rd ++ s.wr) (VG.Proof.Scrypt.AArch64.BlockMix.xP s₀ k + BitVec.ofNat 64 (8 * i)) 8 := by
  intro i hi
  rw [hrd, hwr]
  cases k with
  | zero =>
    simp only [VG.Proof.Scrypt.AArch64.BlockMix.xP]
    rw [add_ofNat]
    exact InRegions.of_mem (by simp) (VG.Proof.Scrypt.AArch64.BlockMix.in_b hp (by have := hp.pos; omega))
  | succ j =>
    simp only [VG.Proof.Scrypt.AArch64.BlockMix.xP]
    rw [add_ofNat]
    exact InRegions.of_mem (by simp) (VG.Proof.Scrypt.AArch64.BlockMix.in_y hp (by omega))

theorem xP_disj {s₀ : State} (hp : VG.Proof.Scrypt.AArch64.BlockMix.Pre s₀) {k : Nat} (hk : k < VG.Proof.Scrypt.AArch64.BlockMix.rr s₀) :
    Region.Disjoint (VG.Proof.Scrypt.AArch64.BlockMix.slot s₀ (64 * k)) ⟨VG.Proof.Scrypt.AArch64.BlockMix.xP s₀ k, 64⟩ := by
  cases k with
  | zero => exact VG.Proof.Scrypt.AArch64.BlockMix.yb_disj hp (by omega) (by have := hp.pos; omega)
  | succ j => exact VG.Proof.Scrypt.AArch64.BlockMix.y_disj hp (by omega) (by omega) (by omega) (by omega) (by omega)

/-- What a call's frame keeps: our caller's saved registers. -/
theorem saved_keep {s₀ : State} (hp : VG.Proof.Scrypt.AArch64.BlockMix.Pre s₀) {o : Nat} (ho : o + 64 ≤ 128 * VG.Proof.Scrypt.AArch64.BlockMix.rr s₀) {m m' : Mem}
    (hf : Frame [VG.Proof.Scrypt.AArch64.BlockMix.slot s₀ o, ⟨VG.Proof.Scrypt.AArch64.BlockMix.sc s₀, 64⟩] m m') (h : VG.Proof.Scrypt.AArch64.BlockMix.Saved s₀ m) : VG.Proof.Scrypt.AArch64.BlockMix.Saved s₀ m' :=
  Spill.Saved.frame h hf fun p hp' r hr => by
  have hp8 : p.2 + 8 ≤ 128 ∧ 64 ≤ p.2 := by revert p; decide
  have hsub : Region.Sub ⟨VG.Proof.Scrypt.AArch64.BlockMix.sc s₀ + BitVec.ofNat 64 p.2, 8⟩ (VG.Proof.Scrypt.AArch64.BlockMix.scR s₀) := VG.Proof.Scrypt.AArch64.BlockMix.s_sub s₀ (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (hp.y_s.sub_left (VG.Proof.Scrypt.AArch64.BlockMix.y_sub hp ho)).sub_right hsub |>.symm
  · have := disj_off (VG.Proof.Scrypt.AArch64.BlockMix.sc s₀) (o₁ := p.2) (n₁ := 8) (o₂ := 0) (n₂ := 64) (by omega) (by omega)
      (by omega) (by omega) (by omega)
    simpa using this

/-- What a call's frame keeps: the other blocks of `y`. -/
theorem slot_keep {s₀ : State} (hp : VG.Proof.Scrypt.AArch64.BlockMix.Pre s₀) {o o' : Nat} (ho : o + 64 ≤ 128 * VG.Proof.Scrypt.AArch64.BlockMix.rr s₀)
    (ho' : o' + 64 ≤ 128 * VG.Proof.Scrypt.AArch64.BlockMix.rr s₀) (hd : o' + 64 ≤ o ∨ o + 64 ≤ o') {m m' : Mem}
    (hf : Frame [VG.Proof.Scrypt.AArch64.BlockMix.slot s₀ o, ⟨VG.Proof.Scrypt.AArch64.BlockMix.sc s₀, 64⟩] m m') :
    bytesAt m' (VG.Proof.Scrypt.AArch64.BlockMix.yP s₀ + BitVec.ofNat 64 o') 64 = bytesAt m (VG.Proof.Scrypt.AArch64.BlockMix.yP s₀ + BitVec.ofNat 64 o') 64 := by
  refine frame_bytesAt hf (fun r hr => ?_) (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact VG.Proof.Scrypt.AArch64.BlockMix.y_disj hp hd ho' ho (by omega) (by omega)
  · exact VG.Proof.Scrypt.AArch64.BlockMix.slot_s hp ho'

theorem frame_big {s₀ : State} (hp : VG.Proof.Scrypt.AArch64.BlockMix.Pre s₀) {o : Nat} (ho : o + 64 ≤ 128 * VG.Proof.Scrypt.AArch64.BlockMix.rr s₀) {m m' : Mem}
    (hf : Frame [VG.Proof.Scrypt.AArch64.BlockMix.slot s₀ o, ⟨VG.Proof.Scrypt.AArch64.BlockMix.sc s₀, 64⟩] m m') : Frame [VG.Proof.Scrypt.AArch64.BlockMix.yR s₀, VG.Proof.Scrypt.AArch64.BlockMix.scR s₀] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨VG.Proof.Scrypt.AArch64.BlockMix.yR s₀, List.mem_cons_self, VG.Proof.Scrypt.AArch64.BlockMix.y_sub hp ho⟩
    · exact ⟨VG.Proof.Scrypt.AArch64.BlockMix.scR s₀, List.mem_cons_of_mem _ List.mem_cons_self, Region.sub_prefix (by omega)⟩

/-- Half a pair: `T = X xor B[i]` into block `o` of `y`, then Salsa20/8 of it. -/
theorem half_ok {c : Prog isa} (hS : VG.Proof.Scrypt.AArch64.BlockMix.SalsaSpec c) {s₀ : State} (hp : VG.Proof.Scrypt.AArch64.BlockMix.Pre s₀) {dR xR sR : Reg}
    (hd : dR ≠ .x9 ∧ dR ≠ .x10) (hx : xR ≠ .x9 ∧ xR ≠ .x10) (hs : sR ≠ .x9 ∧ sR ≠ .x10)
    {o : Nat} (ho : o + 64 ≤ 128 * VG.Proof.Scrypt.AArch64.BlockMix.rr s₀)
    {x : Addr} {ob : Nat} (hob : ob + 64 ≤ 128 * VG.Proof.Scrypt.AArch64.BlockMix.rr s₀) {s : State}
    (hrd : s.rd = [VG.Proof.Scrypt.AArch64.BlockMix.bR s₀]) (hwr : s.wr = [VG.Proof.Scrypt.AArch64.BlockMix.yR s₀, VG.Proof.Scrypt.AArch64.BlockMix.scR s₀])
    (gd : s.gpr dR = VG.Proof.Scrypt.AArch64.BlockMix.yP s₀ + BitVec.ofNat 64 o) (gx : s.gpr xR = x)
    (gs : s.gpr sR = VG.Proof.Scrypt.AArch64.BlockMix.bP s₀ + BitVec.ofNat 64 ob) (h22 : s.gpr .x22 = VG.Proof.Scrypt.AArch64.BlockMix.sc s₀)
    (hdx : Region.Disjoint (VG.Proof.Scrypt.AArch64.BlockMix.slot s₀ o) ⟨x, 64⟩)
    (hinx : ∀ i < 8, InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 (8 * i)) 8)
    {P : Prog isa} {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) →
      Frame [VG.Proof.Scrypt.AArch64.BlockMix.slot s₀ o, ⟨VG.Proof.Scrypt.AArch64.BlockMix.sc s₀, 64⟩] s.mem s'.mem →
      bytesAt s'.mem (VG.Proof.Scrypt.AArch64.BlockMix.yP s₀ + BitVec.ofNat 64 o) 64 =
        salsa (xorBytes (bytesAt s.mem x 64) (bytesAt s.mem (VG.Proof.Scrypt.AArch64.BlockMix.bP s₀ + BitVec.ofNat 64 ob) 64)) →
      WP isa P s' Q) :
    WP isa (.block (xor64 dR xR sR)) s fun s' => WP isa (.seq (salsaAt c dR) P) s' Q := by
  have lt := VG.Proof.Scrypt.AArch64.BlockMix.r_lt hp
  rw [← List.append_nil (xor64 dR xR sR)]
  refine VG.Proof.Scrypt.AArch64.BlockMix.xor64_ok hd hx hs hdx (VG.Proof.Scrypt.AArch64.BlockMix.yb_disj hp ho hob) 8 (Nat.le_refl _) [] s _ gd gx gs hinx
    (fun i hi => by
      rw [hrd, hwr, add_ofNat]; exact InRegions.of_mem (by simp) (VG.Proof.Scrypt.AArch64.BlockMix.in_b hp (by omega)))
    (fun i hi => by
      rw [hwr, add_ofNat]; exact InRegions.of_mem (by simp) (VG.Proof.Scrypt.AArch64.BlockMix.in_y hp (by omega)))
    fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => WP.block_nil ?_
  have l1 : (xorBytes (bytesAt s.mem x 64) (bytesAt s.mem (VG.Proof.Scrypt.AArch64.BlockMix.bP s₀ + BitVec.ofNat 64 ob) 64)).length
      = 64 := by
    rw [xorBytes_length _ _ (by simp [bytesAt_length]), bytesAt_length]
  have f₁ : Frame [VG.Proof.Scrypt.AArch64.BlockMix.slot s₀ o] s.mem s₁.mem := by
    rw [m₁]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [l1]; exact Region.contains_self _ _)
  have hw := bytesAt_writeBytes_self s.mem (VG.Proof.Scrypt.AArch64.BlockMix.yP s₀ + BitVec.ofNat 64 o) _ (by rw [l1]; omega)
  rw [l1] at hw
  refine WP.seq (VG.Proof.Scrypt.AArch64.BlockMix.salsaAt_ok hS hp ho (by rw [g₁ _ hd.1 hd.2, gd]) (by rw [g₁ _ (by decide) (by decide), h22])
    (by rw [wr₁, hwr, hp.wr]) fun s₂ rd₂ wr₂ sp₂ cs₂ f₂ b₂ => ?_)
  refine hQ s₂ (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]) (by rw [sp₂, sp₁])
    (fun r hr h30 => by rw [cs₂ r hr h30, g₁ r (VG.Proof.Scrypt.AArch64.BlockMix.pres_ne r hr).2.2.1 (VG.Proof.Scrypt.AArch64.BlockMix.pres_ne r hr).2.2.2])
    ((f₁.mono (by simp)).trans f₂) ?_
  rw [b₂, m₁, hw]

/-- The state after both halves of pair `k`. -/
structure Mid (s₀ : State) (k : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x19 : s.gpr .x19 = VG.Proof.Scrypt.AArch64.BlockMix.bP s₀ + BitVec.ofNat 64 (64 * (2 * k + 1))
  x20 : s.gpr .x20 = VG.Proof.Scrypt.AArch64.BlockMix.yE s₀ k
  x21 : s.gpr .x21 = VG.Proof.Scrypt.AArch64.BlockMix.yO s₀ k
  x22 : s.gpr .x22 = VG.Proof.Scrypt.AArch64.BlockMix.sc s₀
  x23 : s.gpr .x23 = BitVec.ofNat 64 (VG.Proof.Scrypt.AArch64.BlockMix.rr s₀ - k)
  keep : ∀ r ∈ VG.Proof.Scrypt.AArch64.BlockMix.others, s.gpr r = s₀.gpr r
  frame : Frame [VG.Proof.Scrypt.AArch64.BlockMix.yR s₀, VG.Proof.Scrypt.AArch64.BlockMix.scR s₀] s₀.mem s.mem
  saved : VG.Proof.Scrypt.AArch64.BlockMix.Saved s₀ s.mem
  done : ∀ i < k + 1, bytesAt s.mem (VG.Proof.Scrypt.AArch64.BlockMix.yE s₀ i) 64 = yAt (VG.Proof.Scrypt.AArch64.BlockMix.B s₀) (VG.Proof.Scrypt.AArch64.BlockMix.rr s₀) (2 * i) ∧
    bytesAt s.mem (VG.Proof.Scrypt.AArch64.BlockMix.yO s₀ i) 64 = yAt (VG.Proof.Scrypt.AArch64.BlockMix.B s₀) (VG.Proof.Scrypt.AArch64.BlockMix.rr s₀) (2 * i + 1)

/-- The memory after pair `k`. -/
theorem mem_ok {s₀ : State} (hp : VG.Proof.Scrypt.AArch64.BlockMix.Pre s₀) {k : Nat} (hk : k < VG.Proof.Scrypt.AArch64.BlockMix.rr s₀) {s s₂ s₅ : State}
    (h : VG.Proof.Scrypt.AArch64.BlockMix.Inv s₀ k s)
    (f₂ : Frame [VG.Proof.Scrypt.AArch64.BlockMix.slot s₀ (64 * k), ⟨VG.Proof.Scrypt.AArch64.BlockMix.sc s₀, 64⟩] s.mem s₂.mem)
    (b₂ : bytesAt s₂.mem (VG.Proof.Scrypt.AArch64.BlockMix.yE s₀ k) 64 =
      salsa (xorBytes (bytesAt s.mem (VG.Proof.Scrypt.AArch64.BlockMix.xP s₀ k) 64) (bytesAt s.mem (VG.Proof.Scrypt.AArch64.BlockMix.bB s₀ k) 64)))
    (f₅ : Frame [VG.Proof.Scrypt.AArch64.BlockMix.slot s₀ (64 * (VG.Proof.Scrypt.AArch64.BlockMix.rr s₀ + k)), ⟨VG.Proof.Scrypt.AArch64.BlockMix.sc s₀, 64⟩] s₂.mem s₅.mem)
    (b₅ : bytesAt s₅.mem (VG.Proof.Scrypt.AArch64.BlockMix.yO s₀ k) 64 = salsa (xorBytes (bytesAt s₂.mem (VG.Proof.Scrypt.AArch64.BlockMix.yE s₀ k) 64)
      (bytesAt s₂.mem (VG.Proof.Scrypt.AArch64.BlockMix.bP s₀ + BitVec.ofNat 64 (64 * (2 * k + 1))) 64))) :
    Frame [VG.Proof.Scrypt.AArch64.BlockMix.yR s₀, VG.Proof.Scrypt.AArch64.BlockMix.scR s₀] s₀.mem s₅.mem ∧ VG.Proof.Scrypt.AArch64.BlockMix.Saved s₀ s₅.mem ∧
    ∀ i < k + 1, bytesAt s₅.mem (VG.Proof.Scrypt.AArch64.BlockMix.yE s₀ i) 64 = yAt (VG.Proof.Scrypt.AArch64.BlockMix.B s₀) (VG.Proof.Scrypt.AArch64.BlockMix.rr s₀) (2 * i) ∧
      bytesAt s₅.mem (VG.Proof.Scrypt.AArch64.BlockMix.yO s₀ i) 64 = yAt (VG.Proof.Scrypt.AArch64.BlockMix.B s₀) (VG.Proof.Scrypt.AArch64.BlockMix.rr s₀) (2 * i + 1) := by
  have lt := VG.Proof.Scrypt.AArch64.BlockMix.r_lt hp
  have oE : 64 * k + 64 ≤ 128 * VG.Proof.Scrypt.AArch64.BlockMix.rr s₀ := by omega
  have oO : 64 * (VG.Proof.Scrypt.AArch64.BlockMix.rr s₀ + k) + 64 ≤ 128 * VG.Proof.Scrypt.AArch64.BlockMix.rr s₀ := by omega
  have F₂ := h.frame.trans (VG.Proof.Scrypt.AArch64.BlockMix.frame_big hp oE f₂)
  have yE_eq : bytesAt s₂.mem (VG.Proof.Scrypt.AArch64.BlockMix.yE s₀ k) 64 = yAt (VG.Proof.Scrypt.AArch64.BlockMix.B s₀) (VG.Proof.Scrypt.AArch64.BlockMix.rr s₀) (2 * k) := by
    rw [b₂, h.x, VG.Proof.Scrypt.AArch64.BlockMix.b_frame hp h.frame (by omega : 128 * k + 64 ≤ 128 * rr s₀),
      show 128 * k = 64 * (2 * k) by omega, ← VG.Proof.Scrypt.AArch64.BlockMix.blk_B s₀ (by omega), yAt_eq]
  have hb : bytesAt s₂.mem (VG.Proof.Scrypt.AArch64.BlockMix.bP s₀ + BitVec.ofNat 64 (64 * (2 * k + 1))) 64 =
      blk (VG.Proof.Scrypt.AArch64.BlockMix.B s₀) (2 * k + 1) := by
    rw [VG.Proof.Scrypt.AArch64.BlockMix.blk_B s₀ (by omega)]
    exact VG.Proof.Scrypt.AArch64.BlockMix.b_frame hp F₂ (by omega)
  refine ⟨F₂.trans (VG.Proof.Scrypt.AArch64.BlockMix.frame_big hp oO f₅), VG.Proof.Scrypt.AArch64.BlockMix.saved_keep hp oO f₅ (VG.Proof.Scrypt.AArch64.BlockMix.saved_keep hp oE f₂ h.saved),
    fun i hi => ?_⟩
  by_cases hik : i = k
  · subst i
    refine ⟨?_, ?_⟩
    · rw [VG.Proof.Scrypt.AArch64.BlockMix.slot_keep hp oO oE (by omega) f₅, yE_eq]
    · rw [b₅, yE_eq, hb, yAt_eq (VG.Proof.Scrypt.AArch64.BlockMix.B s₀) (VG.Proof.Scrypt.AArch64.BlockMix.rr s₀) (2 * k + 1), xBefore_succ]
  · have hi' : i < k := by omega
    obtain ⟨d₁, d₂⟩ := h.done i hi'
    refine ⟨?_, ?_⟩
    · rw [VG.Proof.Scrypt.AArch64.BlockMix.slot_keep hp oO (by omega) (by omega) f₅, VG.Proof.Scrypt.AArch64.BlockMix.slot_keep hp oE (by omega) (by omega) f₂, d₁]
    · rw [VG.Proof.Scrypt.AArch64.BlockMix.slot_keep hp oO (by omega) (by omega) f₅, VG.Proof.Scrypt.AArch64.BlockMix.slot_keep hp oE (by omega) (by omega) f₂, d₂]

theorem others_pres : ∀ r ∈ VG.Proof.Scrypt.AArch64.BlockMix.others, r ∈ preserved ∧ r ≠ .x30 ∧ r ≠ .x19 := by decide

/-- Both halves of pair `k`. -/
theorem halves_ok {c : Prog isa} (hS : VG.Proof.Scrypt.AArch64.BlockMix.SalsaSpec c) {s₀ : State} (hp : VG.Proof.Scrypt.AArch64.BlockMix.Pre s₀) {k : Nat}
    (hk : k < VG.Proof.Scrypt.AArch64.BlockMix.rr s₀) {s : State} (h : VG.Proof.Scrypt.AArch64.BlockMix.Inv s₀ k s) {P : Prog isa} {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.Scrypt.AArch64.BlockMix.Mid s₀ k s' → WP isa P s' Q) :
    WP isa (.seq (.block (xor64 .x20 .x24 .x19)) <| .seq (salsaAt c .x20) <|
      .seq (.block (.addImm .x .x19 .x19 64 :: xor64 .x21 .x20 .x19)) <| .seq (salsaAt c .x21) P)
      s Q := by
  have lt := VG.Proof.Scrypt.AArch64.BlockMix.r_lt hp
  have hrd : s.rd = [VG.Proof.Scrypt.AArch64.BlockMix.bR s₀] := by rw [h.rd, hp.rd]
  have hwr : s.wr = [VG.Proof.Scrypt.AArch64.BlockMix.yR s₀, VG.Proof.Scrypt.AArch64.BlockMix.scR s₀] := by rw [h.wr, hp.wr]
  have oE : 64 * k + 64 ≤ 128 * VG.Proof.Scrypt.AArch64.BlockMix.rr s₀ := by omega
  have oO : 64 * (VG.Proof.Scrypt.AArch64.BlockMix.rr s₀ + k) + 64 ≤ 128 * VG.Proof.Scrypt.AArch64.BlockMix.rr s₀ := by omega
  refine WP.seq (VG.Proof.Scrypt.AArch64.BlockMix.half_ok hS hp (by decide) (by decide) (by decide) oE (ob := 128 * k) (by omega)
    hrd hwr h.x20 h.x24 h.x19 h.x22 (VG.Proof.Scrypt.AArch64.BlockMix.xP_disj hp hk) (VG.Proof.Scrypt.AArch64.BlockMix.xP_in hp hk hrd hwr)
    fun s₂ rd₂ wr₂ sp₂ cs₂ f₂ b₂ => ?_)
  refine WP.seq (wp_addImm (by decide) fun s₃ u₃ => ?_)
  have k3 : ∀ r, r ≠ .x19 → r ∈ preserved → r ≠ .x30 → s₃.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [u₃.other _ h1, cs₂ r h2 h3]
  have e3 : s₃.gpr .x19 = VG.Proof.Scrypt.AArch64.BlockMix.bP s₀ + BitVec.ofNat 64 (64 * (2 * k + 1)) := by
    rw [u₃.gpr, cs₂ _ (by decide) (by decide), h.x19, add_ofNat]; congr 2; omega
  have hrd₃ : s₃.rd = [VG.Proof.Scrypt.AArch64.BlockMix.bR s₀] := by rw [u₃.rd, rd₂, hrd]
  have hwr₃ : s₃.wr = [VG.Proof.Scrypt.AArch64.BlockMix.yR s₀, VG.Proof.Scrypt.AArch64.BlockMix.scR s₀] := by rw [u₃.wr, wr₂, hwr]
  have e20 : s₃.gpr .x20 = VG.Proof.Scrypt.AArch64.BlockMix.yE s₀ k := by rw [k3 _ (by decide) (by decide) (by decide), h.x20]
  refine VG.Proof.Scrypt.AArch64.BlockMix.half_ok hS hp (by decide) (by decide) (by decide) oO (ob := 64 * (2 * k + 1)) (by omega)
    hrd₃ hwr₃ (by rw [k3 _ (by decide) (by decide) (by decide), h.x21]) e20 e3
    (by rw [k3 _ (by decide) (by decide) (by decide), h.x22])
    (VG.Proof.Scrypt.AArch64.BlockMix.y_disj hp (by omega) oO oE (by omega) (by omega))
    (fun i hi => by rw [hrd₃, hwr₃, add_ofNat]; exact InRegions.of_mem (by simp) (VG.Proof.Scrypt.AArch64.BlockMix.in_y hp (by omega)))
    fun s₅ rd₅ wr₅ sp₅ cs₅ f₅ b₅ => ?_
  rw [u₃.mem] at f₅ b₅
  obtain ⟨F, S, D⟩ := VG.Proof.Scrypt.AArch64.BlockMix.mem_ok hp hk h f₂ b₂ f₅ b₅
  have k5 : ∀ r, r ≠ .x19 → r ∈ preserved → r ≠ .x30 → s₅.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [cs₅ r h2 h3, k3 r h1 h2 h3]
  exact hQ s₅ ⟨by rw [rd₅, hrd₃, hp.rd], by rw [wr₅, hwr₃, hp.wr],
    by rw [sp₅, u₃.sp, sp₂, h.sp],
    by rw [cs₅ _ (by decide) (by decide), e3],
    by rw [k5 _ (by decide) (by decide) (by decide), h.x20],
    by rw [k5 _ (by decide) (by decide) (by decide), h.x21],
    by rw [k5 _ (by decide) (by decide) (by decide), h.x22],
    by rw [k5 _ (by decide) (by decide) (by decide), h.x23],
    fun r hr => by
      rw [k5 r (VG.Proof.Scrypt.AArch64.BlockMix.others_pres r hr).2.2 (VG.Proof.Scrypt.AArch64.BlockMix.others_pres r hr).1 (VG.Proof.Scrypt.AArch64.BlockMix.others_pres r hr).2.1, h.keep r hr],
    F, S, D⟩

/-- The pointers move on. -/
theorem regs_ok {s₀ : State} (hp : VG.Proof.Scrypt.AArch64.BlockMix.Pre s₀) {k : Nat} (hk : k < VG.Proof.Scrypt.AArch64.BlockMix.rr s₀) {s : State}
    (h : VG.Proof.Scrypt.AArch64.BlockMix.Mid s₀ k s) :
    WP isa (.block [mov .x24 .x21, .addImm .x .x19 .x19 64, .addImm .x .x20 .x20 64,
      .addImm .x .x21 .x21 64, .subImm .x .x23 .x23 1]) s (VG.Proof.Scrypt.AArch64.BlockMix.Inv s₀ (k + 1)) := by
  have lt := VG.Proof.Scrypt.AArch64.BlockMix.r_lt hp
  refine wp_mov fun s₆ u₆ => wp_addImm (by decide) fun s₇ u₇ => wp_addImm (by decide) fun s₈ u₈ =>
    wp_addImm (by decide) fun s₉ u₉ => wp_subImm (by decide) fun s₁₀ u₁₀ => WP.block_nil ?_
  have m₁₀ : s₁₀.mem = s.mem := by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem]
  have g : ∀ r, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x23 → r ≠ .x24 → s₁₀.gpr r = s.gpr r :=
    fun r h19 h20 h21 h23 h24 => by
      rw [u₁₀.other _ h23, u₉.other _ h21, u₈.other _ h20, u₇.other _ h19, u₆.other _ h24]
  refine ⟨(by omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, h.rd]
  · rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, h.wr]
  · rw [u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, h.sp]
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr,
      u₆.other _ (by decide), h.x19, add_ofNat]
    congr 2; omega
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide),
      u₆.other _ (by decide), h.x20, add_ofNat]
    congr 2
  · rw [u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), h.x21, add_ofNat]
    congr 2
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), h.x22]
  · rw [u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), h.x23, sub_ofNat (by omega)]
    congr 1
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), u₆.gpr, h.x21]
    rfl
  · intro r hr
    have : r ≠ .x19 ∧ r ≠ .x20 ∧ r ≠ .x21 ∧ r ≠ .x23 ∧ r ≠ .x24 := by
      simp only [VG.Proof.Scrypt.AArch64.BlockMix.others, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
    rw [g r this.1 this.2.1 this.2.2.1 this.2.2.2.1 this.2.2.2.2, h.keep r hr]
  · rw [m₁₀]; exact h.frame
  · rw [m₁₀]; exact h.saved
  · rw [m₁₀]; exact h.done
  · rw [m₁₀]
    show bytesAt s.mem (VG.Proof.Scrypt.AArch64.BlockMix.yO s₀ k) 64 = _
    rw [(h.done k (by omega)).2]
    rfl

theorem body_ok {c : Prog isa} (hS : VG.Proof.Scrypt.AArch64.BlockMix.SalsaSpec c) {s₀ : State} (hp : VG.Proof.Scrypt.AArch64.BlockMix.Pre s₀) {k : Nat}
    (hk : k < VG.Proof.Scrypt.AArch64.BlockMix.rr s₀) {s : State} (h : VG.Proof.Scrypt.AArch64.BlockMix.Inv s₀ k s) : WP isa (bmBody c) s (VG.Proof.Scrypt.AArch64.BlockMix.Inv s₀ (k + 1)) :=
  VG.Proof.Scrypt.AArch64.BlockMix.halves_ok hS hp hk h fun _ hm => VG.Proof.Scrypt.AArch64.BlockMix.regs_ok hp hk hm

end VG.Proof.Scrypt.AArch64.BlockMix

/-!
# scryptBlockMix on AArch64: the whole function

The prologue saves our caller's `x19`–`x24` in `scratch` and sets up the
loop's registers; the loop runs the `r` pairs; the epilogue restores the
registers. Around all of it, a frame saves `x30`, which the calls replace.
-/

namespace VG.Proof.Scrypt.AArch64.BlockMix

open VG VG.AArch64 VG.Impl.Scrypt.AArch64
open VG.Spec.Scrypt (bytesAt blk blockMix)
open VG.Proof.Scrypt (yAt xBefore blockMix_eq flatMap_congr)
open VG.Proof.MdStream.AArch64 (Upd Mupd wp_mov wp_add wp_addImm wp_subImm wp_ldr wp_str
  eval_nonzero ofNat_beq_zero readW_writeW_save write_frame_bytes)
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt add_ofNat InRegions.of_mem frame_bytesAt bytesAt_add
  bytesAt_blocks bytesAt_congr)

/-! ## The prologue -/

/-- The memory after the prologue's stores. -/
abbrev saveMem (s₀ : State) : Mem := Spill.saveMem s₀.mem (VG.Proof.Scrypt.AArch64.BlockMix.sc s₀) s₀.gpr bmSaved

theorem saveMem_saved (s₀ : State) : VG.Proof.Scrypt.AArch64.BlockMix.Saved s₀ (VG.Proof.Scrypt.AArch64.BlockMix.saveMem s₀) := Spill.saveMem_saved (by decide) _ _ _

theorem saveMem_frame (s₀ : State) : Frame [VG.Proof.Scrypt.AArch64.BlockMix.scR s₀] s₀.mem (VG.Proof.Scrypt.AArch64.BlockMix.saveMem s₀) :=
  Spill.saveMem_frame_base (by decide) (by decide) _ _ _

theorem prologue_eq : bmPrologue = Spill.saveCode .x4 bmSaved ++
    ([mov .x23 .x1, mov .x19 .x0, mov .x20 .x2, mov .x22 .x4,
     .lsl .x .x9 .x1 6, .add .x .x21 .x2 .x9,
     .lsl .x .x9 .x1 7, .add .x .x24 .x0 .x9, .subImm .x .x24 .x24 64] : List Instr) := rfl

theorem save_ok {s₀ : State} (hp : VG.Proof.Scrypt.AArch64.BlockMix.Pre s₀) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s₁, s₁.gpr = s₀.gpr → s₁.rd = s₀.rd → s₁.wr = s₀.wr → s₁.sp = s₀.sp →
      s₁.mem = VG.Proof.Scrypt.AArch64.BlockMix.saveMem s₀ → WP isa (.block rest) s₁ Q) :
    WP isa (.block (Spill.saveCode .x4 bmSaved ++ rest)) s₀ Q :=
  Spill.save_ok (by decide) (fun p hp' => by
    rw [hp.wr]; exact InRegions.of_mem (by simp) (VG.Proof.Scrypt.AArch64.BlockMix.in_s s₀ (by revert p; decide)))
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
theorem setup_ok {s₀ : State} (hp : VG.Proof.Scrypt.AArch64.BlockMix.Pre s₀) {s₁ : State} (g : s₁.gpr = s₀.gpr)
    (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr) (hsp : s₁.sp = s₀.sp) (hm : s₁.mem = VG.Proof.Scrypt.AArch64.BlockMix.saveMem s₀) :
    WP isa (.block [mov .x23 .x1, mov .x19 .x0, mov .x20 .x2, mov .x22 .x4,
     .lsl .x .x9 .x1 6, .add .x .x21 .x2 .x9,
     .lsl .x .x9 .x1 7, .add .x .x24 .x0 .x9, .subImm .x .x24 .x24 64]) s₁ (VG.Proof.Scrypt.AArch64.BlockMix.Inv s₀ 0) := by
  have lt : 128 * (s₀.gpr .x1).toNat < 2 ^ 64 := VG.Proof.Scrypt.AArch64.BlockMix.r_lt hp
  have pos := hp.pos
  refine wp_mov fun a ua => wp_mov fun b ub => wp_mov fun c uc => wp_mov fun d ud =>
    VG.Proof.Scrypt.AArch64.BlockMix.wp_lsl (by decide) fun e ue => wp_add fun f uf => VG.Proof.Scrypt.AArch64.BlockMix.wp_lsl (by decide) fun g' ug =>
    wp_add fun h uh => wp_subImm (by decide) fun i ui => WP.block_nil ?_
  have x1 : d.gpr .x1 = s₀.gpr .x1 := by
    rw [ud.other _ (by decide), uc.other _ (by decide), ub.other _ (by decide),
      ua.other _ (by decide), g]
  have e9 : e.gpr .x9 = BitVec.ofNat 64 (64 * VG.Proof.Scrypt.AArch64.BlockMix.rr s₀) := by
    rw [ue.gpr, x1, VG.Proof.Scrypt.AArch64.BlockMix.shl_eq (by simp; omega), Nat.mul_comm]
  have g9 : g'.gpr .x9 = BitVec.ofNat 64 (128 * VG.Proof.Scrypt.AArch64.BlockMix.rr s₀) := by
    rw [ug.gpr, uf.other _ (by decide), ue.other _ (by decide), x1, VG.Proof.Scrypt.AArch64.BlockMix.shl_eq (by simp; omega),
      Nat.mul_comm]
  have hm' : i.mem = VG.Proof.Scrypt.AArch64.BlockMix.saveMem s₀ := by
    rw [ui.mem, uh.mem, ug.mem, uf.mem, ue.mem, ud.mem, uc.mem, ub.mem, ua.mem, hm]
  have k : ∀ r, r ≠ .x9 → r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x22 → r ≠ .x23 → r ≠ .x24 →
      i.gpr r = s₀.gpr r := fun r h9 h19 h20 h21 h22 h23 h24 => by
    rw [ui.other _ h24, uh.other _ h24, ug.other _ h9, uf.other _ h21, ue.other _ h9,
      ud.other _ h22, uc.other _ h20, ub.other _ h19, ua.other _ h23, g]
  refine ⟨Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => absurd hi (by omega), ?_⟩
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
  · rw [ui.other _ (by decide), uh.other _ (by decide), ug.other _ (by decide), uf.gpr, e9,
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
  · rw [ui.gpr, uh.gpr, g9, ug.other _ (by decide), uf.other _ (by decide),
      ue.other _ (by decide), ud.other _ (by decide), uc.other _ (by decide),
      ub.other _ (by decide), ua.other _ (by decide), g, VG.Proof.Scrypt.AArch64.BlockMix.add_sub64 _ (by omega)]
    rfl
  · intro r hr
    have : r ≠ .x9 ∧ r ≠ .x19 ∧ r ≠ .x20 ∧ r ≠ .x21 ∧ r ≠ .x22 ∧ r ≠ .x23 ∧ r ≠ .x24 := by
      simp only [VG.Proof.Scrypt.AArch64.BlockMix.others, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
    obtain ⟨h9, h19, h20, h21, h22, h23, h24⟩ := this
    exact k r h9 h19 h20 h21 h22 h23 h24
  · rw [hm']; exact (VG.Proof.Scrypt.AArch64.BlockMix.saveMem_frame s₀).mono (by simp)
  · rw [hm']; exact VG.Proof.Scrypt.AArch64.BlockMix.saveMem_saved s₀
  · rw [hm']
    show bytesAt (VG.Proof.Scrypt.AArch64.BlockMix.saveMem s₀) (VG.Proof.Scrypt.AArch64.BlockMix.bP s₀ + BitVec.ofNat 64 (128 * VG.Proof.Scrypt.AArch64.BlockMix.rr s₀ - 64)) 64 =
      blk (VG.Proof.Scrypt.AArch64.BlockMix.B s₀) (2 * VG.Proof.Scrypt.AArch64.BlockMix.rr s₀ - 1)
    rw [VG.Proof.Scrypt.AArch64.BlockMix.blk_B s₀ (by omega), show 64 * (2 * VG.Proof.Scrypt.AArch64.BlockMix.rr s₀ - 1) = 128 * VG.Proof.Scrypt.AArch64.BlockMix.rr s₀ - 64 by omega]
    refine frame_bytesAt (VG.Proof.Scrypt.AArch64.BlockMix.saveMem_frame s₀) (fun r hr => ?_) (by omega)
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.b_s.sub_left (VG.Proof.Scrypt.AArch64.BlockMix.b_sub hp (by omega))

/-! ## The loop -/

theorem loop_ok {c : Prog isa} (hS : VG.Proof.Scrypt.AArch64.BlockMix.SalsaSpec c) {s₀ : State} (hp : VG.Proof.Scrypt.AArch64.BlockMix.Pre s₀) {s : State}
    (h : VG.Proof.Scrypt.AArch64.BlockMix.Inv s₀ 0 s) : WP isa (.loop (bmBody c) (.nonzero .x .x23)) s (VG.Proof.Scrypt.AArch64.BlockMix.Inv s₀ (VG.Proof.Scrypt.AArch64.BlockMix.rr s₀)) := by
  have lt := VG.Proof.Scrypt.AArch64.BlockMix.r_lt hp
  refine WP.loop (M := isa) (fun n s => ∃ k, n = VG.Proof.Scrypt.AArch64.BlockMix.rr s₀ - k ∧ k < VG.Proof.Scrypt.AArch64.BlockMix.rr s₀ ∧ VG.Proof.Scrypt.AArch64.BlockMix.Inv s₀ k s) ?_ (VG.Proof.Scrypt.AArch64.BlockMix.rr s₀) s
    ⟨0, rfl, hp.pos, h⟩
  rintro n s ⟨k, rfl, hk, hi⟩
  refine WP.mono (VG.Proof.Scrypt.AArch64.BlockMix.body_ok hS hp hk hi) fun s' hi' => ?_
  have hz : isa.eval (.nonzero .x .x23) s' = some (decide (VG.Proof.Scrypt.AArch64.BlockMix.rr s₀ - (k + 1) ≠ 0)) := by
    show VG.AArch64.eval (.nonzero .x .x23) s' = _
    rw [eval_nonzero, hi'.x23, bne, ofNat_beq_zero (by omega)]
    simp
  by_cases hl : VG.Proof.Scrypt.AArch64.BlockMix.rr s₀ - (k + 1) = 0
  · refine .inl ⟨by rw [hz]; simp [hl], ?_⟩
    rwa [show k + 1 = VG.Proof.Scrypt.AArch64.BlockMix.rr s₀ by omega] at hi'
  · exact .inr ⟨by rw [hz]; simp [hl], VG.Proof.Scrypt.AArch64.BlockMix.rr s₀ - (k + 1), by omega, k + 1, rfl, by omega, hi'⟩

/-! ## The epilogue -/

theorem preserved_cases : ∀ r ∈ preserved, r ≠ .x30 → r ∈ bmSaved.map Prod.fst ∨ r ∈ VG.Proof.Scrypt.AArch64.BlockMix.others := by
  decide

theorem restore_ok {s₀ : State} (hp : VG.Proof.Scrypt.AArch64.BlockMix.Pre s₀) {s : State} (h : VG.Proof.Scrypt.AArch64.BlockMix.Inv s₀ (VG.Proof.Scrypt.AArch64.BlockMix.rr s₀) s) :
    WP isa (.block bmEpilogue) s fun s' => s'.mem = s.mem ∧ s'.sp = s.sp ∧
      (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s₀.gpr r) :=
  WP.mono (Spill.restore_wp (b := .x22) h.x22 (by decide) (by decide) (fun p hp' => by
      rw [h.rd, h.wr, hp.rd, hp.wr]; exact InRegions.of_mem (by simp) (VG.Proof.Scrypt.AArch64.BlockMix.in_s s₀ (by revert p; decide)))
    h.saved) fun s' h' => ⟨h'.mem, h'.sp, fun r hr h30 =>
      h'.gpr_of ((VG.Proof.Scrypt.AArch64.BlockMix.preserved_cases r hr h30).imp id (h.keep r))⟩

/-! ## The body of the frame -/

/-- The output, from the blocks the loop wrote. -/
theorem post_of {s₀ : State} {m : Mem}
    (h : ∀ i < VG.Proof.Scrypt.AArch64.BlockMix.rr s₀, bytesAt m (VG.Proof.Scrypt.AArch64.BlockMix.yE s₀ i) 64 = yAt (VG.Proof.Scrypt.AArch64.BlockMix.B s₀) (VG.Proof.Scrypt.AArch64.BlockMix.rr s₀) (2 * i) ∧
      bytesAt m (VG.Proof.Scrypt.AArch64.BlockMix.yO s₀ i) 64 = yAt (VG.Proof.Scrypt.AArch64.BlockMix.B s₀) (VG.Proof.Scrypt.AArch64.BlockMix.rr s₀) (2 * i + 1)) :
    bytesAt m (VG.Proof.Scrypt.AArch64.BlockMix.yP s₀) (128 * VG.Proof.Scrypt.AArch64.BlockMix.rr s₀) = blockMix (VG.Proof.Scrypt.AArch64.BlockMix.rr s₀) (VG.Proof.Scrypt.AArch64.BlockMix.B s₀) := by
  rw [blockMix_eq, show 128 * VG.Proof.Scrypt.AArch64.BlockMix.rr s₀ = 64 * VG.Proof.Scrypt.AArch64.BlockMix.rr s₀ + 64 * VG.Proof.Scrypt.AArch64.BlockMix.rr s₀ by omega, bytesAt_add,
    bytesAt_blocks, bytesAt_blocks]
  congr 1
  · refine flatMap_congr fun i hi => ?_
    rw [List.mem_range] at hi
    exact (h i hi).1
  · refine flatMap_congr fun i hi => ?_
    rw [List.mem_range] at hi
    rw [add_ofNat, ← Nat.mul_add]
    exact (h i hi).2

theorem correctMain {c : Prog isa} (hS : VG.Proof.Scrypt.AArch64.BlockMix.SalsaSpec c) {s₀ : State} (hp : VG.Proof.Scrypt.AArch64.BlockMix.Pre s₀) :
    WP isa (blockMixMain c) s₀ fun s' => (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s₀.gpr r) ∧
      s'.sp = s₀.sp ∧ bytesAt s'.mem (VG.Proof.Scrypt.AArch64.BlockMix.yP s₀) (128 * VG.Proof.Scrypt.AArch64.BlockMix.rr s₀) = blockMix (VG.Proof.Scrypt.AArch64.BlockMix.rr s₀) (VG.Proof.Scrypt.AArch64.BlockMix.B s₀) := by
  unfold blockMixMain
  refine WP.seq ?_
  rw [VG.Proof.Scrypt.AArch64.BlockMix.prologue_eq]
  refine VG.Proof.Scrypt.AArch64.BlockMix.save_ok hp fun s₁ g hrd hwr hsp hm => ?_
  refine WP.mono (VG.Proof.Scrypt.AArch64.BlockMix.setup_ok hp g hrd hwr hsp hm) fun s₂ h₂ => ?_
  refine WP.seq (WP.mono (VG.Proof.Scrypt.AArch64.BlockMix.loop_ok hS hp h₂) fun s₃ h₃ => ?_)
  refine WP.mono (VG.Proof.Scrypt.AArch64.BlockMix.restore_ok hp h₃) fun s' ⟨hm', hsp', hg'⟩ => ⟨hg', hsp'.trans h₃.sp, ?_⟩
  rw [hm']
  exact VG.Proof.Scrypt.AArch64.BlockMix.post_of fun i hi => h₃.done i hi

/-! ## The whole function -/

/-- The frame's 16 bytes are free. -/
structure Stack (s₀ : State) : Prop where
  sp16 : 16 ≤ s₀.sp.toNat
  b : Region.Disjoint ⟨s₀.sp - 16, 16⟩ (VG.Proof.Scrypt.AArch64.BlockMix.bR s₀)
  y : Region.Disjoint ⟨s₀.sp - 16, 16⟩ (VG.Proof.Scrypt.AArch64.BlockMix.yR s₀)
  s : Region.Disjoint ⟨s₀.sp - 16, 16⟩ (VG.Proof.Scrypt.AArch64.BlockMix.scR s₀)

theorem pre_of {s₀ : State} (h : Proof.Scrypt.blockMixAArch64.pre s₀) : VG.Proof.Scrypt.AArch64.BlockMix.Pre s₀ ∧ VG.Proof.Scrypt.AArch64.BlockMix.Stack s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  rw [h13] at h2 h3 h4 h8 h11
  exact ⟨⟨h1, h2, h3, h4, h5, h10, h11, h12, h13, h14⟩, ⟨h6, h7, h8, h9⟩⟩

/-- The state the body starts in, inside the frame. -/
abbrev inner (s₀ : State) : State :=
  { s₀ with sp := s₀.sp - 16, mem := s₀.mem.write (s₀.sp - 16) 8 (s₀.gpr .x30) }

theorem correct {c : Prog isa} (hS : VG.Proof.Scrypt.AArch64.BlockMix.SalsaSpec c)
    (hd : 16 * (blockMixMain c).aarch64Depth + 16 < 2 ^ 64) {s₀ : State} (hp : VG.Proof.Scrypt.AArch64.BlockMix.Pre s₀) (hs : VG.Proof.Scrypt.AArch64.BlockMix.Stack s₀) :
    WP isa (blockMixWith c) s₀ fun s' =>
      GprAbi s₀ s' ∧ Proof.Scrypt.blockMixAArch64.post s₀ s' := by
  have hpi : VG.Proof.Scrypt.AArch64.BlockMix.Pre (VG.Proof.Scrypt.AArch64.BlockMix.inner s₀) := ⟨hp.rd, hp.wr, hp.y_s, hp.b_y, hp.b_s, hp.b_nw, hp.y_nw, hp.s_nw,
    hp.x3, hp.pos⟩
  refine WP.frameReg hs.sp16 (fun R hR => ?_) (WP.mono (VG.Proof.Scrypt.AArch64.BlockMix.correctMain hS hpi) fun s' ⟨hk, hsp, hpost⟩ => ?_) hd
  · rw [hp.wr] at hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · exact hs.y
    · exact hs.s
  · refine ⟨⟨fun r hr => ?_, rfl⟩, ?_⟩
    · by_cases h30 : r = .x30
      · subst h30; simp [State.write]
      · simp only [State.write, h30, ite_false]
        exact hk r hr h30
    · have e : VG.Proof.Scrypt.AArch64.BlockMix.B (VG.Proof.Scrypt.AArch64.BlockMix.inner s₀) = bytesAt s₀.mem (VG.Proof.Scrypt.AArch64.BlockMix.bP s₀) (128 * VG.Proof.Scrypt.AArch64.BlockMix.rr s₀) :=
        bytesAt_congr fun i hi => by
          have hi' : i < 128 * VG.Proof.Scrypt.AArch64.BlockMix.rr s₀ := hi
          exact write_frame_bytes (R := VG.Proof.Scrypt.AArch64.BlockMix.bR s₀) hs.b (by have := VG.Proof.Scrypt.AArch64.BlockMix.r_lt hp; simp only; omega)
            (by simp only; omega)
      show bytesAt s'.mem (VG.Proof.Scrypt.AArch64.BlockMix.yP s₀) (128 * VG.Proof.Scrypt.AArch64.BlockMix.rr s₀) = blockMix (VG.Proof.Scrypt.AArch64.BlockMix.rr s₀) (bytesAt s₀.mem (VG.Proof.Scrypt.AArch64.BlockMix.bP s₀) (128 * VG.Proof.Scrypt.AArch64.BlockMix.rr s₀))
      rw [← e]
      exact hpost

end VG.Proof.Scrypt.AArch64.BlockMix

/-!
# scryptBlockMix on AArch64: verified

`SalsaSpec` of the verified Salsa20/8 Core, from its `Verified` proof by
`WP.call`; then the `Verified` proof of `vg_scrypt_blockmix`. Only the
pointers and `r` are public, and the taint analysis checks that nothing else
reaches an address or a branch.
-/

namespace VG.Proof.Scrypt.AArch64.BlockMix

open VG VG.AArch64

theorem salsa_noFrames : Impl.Scrypt.AArch64.salsa.noFrames = true := by decide +kernel

theorem salsaSpec : VG.Proof.Scrypt.AArch64.BlockMix.SalsaSpec Impl.Scrypt.AArch64.salsa := by
  intro s d sc hd hsc hds hind hins Q hQ
  have c0 : s.callEntry.gpr .x0 = d := (State.callEntry_gpr _ (by decide)).trans hd
  have c1 : s.callEntry.gpr .x1 = sc := (State.callEntry_gpr _ (by decide)).trans hsc
  have hw : Covers [⟨d, 64⟩, ⟨sc, 64⟩] s.wr := Covers.pair (Covers.one hind) (Covers.one hins)
  refine WP.call (k := Proof.Scrypt.salsaAArch64) Proof.Scrypt.AArch64.salsa_correct
    (rd := []) (wr := [⟨d, 64⟩, ⟨sc, 64⟩]) ?_ ?_ hw ?_ VG.Proof.Scrypt.AArch64.BlockMix.salsa_noFrames
  · simp only [Proof.Scrypt.salsaAArch64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, c0, c1]
    exact ⟨trivial, trivial, hds⟩
  · intro a n h
    obtain ⟨R, hR, hc⟩ := hw a n (by simpa using h)
    exact ⟨R, List.mem_append_right _ hR, hc⟩
  · intro s' hrd hwr hsp hf hcs _ hpost
    simp only [Proof.Scrypt.salsaAArch64, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c0] at hpost
    exact hQ s' hrd hwr hsp hcs hf hpost

theorem main_fdepth : 16 * (Impl.Scrypt.AArch64.blockMixMain Impl.Scrypt.AArch64.salsa).aarch64Depth + 16 < 2 ^ 64 := by
  decide +kernel

theorem agree₀ {s₁ s₂ : State} (hpub : Proof.Scrypt.blockMixAArch64.pub s₁ s₂) :
    VG.AArch64.Taint.Agree (VG.AArch64.Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- A state satisfying the precondition (with no data). -/
def bmSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 1 | .x2 => 0x2000 | .x3 => 1 | .x4 => 0x3000 | _ => 0
  sp := 0x5000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 128⟩, ⟨0x3000, 128⟩]

theorem blockMix_correct (s : State) (hs : Proof.Scrypt.blockMixAArch64.pre s) :
    ∃ t s', Exec isa Impl.Scrypt.AArch64.blockMix s t s' ∧ abiPreserved s s' ∧
      Proof.Scrypt.blockMixAArch64.post s s' := by
  obtain ⟨t, s', he, h⟩ :=
    BlockMix.correct VG.Proof.Scrypt.AArch64.BlockMix.salsaSpec VG.Proof.Scrypt.AArch64.BlockMix.main_fdepth (VG.Proof.Scrypt.AArch64.BlockMix.pre_of hs).1 (VG.Proof.Scrypt.AArch64.BlockMix.pre_of hs).2
  exact ⟨t, s', he, ⟨h.1.1, h.1.2, Exec.preservedV he (by lit_decide)⟩, h.2⟩

theorem blockMix_ct : ConstantTime isa Proof.Scrypt.blockMixAArch64.pre
    Proof.Scrypt.blockMixAArch64.pub Impl.Scrypt.AArch64.blockMix := by
  exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    (fun _ _ _ _ hp => VG.Proof.Scrypt.AArch64.BlockMix.agree₀ hp) (by taint_decide)

theorem blockMix_verified :
    Verified AArch64.target Impl.Scrypt.AArch64.blockMix (Spec.Scrypt.blockMixContract AArch64.abi
      16) :=
  Verified.of_correct VG.Proof.Scrypt.AArch64.BlockMix.blockMix_correct VG.Proof.Scrypt.AArch64.BlockMix.blockMix_ct
    { pre := by
        sig_implies_pre [Spec.Scrypt.blockMixContract, Spec.Scrypt.blockMixSig,
          Proof.Scrypt.blockMixAArch64, AArch64.abi, AArch64.argRegs]
      post := by
        sig_implies_post [Spec.Scrypt.blockMixContract, Spec.Scrypt.blockMixSig,
          Proof.Scrypt.blockMixAArch64, AArch64.abi, AArch64.argRegs]
      pub := by
        sig_implies_pub [Spec.Scrypt.blockMixContract, Spec.Scrypt.blockMixSig,
          Proof.Scrypt.blockMixAArch64, AArch64.abi, AArch64.argRegs]
      sat := by
        sig_implies_sat [Spec.Scrypt.blockMixContract, Spec.Scrypt.blockMixSig,
          Proof.Scrypt.blockMixAArch64, AArch64.abi, AArch64.argRegs,
          Proof.Scrypt.AArch64.BlockMix.bmSat]
          [Proof.Scrypt.AArch64.BlockMix.bmSat] using Proof.Scrypt.AArch64.BlockMix.bmSat }

end VG.Proof.Scrypt.AArch64.BlockMix

end
