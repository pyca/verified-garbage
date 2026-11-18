module

public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Scrypt.Contract
meta import VerifiedGarbage.Spec.Scrypt.Contract
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
public import VerifiedGarbage.Proof.Scrypt.X86.Common
import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Mmx
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86.Sse
meta import VerifiedGarbage.Proof.Framework.X86.SseDword
meta import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
meta import VerifiedGarbage.Proof.Scrypt.X86.Common
meta import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Framework.X86.Spill
meta import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Scrypt.Memory
meta import VerifiedGarbage.Proof.Scrypt.Memory
public import VerifiedGarbage.Proof.Scrypt.BlockMix
public import VerifiedGarbage.Impl.Scrypt.X86.BlockMix
import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Scrypt.BlockMix
meta import VerifiedGarbage.Impl.Scrypt.X86.BlockMix
meta import VerifiedGarbage.Proof.Framework.WriteBytes

/-! ### `Scrypt.X86.BlockMix`, which only this module used -/

section

/-!
# scryptBlockMix on x86 (32-bit): the loop

As on 32-bit ARM (`Proof/Scrypt/Arm/BlockMixVerified.lean`), the calls of
`vg_salsa20_8` are used through `SalsaSpec`, what its proof says about a call in
a frame of its arguments; the proof of this file holds for any code meeting it.
Pointers are read from the arguments on the stack, which nothing writes; the
calls use the 12 bytes below `esp` (`stkR`), which the memory frames include, as
on x86-64 (`Proof/Scrypt/X86_64/BlockMixCT.lean`).
-/

@[expose] public section

namespace VG.Proof.Scrypt.X86.BlockMix

open VG VG.X86 VG.Impl.Scrypt.X86
open VG.Spec.Scrypt (bytesAt blk salsa)
open VG.Spec.Pbkdf2 (xorBytes)
open VG.Proof.Scrypt (yAt xBefore yAt_eq xBefore_succ)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame)
open VG.Proof.Sha256.X86.Stream (Upd wp_mov wp_movm wp_add wp_addi wp_cmp addr_toNat)
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt add_ofNat contains_off sub_off disj_off
  InRegions.of_mem frame_bytesAt bytesAt_writeBytes_self xorBytes_length bytesAt_length blk_bytesAt)

/-! ## What a call of `vg_salsa20_8` does -/

/-- A call of `c`, in a frame of its arguments pushed from `eax` and `dR`,
replaces the 64 bytes at `dR` by their Salsa20/8 Core, with the 64 bytes at
`eax` as working space, using the 12 bytes below `esp`. -/
def SalsaSpec (c : Prog isa) : Prop :=
  ∀ (s : State) (dR : Reg) (d sc : BitVec 32), dR ≠ .esp → s.gpr dR = d → s.gpr .eax = sc →
    d.toNat + 64 ≤ 2 ^ 32 → sc.toNat + 64 ≤ 2 ^ 32 →
    Region.Disjoint ⟨d.setWidth 64, 64⟩ ⟨sc.setWidth 64, 64⟩ → 12 ≤ (s.gpr .esp).toNat →
    (below (s.gpr .esp) 12).Disjoint ⟨d.setWidth 64, 64⟩ →
    (below (s.gpr .esp) 12).Disjoint ⟨sc.setWidth 64, 64⟩ →
    InRegions s.wr (d.setWidth 64) 64 → InRegions s.wr (sc.setWidth 64) 64 →
    ∀ Q : State → Prop, (∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
        Frame [⟨d.setWidth 64, 64⟩, ⟨sc.setWidth 64, 64⟩, below (s.gpr .esp) 12] s.mem s'.mem →
        bytesAt s'.mem (d.setWidth 64) 64 = salsa (bytesAt s.mem (d.setWidth 64) 64) → Q s') →
    WP isa (.frame (.push [.eax, dR]) (.call "vg_salsa20_8" c) (.pop .eax 2)) s Q

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev esp₀ : BitVec 32 := s₀.gpr .esp
abbrev bP : BitVec 32 := arg s₀ 0
abbrev rr : Nat := (arg s₀ 1).toNat
abbrev yP : BitVec 32 := arg s₀ 2
abbrev sc : BitVec 32 := arg s₀ 4
abbrev bA : Addr := (bP s₀).setWidth 64
abbrev yA : Addr := (yP s₀).setWidth 64
abbrev scA : Addr := (sc s₀).setWidth 64
abbrev bR : Region := ⟨bA s₀, rr s₀ * 128⟩
abbrev yR : Region := ⟨yA s₀, rr s₀ * 128⟩
abbrev scR : Region := ⟨scA s₀, 128⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 20⟩
abbrev retR : Region := ⟨(esp₀ s₀).setWidth 64, 4⟩
/-- The stack the calls use. -/
abbrev stkR : Region := below (esp₀ s₀) 12
/-- The input. -/
abbrev B : List Byte := bytesAt s₀.mem (bA s₀) (128 * rr s₀)

/-- `Y[2i]` goes to `y + 64 i`. -/
abbrev yE (i : Nat) : Addr := yA s₀ + BitVec.ofNat 64 (64 * i)
/-- `Y[2i + 1]` goes to `y + 64 (r + i)`. -/
abbrev yO (i : Nat) : Addr := yA s₀ + BitVec.ofNat 64 (64 * (rr s₀ + i))
/-- Where `X` is before the pair `(2k, 2k + 1)`. -/
def xP : Nat → Addr
  | 0 => bA s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64)
  | k + 1 => yO s₀ k
/-- `xP`, as the 32-bit pointer in `ebp`. -/
def xP32 : Nat → BitVec 32
  | 0 => bP s₀ + BitVec.ofNat 32 (128 * rr s₀ - 64)
  | k + 1 => yP s₀ + BitVec.ofNat 32 (64 * (rr s₀ + k))

/-- Our caller's `ebx`, `esi`, `edi` and `ebp` are saved in the scratch space. -/
abbrev Saved (m : Mem) : Prop := Spill.Saved m (scA s₀ + BitVec.ofNat 64 ·) s₀.gpr bmSaved

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [bR s₀, argR s₀]
  wr : s₀.wr = [yR s₀, scR s₀]
  y_s : (yR s₀).Disjoint (scR s₀)
  b_y : (bR s₀).Disjoint (yR s₀)
  b_s : (bR s₀).Disjoint (scR s₀)
  a_y : (argR s₀).Disjoint (yR s₀)
  a_s : (argR s₀).Disjoint (scR s₀)
  ret_y : (retR s₀).Disjoint (yR s₀)
  ret_s : (retR s₀).Disjoint (scR s₀)
  stk_b : (stkR s₀).Disjoint (bR s₀)
  stk_y : (stkR s₀).Disjoint (yR s₀)
  stk_s : (stkR s₀).Disjoint (scR s₀)
  b_nw : (bP s₀).toNat + rr s₀ * 128 ≤ 2 ^ 32
  y_nw : (yP s₀).toNat + rr s₀ * 128 ≤ 2 ^ 32
  s_nw : (sc s₀).toNat + 128 ≤ 2 ^ 32
  sp_lo : 12 ≤ (esp₀ s₀).toNat
  sp_fit : (esp₀ s₀).toNat + 24 ≤ 2 ^ 32
  r3 : arg s₀ 3 = arg s₀ 1
  pos : 0 < rr s₀

/-- The 12 bytes of stack below `E`, as the contracts write them. -/
theorem stk_eq {E : BitVec 32} (h : 12 ≤ E.toNat) : below E 12 = ⟨E.setWidth 64 - 12, 12⟩ := by
  simp only [below]; rw [Taint.sub_setWidth h]; rfl

theorem pre_of {s₀ : State} (h : Proof.Scrypt.blockMixX86.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩ := h
  obtain e := stk_eq h16
  simp only [h18] at h2 h3 h4 h6 h8 h11 h14
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, by rw [stkR, e]; exact h10, by rw [stkR, e]; exact h11,
    by rw [stkR, e]; exact h12, h13, h14, h15, h16, h17, h18, h19⟩

section
variable {s₀ : State} (hp : Pre s₀)
include hp

/-- `y` is not the whole address space, since `scratch` is not in it. -/
theorem r_lt : 128 * rr s₀ < 2 ^ 32 := by
  by_contra hc
  obtain hy : yA s₀ = 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [addr_toNat]; show _ = 0; have := hp.y_nw; omega_arith
  obtain hs : (scA s₀).toNat < 2 ^ 32 := by rw [addr_toNat]; exact (sc s₀).isLt
  refine hp.y_s (scA s₀) ?_ ?_
  · show (scA s₀ - yA s₀).toNat + 1 ≤ rr s₀ * 128
    rw [hy, show (0 : Addr) = 0#64 from rfl, BitVec.sub_zero]; omega_arith
  · show (scA s₀ - scA s₀).toNat + 1 ≤ 128
    rw [BitVec.sub_self, BitVec.toNat_zero]; omega_arith

theorem in_y {o n : Nat} (h : o + n ≤ 128 * rr s₀) :
    (yR s₀).Contains (yA s₀ + BitVec.ofNat 64 o) n :=
  contains_off (by omega_arith) (by have := r_lt hp; omega_arith)

theorem in_b {o n : Nat} (h : o + n ≤ 128 * rr s₀) :
    (bR s₀).Contains (bA s₀ + BitVec.ofNat 64 o) n :=
  contains_off (by omega_arith) (by have := r_lt hp; omega_arith)

/-- Two parts of `y`. -/
theorem y_disj {o₁ n₁ o₂ n₂ : Nat} (h : o₁ + n₁ ≤ o₂ ∨ o₂ + n₂ ≤ o₁) (h₁ : o₁ + n₁ ≤ 128 * rr s₀)
    (h₂ : o₂ + n₂ ≤ 128 * rr s₀) :
    Region.Disjoint ⟨yA s₀ + BitVec.ofNat 64 o₁, n₁⟩ ⟨yA s₀ + BitVec.ofNat 64 o₂, n₂⟩ :=
  have := r_lt hp
  disj_off _ h (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)

theorem y_sub {o n : Nat} (h : o + n ≤ 128 * rr s₀) : Region.Sub ⟨yA s₀ + BitVec.ofNat 64 o, n⟩ (yR s₀) :=
  sub_off (by omega_arith) (by have := r_lt hp; omega_arith)

theorem b_sub {o n : Nat} (h : o + n ≤ 128 * rr s₀) : Region.Sub ⟨bA s₀ + BitVec.ofNat 64 o, n⟩ (bR s₀) :=
  sub_off (by omega_arith) (by have := r_lt hp; omega_arith)

/-- A part of `y` and a part of `b`. -/
theorem yb_disj {o₁ n₁ o₂ n₂ : Nat} (h₁ : o₁ + n₁ ≤ 128 * rr s₀) (h₂ : o₂ + n₂ ≤ 128 * rr s₀) :
    Region.Disjoint ⟨yA s₀ + BitVec.ofNat 64 o₁, n₁⟩ ⟨bA s₀ + BitVec.ofNat 64 o₂, n₂⟩ :=
  (hp.b_y.symm.sub_left (y_sub hp h₁)).sub_right (b_sub hp h₂)

/-- A pointer into `y`, as an address. -/
theorem y_addr {o : Nat} (h : o < 128 * rr s₀) :
    (yP s₀ + BitVec.ofNat 32 o).setWidth 64 = yA s₀ + BitVec.ofNat 64 o :=
  addr_add (by have := hp.y_nw; omega_arith)

theorem b_addr {o : Nat} (h : o < 128 * rr s₀) :
    (bP s₀ + BitVec.ofNat 32 o).setWidth 64 = bA s₀ + BitVec.ofNat 64 o :=
  addr_add (by have := hp.b_nw; omega_arith)

theorem y_fit {o : Nat} (h : o + 64 ≤ 128 * rr s₀) : (yP s₀ + BitVec.ofNat 32 o).toNat + 64 ≤ 2 ^ 32 := by
  have := hp.y_nw
  rw [toNat_add32 (by omega_arith)]; omega_arith

theorem b_fit {o : Nat} (h : o + 64 ≤ 128 * rr s₀) : (bP s₀ + BitVec.ofNat 32 o).toNat + 64 ≤ 2 ^ 32 := by
  have := hp.b_nw
  rw [toNat_add32 (by omega_arith)]; omega_arith

/-- The argument words are in the arguments' region. -/
theorem arg_sub {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 24) :
    Region.Sub ⟨addr (esp₀ s₀) d, 4⟩ (argR s₀) := by
  have := hp.sp_fit
  intro a ha
  simp only [Region.Contains, argAddr] at ha ⊢
  rw [addr_eq (by omega_arith)] at ha
  rw [show (esp₀ s₀ + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 = addr (esp₀ s₀) 4 from rfl,
    addr_eq (by omega_arith)]
  generalize (esp₀ s₀).setWidth 64 = b at *
  bv_omega

theorem arg_in {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 24) :
    InRegions (s₀.rd ++ s₀.wr) (addr (esp₀ s₀) d) 4 := by
  have hs := hp.sp_fit
  refine ⟨argR s₀, by simp [hp.rd], ?_⟩
  show (addr (esp₀ s₀) d - addr (esp₀ s₀) 4).toNat + 4 ≤ 20
  rw [addr_eq (by omega_arith), addr_eq (by omega_arith),
    show (esp₀ s₀).setWidth 64 + BitVec.ofNat 64 d - ((esp₀ s₀).setWidth 64 + BitVec.ofNat 64 4) =
      BitVec.ofNat 64 (d - 4) by rw [show d = (d - 4) + 4 by omega_arith, BitVec.ofNat_add]; bv_omega,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  omega_arith

theorem stk_arg : (stkR s₀).Disjoint (argR s₀) := by
  have := hp.sp_fit; have := hp.sp_lo
  intro a h₁ h₂
  simp only [Region.Contains, argAddr] at h₁ h₂
  rw [Taint.sub_setWidth (by omega_arith)] at h₁
  rw [show (esp₀ s₀ + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 = addr (esp₀ s₀) 4 from rfl,
    addr_eq (by omega_arith)] at h₂
  obtain hE : ((esp₀ s₀).setWidth 64).toNat = (esp₀ s₀).toNat := addr_toNat _
  generalize (esp₀ s₀).setWidth 64 = b at *
  bv_omega

theorem ret_stk : (retR s₀).Disjoint (stkR s₀) := by
  have := hp.sp_fit; have := hp.sp_lo
  intro a h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  rw [Taint.sub_setWidth (by omega_arith)] at h₂
  obtain hE : ((esp₀ s₀).setWidth 64).toNat = (esp₀ s₀).toNat := addr_toNat _
  generalize (esp₀ s₀).setWidth 64 = b at *
  bv_omega

/-- The arguments are kept by anything that writes only `y`, `scratch` and the
stack below `esp`. -/
theorem arg_keep {m : Mem} (hf : Frame [yR s₀, scR s₀, stkR s₀] s₀.mem m) {d : Nat} (hd₁ : 4 ≤ d)
    (hd : d + 4 ≤ 24) : m.readW (addr (esp₀ s₀) d) 32 = s₀.mem.readW (addr (esp₀ s₀) d) 32 := by
  refine hf.readW (r := ⟨addr (esp₀ s₀) d, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.a_y.sub_left (arg_sub hp hd₁ hd)
  · exact hp.a_s.sub_left (arg_sub hp hd₁ hd)
  · exact (stk_arg hp).symm.sub_left (arg_sub hp hd₁ hd)

end

theorem in_s (s₀ : State) {o n : Nat} (h : o + n ≤ 128) :
    (scR s₀).Contains (scA s₀ + BitVec.ofNat 64 o) n :=
  contains_off h (by omega_arith)

theorem s_sub (s₀ : State) {o n : Nat} (h : o + n ≤ 128) :
    Region.Sub ⟨scA s₀ + BitVec.ofNat 64 o, n⟩ (scR s₀) :=
  sub_off h (by omega_arith)

/-! ## The loop invariant -/

/-- After `k` pairs. -/
structure Inv (s₀ : State) (k : Nat) (s : State) : Prop where
  k_le : k ≤ rr s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  esp : s.gpr .esp = esp₀ s₀
  ebx : s.gpr .ebx = bP s₀ + BitVec.ofNat 32 (128 * k)
  esi : s.gpr .esi = yP s₀ + BitVec.ofNat 32 (64 * k)
  edi : s.gpr .edi = yP s₀ + BitVec.ofNat 32 (64 * (rr s₀ + k))
  ebp : s.gpr .ebp = xP32 s₀ k
  frame : Frame [yR s₀, scR s₀, stkR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem
  done : ∀ i < k, bytesAt s.mem (yE s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i) ∧
    bytesAt s.mem (yO s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i + 1)
  x : bytesAt s.mem (xP s₀ k) 64 = xBefore (B s₀) (rr s₀) (2 * k)

/-- The input is unchanged in any memory that differs from the initial one
only in `y`, `scratch` and the stack. -/
theorem b_frame {s₀ : State} (hp : Pre s₀) {m : Mem} (hf : Frame [yR s₀, scR s₀, stkR s₀] s₀.mem m)
    {o n : Nat} (ho : o + n ≤ 128 * rr s₀) :
    bytesAt m (bA s₀ + BitVec.ofNat 64 o) n = bytesAt s₀.mem (bA s₀ + BitVec.ofNat 64 o) n := by
  refine frame_bytesAt hf (fun r hr => ?_) (by have := r_lt hp; omega_arith)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.b_y.sub_left (b_sub hp ho)
  · exact hp.b_s.sub_left (b_sub hp ho)
  · exact hp.stk_b.symm.sub_left (b_sub hp ho)

/-- Block `i` of the input. -/
theorem blk_B (s₀ : State) {i : Nat} (hi : i < 2 * rr s₀) :
    blk (B s₀) i = bytesAt s₀.mem (bA s₀ + BitVec.ofNat 64 (64 * i)) 64 :=
  blk_bytesAt _ _ (by omega_arith)

/-! ## A call of `vg_salsa20_8` on a block of `y` -/

/-- A 64-byte slot of `y` at offset `o`. -/
abbrev slot (s₀ : State) (o : Nat) : Region := ⟨yA s₀ + BitVec.ofNat 64 o, 64⟩

theorem calleeSaved_ne {r : Reg} (hr : r ∈ calleeSaved) : r ≠ .eax := by
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide

theorem salsaAt_ok {c : Prog isa} (hS : SalsaSpec c) {s₀ : State} (hp : Pre s₀) {dR : Reg}
    (hdR : dR ≠ .esp) (hdR' : dR ≠ .eax) {s : State} {o : Nat} (ho : o + 64 ≤ 128 * rr s₀)
    (hd : s.gpr dR = yP s₀ + BitVec.ofNat 32 o) (hesp : s.gpr .esp = esp₀ s₀) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) (hf : Frame [yR s₀, scR s₀, stkR s₀] s₀.mem s.mem) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [slot s₀ o, ⟨scA s₀, 64⟩, stkR s₀] s.mem s'.mem →
      bytesAt s'.mem (yA s₀ + BitVec.ofNat 64 o) 64 =
        salsa (bytesAt s.mem (yA s₀ + BitVec.ofNat 64 o) 64) → Q s') :
    WP isa (salsaAt c dR) s Q := by
  obtain lt := r_lt hp
  unfold salsaAt
  refine WP.seq (wp_movm (a := addr (esp₀ s₀) 20) (by rw [ea_at, hesp])
    (by rw [hrd, hwr]; exact arg_in hp (by omega_arith) (by omega_arith)) fun s₁ u₁ => WP.block_nil ?_)
  obtain e₁ : s₁.gpr .eax = sc s₀ := by rw [u₁.gpr, arg_keep hp hf (by omega_arith) (by omega_arith)]; rfl
  obtain e₃ : ∀ r ∈ calleeSaved, s₁.gpr r = s.gpr r := fun r hr => u₁.other _ (calleeSaved_ne hr)
  obtain e₄ : s₁.gpr .esp = esp₀ s₀ := by rw [e₃ _ (by simp [calleeSaved]), hesp]
  obtain ea : (yP s₀ + BitVec.ofNat 32 o).setWidth 64 = yA s₀ + BitVec.ofNat 64 o := y_addr hp (by omega_arith)
  obtain hsub : Region.Sub (slot s₀ o) (yR s₀) := y_sub hp ho
  obtain hsub' : Region.Sub ⟨scA s₀, 64⟩ (scR s₀) := Region.sub_prefix (by omega_arith)
  obtain hsc : (scR s₀).Contains (scA s₀) 64 := by
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_arith
  refine hS s₁ dR _ _ hdR (by rw [u₁.other _ hdR', hd]) e₁ (y_fit hp ho) (by have := hp.s_nw; omega_arith)
    (by rw [ea]; exact hp.y_s.sub_left hsub |>.sub_right hsub') (by rw [e₄]; exact hp.sp_lo)
    (by rw [e₄, ea]; exact hp.stk_y.sub_right hsub) (by rw [e₄]; exact hp.stk_s.sub_right hsub')
    (by rw [u₁.wr, hwr, hp.wr, ea]; exact InRegions.of_mem (by simp) (in_y hp ho))
    (by rw [u₁.wr, hwr, hp.wr]; exact InRegions.of_mem (R := scR s₀) (by simp) hsc)
    _ fun s' hrd' hwr' hcs hf' hb => hQ s' (by rw [hrd', u₁.rd]) (by rw [hwr', u₁.wr])
      (fun r hr => by rw [hcs r hr, e₃ r hr]) (by rw [u₁.mem, ea, e₄] at hf'; exact hf')
      (by rw [ea] at hb; rw [hb, u₁.mem])

/-! ## One pair -/

theorem slot_s {s₀ : State} (hp : Pre s₀) {o : Nat} (ho : o + 64 ≤ 128 * rr s₀) :
    (slot s₀ o).Disjoint ⟨scA s₀, 64⟩ :=
  (hp.y_s.sub_left (y_sub hp ho)).sub_right (Region.sub_prefix (by omega_arith))

theorem slot_stk {s₀ : State} (hp : Pre s₀) {o : Nat} (ho : o + 64 ≤ 128 * rr s₀) :
    (slot s₀ o).Disjoint (stkR s₀) :=
  (hp.stk_y.sub_right (y_sub hp ho)).symm

/-- Where `X` is, as an address. -/
theorem xP_addr {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < rr s₀) :
    (xP32 s₀ k).setWidth 64 = xP s₀ k := by
  cases k with
  | zero => exact b_addr hp (by have := hp.pos; omega_arith)
  | succ j => exact y_addr hp (by omega_arith)

theorem xP_fit {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < rr s₀) :
    (xP32 s₀ k).toNat + 64 ≤ 2 ^ 32 := by
  cases k with
  | zero => exact b_fit hp (by have := hp.pos; omega_arith)
  | succ j => exact y_fit hp (by omega_arith)

theorem xP_in {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < rr s₀) {s : State}
    (hrd : s.rd = [bR s₀, argR s₀]) (hwr : s.wr = [yR s₀, scR s₀]) :
    ∀ i < 4, InRegions (s.rd ++ s.wr) (xP s₀ k + BitVec.ofNat 64 (16 * i)) 16 := by
  intro i hi
  rw [hrd, hwr]
  cases k with
  | zero =>
    simp only [xP]
    rw [add_ofNat]
    exact InRegions.of_mem (by simp) (in_b hp (by have := hp.pos; omega_arith))
  | succ j =>
    simp only [xP]
    rw [add_ofNat]
    exact InRegions.of_mem (by simp) (in_y hp (by omega_arith))

theorem xP_disj {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < rr s₀) :
    Region.Disjoint (slot s₀ (64 * k)) ⟨xP s₀ k, 64⟩ := by
  cases k with
  | zero => exact yb_disj hp (by omega_arith) (by have := hp.pos; omega_arith)
  | succ j => exact y_disj hp (by omega_arith) (by omega_arith) (by omega_arith)

/-- What a call's frame keeps: our caller's saved registers. -/
theorem saved_keep {s₀ : State} (hp : Pre s₀) {o : Nat} (ho : o + 64 ≤ 128 * rr s₀) {m m' : Mem}
    (hf : Frame [slot s₀ o, ⟨scA s₀, 64⟩, stkR s₀] m m') (h : Saved s₀ m) : Saved s₀ m' := by
  intro p hp'
  rw [← h p hp']
  obtain hp4 : p.2 + 4 ≤ 128 ∧ 64 ≤ p.2 := by
    simp only [bmSaved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl <;> simp
  obtain hsub : Region.Sub ⟨scA s₀ + BitVec.ofNat 64 p.2, 4⟩ (scR s₀) := s_sub s₀ (by omega_arith)
  refine hf.readW (r := ⟨scA s₀ + BitVec.ofNat 64 p.2, 4⟩) (Region.contains_self _ _) (fun r hr => ?_)
    (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hp.y_s.sub_left (y_sub hp ho)).sub_right hsub |>.symm
  · have := disj_off (scA s₀) (o₁ := p.2) (n₁ := 4) (o₂ := 0) (n₂ := 64) (by omega_arith) (by omega_arith)
      (by omega_arith) (by omega_arith) (by omega_arith)
    simpa using this
  · exact (hp.stk_s.sub_right hsub).symm

/-- What a call's frame keeps: the other blocks of `y`. -/
theorem slot_keep {s₀ : State} (hp : Pre s₀) {o o' : Nat} (ho : o + 64 ≤ 128 * rr s₀)
    (ho' : o' + 64 ≤ 128 * rr s₀) (hd : o' + 64 ≤ o ∨ o + 64 ≤ o') {m m' : Mem}
    (hf : Frame [slot s₀ o, ⟨scA s₀, 64⟩, stkR s₀] m m') :
    bytesAt m' (yA s₀ + BitVec.ofNat 64 o') 64 = bytesAt m (yA s₀ + BitVec.ofNat 64 o') 64 := by
  refine frame_bytesAt hf (fun r hr => ?_) (by omega_arith)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact y_disj hp hd ho' ho
  · exact slot_s hp ho'
  · exact slot_stk hp ho'

theorem frame_big {s₀ : State} (hp : Pre s₀) {o : Nat} (ho : o + 64 ≤ 128 * rr s₀) {m m' : Mem}
    (hf : Frame [slot s₀ o, ⟨scA s₀, 64⟩, stkR s₀] m m') : Frame [yR s₀, scR s₀, stkR s₀] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨yR s₀, List.mem_cons_self, y_sub hp ho⟩
    · exact ⟨scR s₀, List.mem_cons_of_mem _ List.mem_cons_self, Region.sub_prefix (by omega_arith)⟩
    · exact ⟨stkR s₀, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
        fun _ h => h⟩

/-- Half a pair: `T = X xor B[i]` into block `o` of `y`, then Salsa20/8 of it. -/
theorem half_ok {c : Prog isa} (hS : SalsaSpec c) {s₀ : State} (hp : Pre s₀) {dR xR sR : Reg}
    (hd : dR ≠ .eax) (hd' : dR ≠ .esp) (hx : xR ≠ .eax) (hs : sR ≠ .eax) {o : Nat}
    (ho : o + 64 ≤ 128 * rr s₀) {x : BitVec 32} (fx : x.toNat + 64 ≤ 2 ^ 32) {ob : Nat}
    (hob : ob + 64 ≤ 128 * rr s₀) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hesp : s.gpr .esp = esp₀ s₀) (hf : Frame [yR s₀, scR s₀, stkR s₀] s₀.mem s.mem)
    (gd : s.gpr dR = yP s₀ + BitVec.ofNat 32 o) (gx : s.gpr xR = x)
    (gs : s.gpr sR = bP s₀ + BitVec.ofNat 32 ob)
    (hdx : Region.Disjoint (slot s₀ o) ⟨x.setWidth 64, 64⟩)
    (hinx : ∀ i < 4, InRegions (s.rd ++ s.wr) (x.setWidth 64 + BitVec.ofNat 64 (16 * i)) 16)
    {P : Prog isa} {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [slot s₀ o, ⟨scA s₀, 64⟩, stkR s₀] s.mem s'.mem →
      bytesAt s'.mem (yA s₀ + BitVec.ofNat 64 o) 64 =
        salsa (xorBytes (bytesAt s.mem (x.setWidth 64) 64)
          (bytesAt s.mem (bA s₀ + BitVec.ofNat 64 ob) 64)) →
      WP isa P s' Q) :
    WP isa (.block (xor64 dR xR sR)) s fun s' => WP isa (.seq (salsaAt c dR) P) s' Q := by
  obtain lt := r_lt hp
  obtain ed : (yP s₀ + BitVec.ofNat 32 o).setWidth 64 = yA s₀ + BitVec.ofNat 64 o := y_addr hp (by omega_arith)
  obtain eb : (bP s₀ + BitVec.ofNat 32 ob).setWidth 64 = bA s₀ + BitVec.ofNat 64 ob := b_addr hp (by omega_arith)
  rw [← List.append_nil (xor64 dR xR sR)]
  refine xor64_ok hd hx hs (y_fit hp ho) fx (b_fit hp hob) (by rw [ed]; exact hdx)
    (by rw [ed, eb]; exact yb_disj hp ho hob) 4 (Nat.le_refl _) [] s _ gd gx gs hinx
    (fun i hi => by
      rw [hrd, hwr, hp.rd, hp.wr, eb, add_ofNat]; exact InRegions.of_mem (by simp) (in_b hp (by omega_arith)))
    (fun i hi => by
      rw [hwr, hp.wr, ed, add_ofNat]; exact InRegions.of_mem (by simp) (in_y hp (by omega_arith)))
    fun s₁ g₁ rd₁ wr₁ m₁ => WP.block_nil ?_
  rw [ed, eb, show 16 * 4 = 64 from rfl] at m₁
  obtain l1 : (xorBytes (bytesAt s.mem (x.setWidth 64) 64)
      (bytesAt s.mem (bA s₀ + BitVec.ofNat 64 ob) 64)).length = 64 := by
    rw [xorBytes_length _ _ (by simp [bytesAt_length]), bytesAt_length]
  obtain f₁ : Frame [slot s₀ o] s.mem s₁.mem := by
    rw [m₁]; exact writeBytes_frame _ _ _ (by rw [l1]; exact Region.contains_self _ _)
  obtain hw := bytesAt_writeBytes_self s.mem (yA s₀ + BitVec.ofNat 64 o) _ (by rw [l1]; omega_arith)
  rw [l1] at hw
  obtain hf₁ : Frame [yR s₀, scR s₀, stkR s₀] s₀.mem s₁.mem :=
    hf.trans (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨yR s₀, List.mem_cons_self, y_sub hp ho⟩)
  refine WP.seq (salsaAt_ok hS hp hd' hd ho (by rw [g₁ _ hd, gd]) (by rw [g₁ _ (by decide), hesp])
    (by rw [rd₁, hrd]) (by rw [wr₁, hwr]) hf₁ fun s₂ rd₂ wr₂ cs₂ f₂ b₂ => ?_)
  refine hQ s₂ (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])
    (fun r hr => by rw [cs₂ r hr, g₁ r (calleeSaved_ne hr)])
    ((f₁.mono (by simp)).trans f₂) ?_
  rw [b₂, m₁, hw]

/-- The state after both halves of pair `k`. -/
structure Mid (s₀ : State) (k : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  esp : s.gpr .esp = esp₀ s₀
  ebx : s.gpr .ebx = bP s₀ + BitVec.ofNat 32 (64 * (2 * k + 1))
  esi : s.gpr .esi = yP s₀ + BitVec.ofNat 32 (64 * k)
  edi : s.gpr .edi = yP s₀ + BitVec.ofNat 32 (64 * (rr s₀ + k))
  frame : Frame [yR s₀, scR s₀, stkR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem
  done : ∀ i < k + 1, bytesAt s.mem (yE s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i) ∧
    bytesAt s.mem (yO s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i + 1)

/-- The memory after pair `k`. -/
theorem mem_ok {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < rr s₀) {s s₂ s₅ : State}
    (h : Inv s₀ k s)
    (f₂ : Frame [slot s₀ (64 * k), ⟨scA s₀, 64⟩, stkR s₀] s.mem s₂.mem)
    (b₂ : bytesAt s₂.mem (yE s₀ k) 64 =
      salsa (xorBytes (bytesAt s.mem (xP s₀ k) 64) (bytesAt s.mem (bA s₀ + BitVec.ofNat 64 (128 * k)) 64)))
    (f₅ : Frame [slot s₀ (64 * (rr s₀ + k)), ⟨scA s₀, 64⟩, stkR s₀] s₂.mem s₅.mem)
    (b₅ : bytesAt s₅.mem (yO s₀ k) 64 = salsa (xorBytes (bytesAt s₂.mem (yE s₀ k) 64)
      (bytesAt s₂.mem (bA s₀ + BitVec.ofNat 64 (64 * (2 * k + 1))) 64))) :
    Frame [yR s₀, scR s₀, stkR s₀] s₀.mem s₅.mem ∧ Saved s₀ s₅.mem ∧
    ∀ i < k + 1, bytesAt s₅.mem (yE s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i) ∧
      bytesAt s₅.mem (yO s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i + 1) := by
  obtain lt := r_lt hp
  obtain oE : 64 * k + 64 ≤ 128 * rr s₀ := by omega_arith
  obtain oO : 64 * (rr s₀ + k) + 64 ≤ 128 * rr s₀ := by omega_arith
  obtain F₂ := h.frame.trans (frame_big hp oE f₂)
  obtain yE_eq : bytesAt s₂.mem (yE s₀ k) 64 = yAt (B s₀) (rr s₀) (2 * k) := by
    rw [b₂, h.x, b_frame hp h.frame (by omega_arith : 128 * k + 64 ≤ 128 * rr s₀),
      show 128 * k = 64 * (2 * k) by omega_arith, ← blk_B s₀ (by omega_arith), yAt_eq]
  obtain hb : bytesAt s₂.mem (bA s₀ + BitVec.ofNat 64 (64 * (2 * k + 1))) 64 =
      blk (B s₀) (2 * k + 1) := by
    rw [blk_B s₀ (by omega_arith)]
    exact b_frame hp F₂ (by omega_arith)
  refine ⟨F₂.trans (frame_big hp oO f₅), saved_keep hp oO f₅ (saved_keep hp oE f₂ h.saved),
    fun i hi => ?_⟩
  by_cases hik : i = k
  · subst i
    refine ⟨?_, ?_⟩
    · rw [slot_keep hp oO oE (by omega_arith) f₅, yE_eq]
    · rw [b₅, yE_eq, hb, yAt_eq (B s₀) (rr s₀) (2 * k + 1), xBefore_succ]
  · have hi' : i < k := by omega_arith
    obtain ⟨d₁, d₂⟩ := h.done i hi'
    refine ⟨?_, ?_⟩
    · rw [slot_keep hp oO (by omega_arith) (by omega_arith) f₅, slot_keep hp oE (by omega_arith) (by omega_arith) f₂, d₁]
    · rw [slot_keep hp oO (by omega_arith) (by omega_arith) f₅, slot_keep hp oE (by omega_arith) (by omega_arith) f₂, d₂]

/-- Both halves of pair `k`. -/
theorem halves_ok {c : Prog isa} (hS : SalsaSpec c) {s₀ : State} (hp : Pre s₀) {k : Nat}
    (hk : k < rr s₀) {s : State} (h : Inv s₀ k s) {P : Prog isa} {Q : State → Prop}
    (hQ : ∀ s', Mid s₀ k s' → WP isa P s' Q) :
    WP isa (.seq (.block (xor64 .esi .ebp .ebx)) <| .seq (salsaAt c .esi) <|
      .seq (.block (.alu .add .ebx (.imm 64) :: xor64 .edi .esi .ebx)) <| .seq (salsaAt c .edi) P)
      s Q := by
  obtain lt := r_lt hp
  obtain hrd : s.rd = [bR s₀, argR s₀] := by rw [h.rd, hp.rd]
  obtain hwr : s.wr = [yR s₀, scR s₀] := by rw [h.wr, hp.wr]
  obtain oE : 64 * k + 64 ≤ 128 * rr s₀ := by omega_arith
  obtain oO : 64 * (rr s₀ + k) + 64 ≤ 128 * rr s₀ := by omega_arith
  obtain ex := xP_addr hp hk
  refine WP.seq (half_ok hS hp (by decide) (by decide) (by decide) (by decide) oE (xP_fit hp hk)
    (ob := 128 * k) (by omega_arith) h.rd h.wr h.esp h.frame h.esi h.ebp h.ebx
    (by rw [ex]; exact xP_disj hp hk) (by rw [ex]; exact xP_in hp hk hrd hwr)
    fun s₂ rd₂ wr₂ cs₂ f₂ b₂ => ?_)
  rw [ex] at b₂
  refine WP.seq (wp_addi fun s₃ u₃ => ?_)
  obtain k3 : ∀ r, r ≠ .ebx → r ∈ calleeSaved → s₃.gpr r = s.gpr r := fun r h1 h2 => by
    rw [u₃.other _ h1, cs₂ r h2]
  obtain e3 : s₃.gpr .ebx = bP s₀ + BitVec.ofNat 32 (64 * (2 * k + 1)) := by
    rw [u₃.gpr, cs₂ _ (by simp [calleeSaved]), h.ebx, add32_lit]; congr 2; omega_arith
  obtain hf₂ : Frame [yR s₀, scR s₀, stkR s₀] s₀.mem s₃.mem := by
    rw [u₃.mem]; exact h.frame.trans (frame_big hp oE f₂)
  obtain e5 : s₃.gpr .esi = yP s₀ + BitVec.ofNat 32 (64 * k) := by
    rw [k3 _ (by decide) (by simp [calleeSaved]), h.esi]
  refine half_ok hS hp (by decide) (by decide) (by decide) (by decide) oO (y_fit hp oE)
    (ob := 64 * (2 * k + 1)) (by omega_arith) (by rw [u₃.rd, rd₂, h.rd]) (by rw [u₃.wr, wr₂, h.wr])
    (by rw [k3 _ (by decide) (by simp [calleeSaved]), h.esp]) hf₂
    (by rw [k3 _ (by decide) (by simp [calleeSaved]), h.edi]) e5 e3
    (by rw [y_addr hp (by omega_arith)]; exact y_disj hp (by omega_arith) oO oE)
    (fun i hi => by
      rw [u₃.rd, u₃.wr, rd₂, wr₂, hrd, hwr, y_addr hp (by omega_arith), add_ofNat]
      exact InRegions.of_mem (by simp) (in_y hp (by omega_arith)))
    fun s₅ rd₅ wr₅ cs₅ f₅ b₅ => ?_
  rw [u₃.mem, y_addr hp (by omega_arith)] at b₅
  rw [u₃.mem] at f₅
  obtain ⟨F, S, D⟩ := mem_ok hp hk h f₂ b₂ f₅ b₅
  obtain k5 : ∀ r, r ≠ .ebx → r ∈ calleeSaved → s₅.gpr r = s.gpr r := fun r h1 h2 => by
    rw [cs₅ r h2, k3 r h1 h2]
  exact hQ s₅ ⟨by rw [rd₅, u₃.rd, rd₂, h.rd], by rw [wr₅, u₃.wr, wr₂, h.wr],
    by rw [k5 _ (by decide) (by simp [calleeSaved]), h.esp],
    by rw [cs₅ _ (by simp [calleeSaved]), e3],
    by rw [k5 _ (by decide) (by simp [calleeSaved]), h.esi],
    by rw [k5 _ (by decide) (by simp [calleeSaved]), h.edi], F, S, D⟩

/-- `y + 64 (k + 1)` is `y + 64 r` exactly when `k + 1 = r`. -/
theorem cmp_end (y : BitVec 32) {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (y + BitVec.ofNat 32 a - (BitVec.ofNat 32 b + y) == 0) = decide (a = b) := by
  rw [show y + BitVec.ofNat 32 a - (BitVec.ofNat 32 b + y) = BitVec.ofNat 32 a - BitVec.ofNat 32 b by
    bv_omega]
  exact Proof.Sha256.X86.Stream.sub_beq ha hb

theorem bmNext_eq : bmNext = .mov .ebp (.reg .edi) :: .alu .add .ebx (.imm 64) ::
    .alu .add .esi (.imm 64) :: .alu .add .edi (.imm 64) ::
    (timesR 64 ++ ([.mov .ecx (.mem (at_ .esp 12)), .alu .add .eax (.reg .ecx), .alu .cmp .esi (.reg .eax)] :
      List Instr)) := rfl

/-- The pointers move on, and ZF is set after the last pair. -/
theorem regs_ok {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < rr s₀) {s : State}
    (h : Mid s₀ k s) :
    WP isa (.block bmNext) s fun s' => Inv s₀ (k + 1) s' ∧ s'.zf = some (decide (k + 1 = rr s₀)) := by
  obtain lt := r_lt hp
  rw [bmNext_eq]
  refine wp_mov fun s₆ u₆ => wp_addi fun s₇ u₇ => wp_addi fun s₈ u₈ => wp_addi fun s₉ u₉ => ?_
  obtain m₉ : s₉.mem = s.mem := by rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem]
  obtain g₉ : ∀ r, r ≠ .ebp → r ≠ .ebx → r ≠ .esi → r ≠ .edi → s₉.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 => by rw [u₉.other _ h4, u₈.other _ h3, u₇.other _ h2, u₆.other _ h1]
  obtain esp₉ : s₉.gpr .esp = esp₀ s₀ := by
    rw [g₉ _ (by decide) (by decide) (by decide) (by decide), h.esp]
  obtain rd₉ : s₉.rd = s₀.rd := by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, h.rd]
  obtain wr₉ : s₉.wr = s₀.wr := by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, h.wr]
  refine timesR_ok (r := arg s₀ 1) (by rw [esp₉, m₉, arg_keep hp h.frame (by omega_arith) (by omega_arith)]; rfl)
    (by rw [esp₉, rd₉, wr₉]; exact arg_in hp (by omega_arith) (by omega_arith)) fun t e o mt rdt wrt => ?_
  refine wp_movm (a := addr (esp₀ s₀) 12) (by rw [ea_at, o _ (by decide) (by decide) (by decide), esp₉])
    (by rw [rdt, wrt, rd₉, wr₉]; exact arg_in hp (by omega_arith) (by omega_arith)) fun t₀ u₀ => ?_
  refine wp_add fun t₁ u₁ => wp_cmp fun t₂ f₂ _ z₂ => WP.block_nil ?_
  obtain gt : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t₂.gpr r = s₉.gpr r := fun r h1 h2 h3 => by
    rw [f₂.gpr, u₁.other _ h1, u₀.other _ h2, o r h1 h2 h3]
  obtain mt₂ : t₂.mem = s.mem := by rw [f₂.mem, u₁.mem, u₀.mem, mt, m₉]
  obtain esi₉ : s₉.gpr .esi = yP s₀ + BitVec.ofNat 32 (64 * (k + 1)) := by
    rw [u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), h.esi, add32_lit]
    congr 2
  refine ⟨⟨(by omega_arith), by rw [f₂.rd, u₁.rd, u₀.rd, rdt, rd₉], by rw [f₂.wr, u₁.wr, u₀.wr, wrt, wr₉],
    by rw [gt _ (by decide) (by decide) (by decide), esp₉], ?_, ?_, ?_, ?_,
    by rw [mt₂]; exact h.frame, by rw [mt₂]; exact h.saved, by rw [mt₂]; exact h.done, ?_⟩, ?_⟩
  · rw [gt _ (by decide) (by decide) (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.gpr, u₆.other _ (by decide), h.ebx, add32_lit]
    congr 2; omega_arith
  · rw [gt _ (by decide) (by decide) (by decide), esi₉]
  · rw [gt _ (by decide) (by decide) (by decide), u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), h.edi, add32_lit]
    congr 2
  · rw [gt _ (by decide) (by decide) (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), u₆.gpr, h.edi]
    rfl
  · rw [mt₂]
    show bytesAt s.mem (yO s₀ k) 64 = _
    rw [(h.done k (by omega_arith)).2]
    rfl
  · have hax : t₁.gpr .eax = BitVec.ofNat 32 (64 * rr s₀) + yP s₀ := by
      rw [u₁.gpr, u₀.gpr, u₀.other _ (by decide), e, mt, m₉, arg_keep hp h.frame (by omega_arith) (by omega_arith),
        show (64 : BitVec 32).toNat = 64 from rfl, Nat.mul_comm]
      rfl
    rw [z₂, u₁.other _ (by decide), u₀.other _ (by decide), o _ (by decide) (by decide) (by decide), esi₉,
      hax,
      cmp_end _ (by omega_arith) (by omega_arith)]
    exact congrArg some (decide_eq_decide.mpr (by omega_arith))

theorem body_ok {c : Prog isa} (hS : SalsaSpec c) {s₀ : State} (hp : Pre s₀) {k : Nat}
    (hk : k < rr s₀) {s : State} (h : Inv s₀ k s) :
    WP isa (bmBody c) s fun s' => Inv s₀ (k + 1) s' ∧ s'.zf = some (decide (k + 1 = rr s₀)) :=
  halves_ok hS hp hk h fun _ hm => regs_ok hp hk hm

end VG.Proof.Scrypt.X86.BlockMix

end

end

@[expose] public section

section

/-!
# scryptBlockMix on x86 (32-bit): the whole function

The prologue saves our caller's `ebx`, `esi`, `edi` and `ebp` in `scratch` and
sets up the loop's registers from the arguments; the loop runs the `r` pairs;
the epilogue restores the registers.
-/

namespace VG.Proof.Scrypt.X86.BlockMix

open VG VG.X86 VG.Impl.Scrypt.X86
open VG.Spec.Scrypt (bytesAt blk blockMix)
open VG.Proof.Scrypt (yAt xBefore blockMix_eq flatMap_congr)
open VG.Proof.Sha256.X86.Stream (Upd wp_mov wp_movm wp_add wp_subi)
open VG.Proof.Scrypt.Memory (add_ofNat InRegions.of_mem frame_bytesAt bytesAt_add
  bytesAt_blocks)

/-! ## The prologue -/

/-- The prologue's register moves. -/
def bmSetup : List Instr :=
  .mov .ebx (.mem (at_ .esp 4)) :: .mov .esi (.mem (at_ .esp 12)) ::
    (timesR 64 ++ ([.mov .edi (.reg .esi), .alu .add .edi (.reg .eax), .mov .ebp (.reg .ebx),
      .alu .add .ebp (.reg .eax), .alu .add .ebp (.reg .eax), .alu .sub .ebp (.imm 64)] : List Instr))

theorem prologue_eq : bmPrologue =
    .mov .eax (.mem (at_ .esp 20)) :: (bmSaved.map (fun p => Instr.store (at_ .eax p.2) p.1) ++ bmSetup) :=
  rfl

theorem bmSaved_bound : ∀ p ∈ bmSaved, p.2 + 4 ≤ 128 ∧ 64 ≤ p.2 ∧ p.1 ≠ .eax := by decide

theorem bmSaved_fits : Spill.Fits 128 bmSaved := by decide

theorem bmSaved_addr (s₀ : State) (hp : Pre s₀) :
    ∀ p ∈ bmSaved, addr (sc s₀) p.2 = scA s₀ + BitVec.ofNat 64 p.2 :=
  Spill.addr_eq_of_fits hp.s_nw bmSaved_fits

theorem save_ok {s₀ : State} (hp : Pre s₀) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s₁, (∀ r, r ≠ .eax → s₁.gpr r = s₀.gpr r) → s₁.gpr .eax = sc s₀ → s₁.rd = s₀.rd →
      s₁.wr = s₀.wr → Frame [scR s₀] s₀.mem s₁.mem → Saved s₀ s₁.mem → WP isa (.block rest) s₁ Q) :
    WP isa (.block (.mov .eax (.mem (at_ .esp 20)) ::
      (bmSaved.map (fun p => Instr.store (at_ .eax p.2) p.1) ++ rest))) s₀ Q := by
  have hs := hp.s_nw
  refine wp_movm (a := addr (esp₀ s₀) 20) rfl (arg_in hp (by omega_using []) (by omega_using [])) fun s₁ u₁ => ?_
  have e : s₁.gpr .eax = sc s₀ := u₁.gpr
  have ha := bmSaved_addr s₀ hp
  refine Spill.save_ok bmSaved (fun p hp' => ?_) fun s₂ u₂ => ?_
  · rw [e, u₁.wr, hp.wr, ha p hp']
    exact InRegions.of_mem (by simp) (in_s s₀ (bmSaved_fits.1 p hp'))
  refine k s₂ (fun r hr => by rw [u₂.gpr, u₁.other r hr]) (by rw [u₂.gpr, e]) (by rw [u₂.rd, u₁.rd])
    (by rw [u₂.wr, u₁.wr]) ?_ ?_
  · rw [u₂.mem, e, u₁.mem]
    exact Spill.saveMem_frame List.mem_cons_self _ _ _ _ fun p hp' => by
      rw [ha p hp']; exact in_s s₀ (bmSaved_fits.1 p hp')
  · rw [u₂.mem, e, u₁.mem]
    exact (Spill.saveMem_saved_addr _ _ bmSaved_fits hs).congr ha
      fun p hp' => u₁.other _ (bmSaved_bound p hp').2.2

/-- The registers the loop starts with. -/
theorem setup_ok {s₀ : State} (hp : Pre s₀) {s₁ : State} (g : ∀ r, r ≠ .eax → s₁.gpr r = s₀.gpr r)
    (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr) (hf : Frame [scR s₀] s₀.mem s₁.mem)
    (hsv : Saved s₀ s₁.mem) :
    WP isa (.block bmSetup) s₁ (Inv s₀ 0) := by
  have lt := r_lt hp
  have pos := hp.pos
  have hesp : s₁.gpr .esp = esp₀ s₀ := g _ (by decide)
  have hf' : Frame [yR s₀, scR s₀, stkR s₀] s₀.mem s₁.mem := hf.mono (by simp)
  have rd₁ : s₁.rd ++ s₁.wr = s₀.rd ++ s₀.wr := by rw [hrd, hwr]
  unfold bmSetup
  refine wp_movm (a := addr (esp₀ s₀) 4) (by rw [ea_at, hesp])
    (by rw [rd₁]; exact arg_in hp (by omega_using []) (by omega_using [])) fun a ua => ?_
  refine wp_movm (a := addr (esp₀ s₀) 12) (by rw [ea_at, ua.other _ (by decide), hesp])
    (by rw [ua.rd, ua.wr, rd₁]; exact arg_in hp (by omega_using []) (by omega_using [])) fun b ub => ?_
  have eb : b.gpr .esp = esp₀ s₀ := by rw [ub.other _ (by decide), ua.other _ (by decide), hesp]
  have mb : b.mem = s₁.mem := by rw [ub.mem, ua.mem]
  have bx : b.gpr .ebx = bP s₀ := by
    rw [ub.other _ (by decide), ua.gpr, arg_keep hp hf' (by omega_using []) (by omega_using [])]; rfl
  have bs : b.gpr .esi = yP s₀ := by
    rw [ub.gpr, ua.mem, arg_keep hp hf' (by omega_using []) (by omega_using [])]; rfl
  refine timesR_ok (r := arg s₀ 1) (by rw [eb, mb, arg_keep hp hf' (by omega_using []) (by omega_using [])]; rfl)
    (by rw [eb, ub.rd, ub.wr, ua.rd, ua.wr, rd₁]; exact arg_in hp (by omega_using []) (by omega_using []))
    fun t e o mt rdt wrt => ?_
  refine wp_mov fun c uc => wp_add fun d ud => wp_mov fun f uf => wp_add fun i ui => wp_add fun j uj =>
    wp_subi fun l ul _ => WP.block_nil ?_
  have e64 : t.gpr .eax = BitVec.ofNat 32 (rr s₀ * 64) := by rw [e]; rfl
  have kl : ∀ r, r ≠ .ebp → r ≠ .edi → r ≠ .eax → r ≠ .ecx → r ≠ .edx → l.gpr r = b.gpr r :=
    fun r h1 h2 h3 h4 h5 => by
      rw [ul.other _ h1, uj.other _ h1, ui.other _ h1, uf.other _ h1, ud.other _ h2, uc.other _ h2,
        o r h3 h4 h5]
  have ml : l.mem = s₁.mem := by rw [ul.mem, uj.mem, ui.mem, uf.mem, ud.mem, uc.mem, mt, mb]
  refine ⟨Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => absurd hi (by omega_using []), ?_⟩
  · rw [ul.rd, uj.rd, ui.rd, uf.rd, ud.rd, uc.rd, rdt, ub.rd, ua.rd, hrd]
  · rw [ul.wr, uj.wr, ui.wr, uf.wr, ud.wr, uc.wr, wrt, ub.wr, ua.wr, hwr]
  · rw [kl _ (by decide) (by decide) (by decide) (by decide) (by decide), eb]
  · rw [kl _ (by decide) (by decide) (by decide) (by decide) (by decide), bx]; simp
  · rw [kl _ (by decide) (by decide) (by decide) (by decide) (by decide), bs]; simp
  · rw [ul.other _ (by decide), uj.other _ (by decide), ui.other _ (by decide), uf.other _ (by decide),
      ud.gpr, uc.gpr, uc.other _ (by decide), e64, o _ (by decide) (by decide) (by decide), bs]
    congr 2; omega_using []
  · rw [ul.gpr, uj.gpr, ui.gpr, ui.other .eax (by decide), uf.gpr, uf.other .eax (by decide),
      ud.other .ebx (by decide), ud.other .eax (by decide), uc.other .ebx (by decide),
      uc.other .eax (by decide), e64, o _ (by decide) (by decide) (by decide), bx, add32,
      sub32 _ (by omega_using [pos])]
    show _ = bP s₀ + BitVec.ofNat 32 (128 * rr s₀ - 64)
    exact congrArg (HAdd.hAdd _) (congrArg (BitVec.ofNat 32) (by omega_using []))
  · rw [ml]; exact hf'
  · rw [ml]; exact hsv
  · rw [ml]
    show bytesAt s₁.mem (bA s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64)) 64 =
      blk (B s₀) (2 * rr s₀ - 1)
    rw [blk_B s₀ (by omega_using [pos]), show 64 * (2 * rr s₀ - 1) = 128 * rr s₀ - 64 by omega_using []]
    exact b_frame hp hf' (by omega_using [pos])

/-! ## The loop -/

theorem loop_ok {c : Prog isa} (hS : SalsaSpec c) {s₀ : State} (hp : Pre s₀) {s : State}
    (h : Inv s₀ 0 s) : WP isa (.loop (bmBody c) .ne) s (Inv s₀ (rr s₀)) :=
  count_loop hp.pos (Inv s₀) (fun _ hk _ h => body_ok hS hp hk h) h

/-! ## The epilogue -/

theorem epilogue_eq : bmEpilogue =
    .mov .eax (.mem (at_ .esp 20)) :: (bmSaved.map (fun p => Instr.mov p.1 (.mem (at_ .eax p.2))) ++ []) :=
  rfl

theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Inv s₀ (rr s₀) s) :
    WP isa (.block bmEpilogue) s fun s' => s'.mem = s.mem ∧ (∀ r ∈ calleeSaved, s'.gpr r = s₀.gpr r) := by
  have hs := hp.s_nw
  rw [epilogue_eq]
  refine wp_movm (a := addr (esp₀ s₀) 20) (by rw [ea_at, h.esp])
    (by rw [h.rd, h.wr]; exact arg_in hp (by omega_using []) (by omega_using [])) fun s₁ u₁ => ?_
  have e : s₁.gpr .eax = sc s₀ := by rw [u₁.gpr, arg_keep hp h.frame (by omega_using []) (by omega_using [])]; rfl
  have ha := bmSaved_addr s₀ hp
  refine Spill.restore_ok bmSaved (by decide) (fun p hp' => ?_)
    (by rw [e, u₁.mem]; exact h.saved.congr (fun p hp' => (ha p hp').symm) fun _ _ => rfl)
    fun s₂ u => WP.block_nil ⟨by rw [u.mem, u₁.mem],
      u.abi (by decide) (by decide) (by rw [u₁.other _ (by decide), h.esp])⟩
  rw [e, u₁.rd, u₁.wr, h.rd, h.wr, hp.rd, hp.wr, ha p hp']
  exact InRegions.of_mem (by simp) (in_s s₀ (bmSaved_fits.1 p hp'))

/-! ## The whole function -/

/-- The output, from the blocks the loop wrote. -/
theorem post_of {s₀ : State} {m : Mem}
    (h : ∀ i < rr s₀, bytesAt m (yE s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i) ∧
      bytesAt m (yO s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i + 1)) :
    bytesAt m (yA s₀) (128 * rr s₀) = blockMix (rr s₀) (B s₀) := by
  rw [blockMix_eq, show 128 * rr s₀ = 64 * rr s₀ + 64 * rr s₀ by omega_using [], bytesAt_add,
    bytesAt_blocks, bytesAt_blocks]
  congr 1
  · refine flatMap_congr fun i hi => ?_
    rw [List.mem_range] at hi
    exact (h i hi).1
  · refine flatMap_congr fun i hi => ?_
    rw [List.mem_range] at hi
    rw [add_ofNat, ← Nat.mul_add]
    exact (h i hi).2

theorem correct {c : Prog isa} (hS : SalsaSpec c) {s₀ : State} (hp : Pre s₀) :
    WP isa (blockMixWith c) s₀ fun s' =>
      abiPreserved s₀ s' ∧ Proof.Scrypt.blockMixX86.post s₀ s' := by
  unfold blockMixWith
  refine WP.seq ?_
  rw [prologue_eq]
  refine save_ok hp fun s₁ g _ hrd hwr hf hsv => ?_
  refine WP.mono (setup_ok hp g hrd hwr hf hsv) fun s₂ h₂ => ?_
  refine WP.seq (WP.mono (loop_ok hS hp h₂) fun s₃ h₃ => ?_)
  refine WP.mono (restore_ok hp h₃) fun s' ⟨hm', hg'⟩ => ⟨⟨hg', ?_⟩, ?_⟩
  · rw [hm']
    refine h₃.frame.readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [hp.ret_y, hp.ret_s, ret_stk hp]
  · show bytesAt s'.mem (yA s₀) (128 * rr s₀) = blockMix (rr s₀) (B s₀)
    rw [hm']
    exact post_of fun i hi => h₃.done i hi

end VG.Proof.Scrypt.X86.BlockMix

end

/-!
# scryptBlockMix on x86 (32-bit): verified

`SalsaSpec` of the verified Salsa20/8 Core, from its proof by `WP.callWith`;
then the `Verified` proof of `vg_scrypt_blockmix`. Only `esp` and the
arguments are public, and the taint analysis checks that nothing else reaches
an address or a branch: the words holding `y` and `scratch` are the bases of
the two writable regions, and the code reads the pointers and `r` from the
arguments, which it never writes. The proof is written against a contract
under which the code only reads its arguments, and moved to the shared
contract with `Verified.narrowTo`.
-/

namespace VG.Proof.Scrypt.X86.BlockMix

open VG VG.X86

theorem salsa_nosp : NoSp Impl.Scrypt.X86.salsa := NoSp.of_all (by decide +kernel)

theorem salsa_stack : stackUse Impl.Scrypt.X86.salsa = 0 := by decide +kernel

theorem salsaSpec : SalsaSpec Impl.Scrypt.X86.salsa := by
  intro s dR d sc hdR hd hsc fd fsc hds hlo hsd hss hind hins Q hQ
  let E := s.gpr .esp
  try rewrite [show s.gpr .esp = E from rfl] at *
  have hE : E = s.gpr .esp := rfl
  have hrs : Reg.esp ∉ [Reg.eax, dR] := by simp [Ne.symm hdR]
  have fit : 4 * [Reg.eax, dR].length + 4 ≤ (s.gpr .esp).toNat := by
    simp only [List.length_cons, List.length_nil]; omega
  let sE := (pushed [Reg.eax, dR] s).callEntry
  try rewrite [show (pushed [Reg.eax, dR] s).callEntry = sE from rfl] at *
  have hsE : sE = (pushed [Reg.eax, dR] s).callEntry := rfl
  have a0 : arg sE 0 = d := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [hd]
  have a1 : arg sE 1 = sc := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [hsc]
  have eA : argAddr sE 0 = (E - BitVec.ofNat 32 8).setWidth 64 := by
    rw [hsE, callEntry_argAddr0]; rfl
  have eSp : sE.gpr .esp = E - BitVec.ofNat 32 12 := by
    rw [hsE, callEntry_esp']; rfl
  have b8 : Region.Sub (below E 8) (below E 12) := below_sub (by omega_using []) hlo
  have r4 : Region.Sub ⟨(E - BitVec.ofNat 32 12).setWidth 64, 4⟩ (below E 12) := by
    have := below_inner (sp := E) (a := 4) (b := 12) (k := 8) (by omega_using []) hlo
    rw [show E - BitVec.ofNat 32 12 = E - BitVec.ofNat 32 8 - BitVec.ofNat 32 4 by bv_omega_arith]
    exact this
  have e12 : 4 * [Reg.eax, dR].length + stackUse Impl.Scrypt.X86.salsa + 4 = 12 := by
    rw [salsa_stack]; rfl
  refine WP.callWith (k := Proof.Scrypt.salsaX86) salsa_correct salsa_nosp (by simp) hrs
    (by rw [e12]; exact hlo)
    (rd := [⟨argAddr sE 0, 8⟩]) (wr := [⟨d.setWidth 64, 64⟩, ⟨sc.setWidth 64, 64⟩])
    ⟨?_, ?_, ?_⟩ fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  · rw [← hsE]
    simp only [Proof.Scrypt.salsaX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, eA, eSp]
    refine ⟨trivial, trivial, hds, hsd.sub_left b8, hss.sub_left b8, hsd.sub_left r4, hss.sub_left r4,
      fd, fsc, ?_⟩
    rw [sub_toNat hlo]; have := E.isLt; omega_using []
  · intro a n ⟨r, hr, hcn⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · refine InRegions_append_cons.mpr (.inl ?_)
      rw [eA] at hcn
      exact hcn
    · obtain ⟨r', hr', hc'⟩ := hind
      exact InRegions_append_cons.mpr (.inr ⟨r', List.mem_append_right _ hr', by
        have : (⟨d.setWidth 64, 64⟩ : Region).Contains a n := hcn
        simp only [Region.Contains] at this hc' ⊢
        bv_omega_arith⟩)
    · obtain ⟨r', hr', hc'⟩ := hins
      exact InRegions_append_cons.mpr (.inr ⟨r', List.mem_append_right _ hr', by
        have : (⟨sc.setWidth 64, 64⟩ : Region).Contains a n := hcn
        simp only [Region.Contains] at this hc' ⊢
        bv_omega_arith⟩)
  · intro a n ⟨r, hr, hcn⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · obtain ⟨r', hr', hc'⟩ := hind
      refine ⟨r', List.mem_cons_of_mem _ hr', ?_⟩
      simp only [Region.Contains] at hcn hc' ⊢
      bv_omega_arith
    · obtain ⟨r', hr', hc'⟩ := hins
      refine ⟨r', List.mem_cons_of_mem _ hr', ?_⟩
      simp only [Region.Contains] at hcn hc' ⊢
      bv_omega_arith
  · rw [e12] at f'
    have hsE' := callEntry_frame fit hrs
    rw [show 4 * [Reg.eax, dR].length + 4 = 12 from rfl, ← hsE] at hsE'
    rw [← hsE] at post
    simp only [Proof.Scrypt.salsaX86, arg_withRegions, State.withRegions_mem, a0] at post
    refine hQ s' rd' wr' cs' (f'.mono fun r hr => by simpa using hr) ?_
    -- The pop loses the arguments' frame, below `esp`, apart from the block.
    have fL : Frame [below E 12] s₂.mem s'.mem := Frame.below_mono (wr := []) m₂ (by simp) hlo
    rw [Proof.Scrypt.Memory.frame_bytesAt fL (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hsd.symm) (by omega_using []), post]
    congr 1
    refine Proof.Scrypt.Memory.frame_bytesAt hsE' (fun r hr => ?_) (by omega_using [])
    simp only [List.mem_singleton] at hr; subst hr
    exact hsd.symm

/-! ## Constant time -/

/-- The initial taint: `esp` and the arguments are public, the words holding
`y` and `scratch` are the base addresses of the writable regions (`y` of a
length the analysis does not know), and the 12 bytes below `esp` are outside
them. -/
def τ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [0, 128], argLen := 24,
    argBases := [(12, 0), (20, 1)], room := 12 }

theorem wf₀ {s : State} (h : Proof.Scrypt.blockMixX86.pre s) : VG.X86.Taint.Wf τ₀ s := by
  have hp := pre_of h
  have hy := hp.y_nw; have hsc := hp.s_nw; have hs := hp.sp_fit; have hlo := hp.sp_lo
  obtain ⟨-, -, -, -, -, -, -, -, -, -, k1, k2, -⟩ := h
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨by simp [hp.wr, τ₀], ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨hs, ?_⟩, ?_⟩ fun _ => ⟨hlo, ?_⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, and_true]
    exact ⟨hp.y_s, fun _ h => h.elim⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega_arith
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega) hp.ret_y hp.a_y
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega) hp.ret_s hp.a_s
  · intro p hp'
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · rw [hp.r3] at k1; exact k1
    · exact k2

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.Scrypt.blockMixX86.pre s₁)
    (h₂ : Proof.Scrypt.blockMixX86.pre s₂) (hpub : Proof.Scrypt.blockMixX86.pub s₁ s₂) :
    VG.X86.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have hp₁ := pre_of h₁; have hp₂ := pre_of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ h₁, wf₀ h₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]
    simp only [yR, scR, yA, scA, yP, sc, rr, ha 1 (by omega_using []), ha 2 (by omega_using []), ha 4 (by omega_using [])]
  · simp only [τ₀] at hk
    rw [show VG.X86.Taint.depth τ₀.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq hp₁.sp_fit h4 hk, VG.X86.Taint.argByte_eq hp₂.sp_fit h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega_using [])), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega_using []))]
    exact congrArg _ (ha _ (by omega_using [hk]))

theorem blockMix_correct (s : State) (hs : Proof.Scrypt.blockMixX86.pre s) :
    ∃ t s', Exec isa Impl.Scrypt.X86.blockMix s t s' ∧ abiPreserved s s' ∧
      Proof.Scrypt.blockMixX86.post s s' := by
  obtain ⟨t, s', he, h⟩ := BlockMix.correct salsaSpec (pre_of hs)
  exact ⟨t, s', he, h⟩

theorem blockMix_ct : ConstantTime isa Proof.Scrypt.blockMixX86.pre Proof.Scrypt.blockMixX86.pub
    Impl.Scrypt.X86.blockMix :=
  VG.Taint.constantTime (A := VG.X86.sseTaint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp) (by taint_decide)

end VG.Proof.Scrypt.X86.BlockMix
