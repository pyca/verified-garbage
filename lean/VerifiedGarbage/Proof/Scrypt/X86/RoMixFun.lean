import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Scrypt.X86.Common
import VerifiedGarbage.Proof.Scrypt.RoMix
import VerifiedGarbage.Impl.Scrypt.X86.RoMix

section

/-!
# scryptROMix on x86 (32-bit): the precondition

The regions the function works on, and `BlockMixSpec`: what a call of
`vg_scrypt_blockmix` in a frame of its arguments does (the verified one meets
it: `Proof/Scrypt/X86/RoMixCT.lean`). As on 32-bit ARM
(`Proof/Scrypt/Arm/RoMixCT.lean`), with the pointers and lengths read from the
arguments on the stack, which nothing writes, and the calls using the 36 bytes
below `esp` (`stkR`), which the memory frames include.
-/

namespace VG.Proof.Scrypt.X86.RoMix

open VG VG.X86 VG.Impl.Scrypt.X86
open VG.Spec.Scrypt (bytesAt blockMix integerify leNat)
open VG.Proof.Scrypt (bytesAt_add' bytesAt_length' leNat_append leNat_bytesAt blk_bytesAt')
open VG.Proof.Sha256.X86.Stream (addr_toNat)
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt add_ofNat toNat_add_ofNat contains_off sub_off
  disj_off InRegions.of_mem)

/-! ## What a call of `vg_scrypt_blockmix` does -/

/-- A call of `c`, in a frame of its arguments pushed from `esi`, `ecx`,
`edx`, `ecx` and `eax`, writes scryptBlockMix of the `128 r` bytes at `esi`
to `edx`, with the 128 bytes at `eax` as working space, using the 36 bytes
below `esp`. -/
def BlockMixSpec (c : Prog isa) : Prop :=
  ∀ (s : State) (src dst scr : BitVec 32) (r : Nat), s.gpr .esi = src →
    s.gpr .ecx = BitVec.ofNat 32 r → s.gpr .edx = dst → s.gpr .eax = scr → 0 < r → 128 * r < 2 ^ 32 →
    Region.Disjoint ⟨dst.setWidth 64, 128 * r⟩ ⟨scr.setWidth 64, 128⟩ →
    Region.Disjoint ⟨src.setWidth 64, 128 * r⟩ ⟨dst.setWidth 64, 128 * r⟩ →
    Region.Disjoint ⟨src.setWidth 64, 128 * r⟩ ⟨scr.setWidth 64, 128⟩ →
    src.toNat + 128 * r ≤ 2 ^ 32 → dst.toNat + 128 * r ≤ 2 ^ 32 → scr.toNat + 128 ≤ 2 ^ 32 →
    36 ≤ (s.gpr .esp).toNat →
    (below (s.gpr .esp) 36).Disjoint ⟨src.setWidth 64, 128 * r⟩ →
    (below (s.gpr .esp) 36).Disjoint ⟨dst.setWidth 64, 128 * r⟩ →
    (below (s.gpr .esp) 36).Disjoint ⟨scr.setWidth 64, 128⟩ →
    InRegions (s.rd ++ s.wr) (src.setWidth 64) (128 * r) → InRegions s.wr (dst.setWidth 64) (128 * r) →
    InRegions s.wr (scr.setWidth 64) 128 →
    ∀ Q : State → Prop, (∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
        Frame [⟨dst.setWidth 64, 128 * r⟩, ⟨scr.setWidth 64, 128⟩, below (s.gpr .esp) 36] s.mem s'.mem →
        bytesAt s'.mem (dst.setWidth 64) (128 * r) =
          blockMix r (bytesAt s.mem (src.setWidth 64) (128 * r)) → Q s') →
    WP isa (.frame (.push [.eax, .ecx, .edx, .ecx, .esi]) (.call "vg_scrypt_blockmix" c) (.pop .eax 5)) s Q

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev esp₀ : BitVec 32 := s₀.gpr .esp
abbrev bP : BitVec 32 := arg s₀ 0
abbrev rr : Nat := (arg s₀ 1).toNat
abbrev vP : BitVec 32 := arg s₀ 2
abbrev vl : Nat := (arg s₀ 3).toNat
abbrev sc : BitVec 32 := arg s₀ 4
/-- `N`. -/
abbrev NN : Nat := vl s₀ / rr s₀
abbrev bA : Addr := (bP s₀).setWidth 64
abbrev vA : Addr := (vP s₀).setWidth 64
abbrev scA : Addr := (sc s₀).setWidth 64
abbrev bR : Region := ⟨bA s₀, rr s₀ * 128⟩
abbrev vR : Region := ⟨vA s₀, vl s₀ * 128⟩
abbrev scR : Region := ⟨scA s₀, (rr s₀ + 2) * 128⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 24⟩
abbrev retR : Region := ⟨(esp₀ s₀).setWidth 64, 4⟩
/-- The stack the calls use. -/
abbrev stkR : Region := below (esp₀ s₀) 36
/-- The input. -/
abbrev B : List Byte := bytesAt s₀.mem (bA s₀) (128 * rr s₀)
/-- `(V[i]'(by omega_arith))`. -/
abbrev vAt (i : Nat) : Addr := vA s₀ + BitVec.ofNat 64 (128 * rr s₀ * i)
/-- `(V[i]'(by omega_arith))`, as the pointer the code computes. -/
abbrev vAt32 (i : Nat) : BitVec 32 := vP s₀ + BitVec.ofNat 32 (128 * rr s₀ * i)
/-- `T`. -/
abbrev tP : Addr := scA s₀ + BitVec.ofNat 64 192
abbrev tP32 : BitVec 32 := sc s₀ + BitVec.ofNat 32 192

/-- Our caller's `ebx`, `esi`, `edi` and `ebp` are saved in the scratch space. -/
abbrev Saved (m : Mem) : Prop := Spill.Saved m (scA s₀ + BitVec.ofNat 64 ·) s₀.gpr rmSaved

/-- The regions the function writes, and the stack its calls use. -/
abbrev frs : List Region := [bR s₀, vR s₀, scR s₀, stkR s₀]

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [argR s₀]
  wr : s₀.wr = [bR s₀, vR s₀, scR s₀]
  b_v : (bR s₀).Disjoint (vR s₀)
  b_s : (bR s₀).Disjoint (scR s₀)
  v_s : (vR s₀).Disjoint (scR s₀)
  a_b : (argR s₀).Disjoint (bR s₀)
  a_v : (argR s₀).Disjoint (vR s₀)
  a_s : (argR s₀).Disjoint (scR s₀)
  ret_b : (retR s₀).Disjoint (bR s₀)
  ret_v : (retR s₀).Disjoint (vR s₀)
  ret_s : (retR s₀).Disjoint (scR s₀)
  stk_b : (stkR s₀).Disjoint (bR s₀)
  stk_v : (stkR s₀).Disjoint (vR s₀)
  stk_s : (stkR s₀).Disjoint (scR s₀)
  b_nw : (bP s₀).toNat + rr s₀ * 128 ≤ 2 ^ 32
  v_nw : (vP s₀).toNat + vl s₀ * 128 ≤ 2 ^ 32
  s_nw : (sc s₀).toNat + (rr s₀ + 2) * 128 ≤ 2 ^ 32
  sp_lo : 36 ≤ (esp₀ s₀).toNat
  sp_fit : (esp₀ s₀).toNat + 28 ≤ 2 ^ 32
  pos : 0 < rr s₀
  vl_eq : vl s₀ = rr s₀ * NN s₀
  pow : (NN s₀).isPowerOfTwo

/-- The 36 bytes of stack below `E`, as the contracts write them. -/
theorem stk_eq {E : BitVec 32} (h : 36 ≤ E.toNat) : below E 36 = ⟨E.setWidth 64 - 36, 36⟩ := by
  simp only [below]; rw [Taint.sub_setWidth h]; rfl

theorem pre_of {s₀ : State} (h : Proof.Scrypt.roMixX86.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23⟩ := h
  have e := stk_eq h18
  simp only [h23] at h2 h4 h5 h8 h11 h14 h17
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, by rw [stkR, e]; exact h12,
    by rw [stkR, e]; exact h13, by rw [stkR, e]; exact h14, h15, h16, h17, h18, h19, h20, ?_, h22⟩
  exact (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h21)).symm

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem NN_pos : 0 < NN s₀ := by
  obtain ⟨e, he⟩ := hp.pow
  rw [he]; exact Nat.two_pow_pos _

theorem vl_mul : vl s₀ * 128 = 128 * rr s₀ * NN s₀ := by
  rw [hp.vl_eq, Nat.mul_comm, ← Nat.mul_assoc]

/-- `v` is not the whole address space, since `scratch` is not in it. -/
theorem v_lt : 128 * rr s₀ * NN s₀ < 2 ^ 32 := by
  rw [← vl_mul hp]
  by_contra hc
  have hv : vA s₀ = 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [addr_toNat]; show _ = 0; have := hp.v_nw; omega_arith
  have hs : (scA s₀).toNat < 2 ^ 32 := by rw [addr_toNat]; exact (sc s₀).isLt
  refine hp.v_s (scA s₀) ?_ ?_
  · show (scA s₀ - vA s₀).toNat + 1 ≤ vl s₀ * 128
    rw [hv, show (0 : Addr) = 0#64 from rfl, BitVec.sub_zero]; omega_arith
  · show (scA s₀ - scA s₀).toNat + 1 ≤ (rr s₀ + 2) * 128
    rw [BitVec.sub_self, BitVec.toNat_zero]; omega_arith

theorem r_lt : 128 * rr s₀ < 2 ^ 32 := by
  have := v_lt hp
  have := NN_pos hp
  have : 128 * rr s₀ ≤ 128 * rr s₀ * NN s₀ := Nat.le_mul_of_pos_right _ (by omega_arith)
  omega_arith

theorem NN_lt : NN s₀ < 2 ^ 32 := by
  have := v_lt hp
  have : NN s₀ ≤ 128 * rr s₀ * NN s₀ := Nat.le_mul_of_pos_left _ (by have := hp.pos; omega_arith)
  omega_arith

omit hp in
theorem v_le {i : Nat} (hi : i < NN s₀) : 128 * rr s₀ * i + 128 * rr s₀ ≤ 128 * rr s₀ * NN s₀ := by
  rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi

/-- `(V[i]'(by omega_arith))` is in `v`. -/
theorem vAt_sub {i : Nat} (hi : i < NN s₀) : Region.Sub ⟨vAt s₀ i, 128 * rr s₀⟩ (vR s₀) := by
  have := v_lt hp
  have := v_le hi
  show Region.Sub ⟨vA s₀ + BitVec.ofNat 64 (128 * rr s₀ * i), 128 * rr s₀⟩ ⟨vA s₀, vl s₀ * 128⟩
  exact sub_off (by rw [vl_mul hp]; omega_arith) (by omega_arith)

theorem vAt_disj {i k : Nat} (hi : i < NN s₀) (hk : k < NN s₀) (hik : i ≠ k) :
    Region.Disjoint ⟨vAt s₀ i, 128 * rr s₀⟩ ⟨vAt s₀ k, 128 * rr s₀⟩ := by
  have := v_lt hp
  have h1 := v_le hi
  have h2 := v_le hk
  refine disj_off _ ?_ (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
  rcases Nat.lt_or_gt_of_ne hik with h | h
  · left; rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h
  · right; rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h

/-- `(V[i]'(by omega_arith))` as an address. -/
theorem vAt_addr {i : Nat} (hi : i < NN s₀) : (vAt32 s₀ i).setWidth 64 = vAt s₀ i := by
  have := v_lt hp
  have := v_le hi
  have := hp.v_nw
  have := vl_mul hp
  have := hp.pos
  exact addr_add (by omega_arith)

theorem vAt_nw {i : Nat} (hi : i < NN s₀) : (vAt32 s₀ i).toNat + 128 * rr s₀ ≤ 2 ^ 32 := by
  have := v_lt hp
  have := v_le hi
  have := hp.v_nw
  have := vl_mul hp
  have := hp.pos
  rw [toNat_add32 (by omega_arith)]
  omega_arith

/-- `T` is in `scratch`. -/
theorem t_sub : Region.Sub ⟨tP s₀, 128 * rr s₀⟩ (scR s₀) := by
  have := hp.s_nw
  exact sub_off (by omega_arith) (by omega_arith)

theorem t_addr : (tP32 s₀).setWidth 64 = tP s₀ := addr_add (by have := hp.s_nw; omega_arith)

theorem t_nw : (tP32 s₀).toNat + 128 * rr s₀ ≤ 2 ^ 32 := by
  have := hp.s_nw
  rw [toNat_add32 (by omega_arith)]
  omega_arith

omit hp in
/-- The block-mix working space is in `scratch`. -/
theorem w_sub : Region.Sub ⟨scA s₀, 128⟩ (scR s₀) := Region.sub_prefix (by omega_arith)

theorem t_w : Region.Disjoint ⟨tP s₀, 128 * rr s₀⟩ ⟨scA s₀, 128⟩ := by
  have := hp.s_nw
  have := hp.pos
  have := disj_off (scA s₀) (o₁ := 192) (n₁ := 128 * rr s₀) (o₂ := 0) (n₂ := 128) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
  simpa using this

/-- The argument words are in the arguments' region. -/
theorem arg_sub {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 28) :
    Region.Sub ⟨addr (esp₀ s₀) d, 4⟩ (argR s₀) := by
  have := hp.sp_fit
  intro a ha
  simp only [Region.Contains, argAddr] at ha ⊢
  rw [addr_eq (by omega_arith)] at ha
  rw [show (esp₀ s₀ + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 = addr (esp₀ s₀) 4 from rfl,
    addr_eq (by omega_arith)]
  generalize (esp₀ s₀).setWidth 64 = b at *
  bv_omega

theorem arg_in {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 28) :
    InRegions (s₀.rd ++ s₀.wr) (addr (esp₀ s₀) d) 4 := by
  have hs := hp.sp_fit
  refine ⟨argR s₀, by simp [hp.rd], ?_⟩
  show (addr (esp₀ s₀) d - addr (esp₀ s₀) 4).toNat + 4 ≤ 24
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
  have hE : ((esp₀ s₀).setWidth 64).toNat = (esp₀ s₀).toNat := addr_toNat _
  generalize (esp₀ s₀).setWidth 64 = b at *
  bv_omega

theorem ret_stk : (retR s₀).Disjoint (stkR s₀) := by
  have := hp.sp_fit; have := hp.sp_lo
  intro a h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  rw [Taint.sub_setWidth (by omega_arith)] at h₂
  have hE : ((esp₀ s₀).setWidth 64).toNat = (esp₀ s₀).toNat := addr_toNat _
  generalize (esp₀ s₀).setWidth 64 = b at *
  bv_omega

/-- The arguments are kept by anything that writes only our regions and the
stack below `esp`. -/
theorem arg_keep {m : Mem} (hf : Frame (frs s₀) s₀.mem m) {d : Nat} (hd₁ : 4 ≤ d)
    (hd : d + 4 ≤ 28) : m.readW (addr (esp₀ s₀) d) 32 = s₀.mem.readW (addr (esp₀ s₀) d) 32 := by
  refine hf.readW (r := ⟨addr (esp₀ s₀) d, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.a_b.sub_left (arg_sub hp hd₁ hd)
  · exact hp.a_v.sub_left (arg_sub hp hd₁ hd)
  · exact hp.a_s.sub_left (arg_sub hp hd₁ hd)
  · exact (stk_arg hp).symm.sub_left (arg_sub hp hd₁ hd)

/-- Argument `i`, read from memory that differs from the initial one only in
our regions and the stack below `esp`. -/
theorem arg_read {m : Mem} (hf : Frame (frs s₀) s₀.mem m) {i : Nat} (hi : i < 6) :
    m.readW (addr (esp₀ s₀) (4 + 4 * i)) 32 = arg s₀ i :=
  arg_keep hp hf (by omega_arith) (by omega_arith)

end

theorem in_s (s₀ : State) {o n : Nat} (h : o + n ≤ 256) :
    (scR s₀).Contains (scA s₀ + BitVec.ofNat 64 o) n :=
  contains_off (by omega_arith) (by omega_arith)

theorem s_sub (s₀ : State) {o n : Nat} (h : o + n ≤ 256) :
    Region.Sub ⟨scA s₀ + BitVec.ofNat 64 o, n⟩ (scR s₀) :=
  sub_off (by omega_arith) (by omega_arith)

/-! ## What stays in `scratch`: our caller's registers -/

/-- Bytes `[128, 192)` of `scratch`. -/
abbrev keepR (s₀ : State) : Region := ⟨scA s₀ + BitVec.ofNat 64 128, 64⟩

theorem word_sub (s₀ : State) {d : Nat} (h₁ : 128 ≤ d) (h₂ : d + 4 ≤ 192) :
    Region.Sub ⟨scA s₀ + BitVec.ofNat 64 d, 4⟩ (keepR s₀) := by
  rw [show d = 128 + (d - 128) by omega_arith, ← add_ofNat]
  exact sub_off (by omega_arith) (by omega_arith)

theorem saved_offs : ∀ p ∈ rmSaved, 128 ≤ p.2 ∧ p.2 + 4 ≤ 144 ∧ p.1 ≠ .eax := by decide

theorem Saved.frame {s₀ : State} {m m' : Mem} {rs : List Region} (h : Saved s₀ m) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (keepR s₀).Disjoint r) : Saved s₀ m' := by
  intro p hp
  have ho := saved_offs p hp
  rw [← h p hp]
  exact hf.readW (r := ⟨scA s₀ + BitVec.ofNat 64 p.2, 4⟩) (Region.contains_self _ _)
    (fun r hr => (hd r hr).sub_left (word_sub s₀ ho.1 (by omega))) (by decide)

theorem keep_sub (s₀ : State) : Region.Sub (keepR s₀) (scR s₀) := s_sub s₀ (by omega_arith)

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem keep_b : (keepR s₀).Disjoint (bR s₀) := hp.b_s.symm.sub_left (keep_sub s₀)
theorem keep_v : (keepR s₀).Disjoint (vR s₀) := hp.v_s.symm.sub_left (keep_sub s₀)
theorem keep_stk : (keepR s₀).Disjoint (stkR s₀) := hp.stk_s.symm.sub_left (keep_sub s₀)

omit hp in
theorem keep_w : (keepR s₀).Disjoint ⟨scA s₀, 128⟩ := by
  have := disj_off (scA s₀) (o₁ := 128) (n₁ := 64) (o₂ := 0) (n₂ := 128) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
  simpa using this

theorem keep_t : (keepR s₀).Disjoint ⟨tP s₀, 128 * rr s₀⟩ := by
  have := hp.s_nw
  have := hp.pos
  exact disj_off (scA s₀) (o₁ := 128) (n₁ := 64) (o₂ := 192) (n₂ := 128 * rr s₀) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)

omit hp in
theorem b_sub' : Region.Sub ⟨bA s₀, 128 * rr s₀⟩ (bR s₀) := by
  rw [Nat.mul_comm]; exact fun _ h => h

end

/-! ## `Integerify`, from a 32-bit word -/

theorem leNat_bytesAt32_mod (m : Mem) (a : Addr) {e : Nat} (he : e ≤ 32) :
    leNat (bytesAt m a 64) % 2 ^ e = (m.readW a 32).toNat % 2 ^ e := by
  rw [show (64 : Nat) = 4 + 60 from rfl, bytesAt_add', leNat_append, bytesAt_length',
    show (256 : Nat) ^ 4 = 2 ^ e * 2 ^ (32 - e) by rw [← Nat.pow_add, Nat.add_sub_cancel' he],
    Nat.mul_assoc, Nat.add_mul_mod_self_left, leNat_bytesAt]
  simp only [Mem.readW, BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (BitVec.isLt _)]

/-- `Integerify (X) mod 2^e`, for `e ≤ 32`, is the first 4 bytes of `X`'s last
64-byte block, read little-endian, mod `2^e`. -/
theorem integerify_mod32 (m : Mem) (p : Addr) {r e : Nat} (hr : 0 < r) (he : e ≤ 32) :
    integerify r (bytesAt m p (128 * r)) % 2 ^ e =
      (m.readW (p + BitVec.ofNat 64 (128 * r - 64)) 32).toNat % 2 ^ e := by
  rw [integerify, blk_bytesAt' _ _ (by omega_arith), show 64 * (2 * r - 1) = 128 * r - 64 by omega_arith,
    leNat_bytesAt32_mod _ _ he]

theorem and_mask32 (w : BitVec 32) {e : Nat} (he : e ≤ 32) :
    (w &&& BitVec.ofNat 32 (2 ^ e - 1)).toNat = w.toNat % 2 ^ e := by
  have := Nat.pow_le_pow_right (by omega_arith : 0 < 2) he
  have := Nat.one_le_two_pow (n := e)
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith),
    Nat.and_two_pow_sub_one_eq_mod]

theorem shr_ofNat32 {a : Nat} (n : Nat) (h : a < 2 ^ 32) :
    BitVec.ofNat 32 a >>> n = BitVec.ofNat 32 (a / 2 ^ n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h), Nat.shiftRight_eq_div_pow]

end VG.Proof.Scrypt.X86.RoMix

end

section

/-!
# scryptROMix on x86 (32-bit): the small loops

The copy (`copyLoop`) and exclusive-or (`xorLoop`) of 16-byte blocks and the
computation of `2 N` by doubling (`nLoop`), as on 32-bit ARM
(`Proof/Scrypt/Arm/RoMixCT.lean`). Words are 4 bytes, and pointers 32 bits,
which address memory by their zero extensions.
-/

namespace VG.Proof.Scrypt.X86.RoMix

open VG VG.X86 VG.Impl.Scrypt.X86
open VG.Spec.Scrypt (bytesAt)
open VG.Spec.Pbkdf2 (xorBytes)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil)
open VG.Proof.Sha256.X86.Stream (Upd Mupd Fupd wp_mov wp_movm wp_store wp_add wp_addi wp_subi wp_cmp
  ofNat_beq_zero sub_beq)

/-! ## Arithmetic -/

/-- A pointer advanced by one 16-byte block. -/
theorem next16 (p : BitVec 32) (k : Nat) :
    p + BitVec.ofNat 32 (16 * k) + 16 = p + BitVec.ofNat 32 (16 * (k + 1)) := by
  rw [add32_lit, Nat.mul_succ]

theorem ofNat_zero_add16 (p : BitVec 32) : p + BitVec.ofNat 32 (16 * 0) = p := by
  rw [Nat.mul_zero]; exact BitVec.add_zero _

/-- A 16-byte block of a region, as an address. -/
theorem block_addr {p : BitVec 32} {n k : Nat} (hp : p.toNat + 16 * n ≤ 2 ^ 32) (hk : k < n) :
    addr (p + BitVec.ofNat 32 (16 * k)) 0 = p.setWidth 64 + BitVec.ofNat 64 (16 * k) := by
  rw [addr_zero, addr_add (by omega_arith)]

/-! ## `copyLoop` -/

/-- After `k` blocks of `copyLoop`. -/
structure CopyInv (s : State) (src dst : BitVec 32) (n k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  other : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → t.gpr r = s.gpr r
  eax : t.gpr .eax = src + BitVec.ofNat 32 (16 * k)
  ecx : t.gpr .ecx = dst + BitVec.ofNat 32 (16 * k)
  edx : t.gpr .edx = BitVec.ofNat 32 (n - k)
  mem : t.mem = writeBytes s.mem (dst.setWidth 64) (bytesAt s.mem (src.setWidth 64) (16 * k))

theorem copy_step {s : State} {src dst : BitVec 32} {n : Nat} (hn : n < 2 ^ 32)
    (fs : src.toNat + 16 * n ≤ 2 ^ 32) (fd : dst.toNat + 16 * n ≤ 2 ^ 32)
    (hin : ∀ k < n, InRegions (s.rd ++ s.wr) (src.setWidth 64 + BitVec.ofNat 64 (16 * k)) 16)
    (hout : ∀ k < n, InRegions s.wr (dst.setWidth 64 + BitVec.ofNat 64 (16 * k)) 16)
    (hsep : Region.Disjoint ⟨src.setWidth 64, 16 * n⟩ ⟨dst.setWidth 64, 16 * n⟩) {k : Nat} (hk : k < n)
    {t : State} (h : CopyInv s src dst n k t) :
    WP isa (.block [.movdquLoad .xmm0 (at_ .eax 0), .movdquStore (at_ .ecx 0) .xmm0,
      .alu .add .eax (.imm 16), .alu .add .ecx (.imm 16), .alu .sub .edx (.imm 1)]) t
      fun t' => CopyInv s src dst n (k + 1) t' ∧ t'.zf = some (decide (k + 1 = n)) := by
  refine wp_ldq (a := src.setWidth 64 + BitVec.ofNat 64 (16 * k))
    (by rw [ea_at, h.eax, block_addr fs hk]) (by rw [h.rd, h.wr]; exact hin k hk) fun t₁ R₁ m₁ x₁ _ => ?_
  refine wp_stq (a := dst.setWidth 64 + BitVec.ofNat 64 (16 * k))
    (by rw [ea_at, R₁.gpr, h.ecx, block_addr fd hk])
    (by rw [R₁.wr, h.wr]; exact hout k hk) fun t₂ R₂ m₂ _ => ?_
  refine wp_addi fun t₃ u₃ => wp_addi fun t₄ u₄ => wp_subi fun t₅ u₅ z₅ => WP.block_nil ?_
  have g : t₂.gpr = t.gpr := by rw [R₂.gpr, R₁.gpr]
  have e2 : t₄.gpr .edx = BitVec.ofNat 32 (n - k) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), g, h.edx]
  refine ⟨⟨by rw [u₅.rd, u₄.rd, u₃.rd, R₂.rd, R₁.rd, h.rd],
    by rw [u₅.wr, u₄.wr, u₃.wr, R₂.wr, R₁.wr, h.wr], fun r h0 h1 h2 h3 => ?_, ?_, ?_,
    by rw [u₅.gpr, e2, dec_count hk], ?_⟩, by rw [z₅, e2, dec_z hk hn]⟩
  · rw [u₅.other r h2, u₄.other r h1, u₃.other r h0, g, h.other r h0 h1 h2 h3]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g, h.eax, next16]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g, h.ecx, next16]
  · rw [u₅.mem, u₄.mem, u₃.mem, m₂, x₁, m₁, h.mem, Nat.mul_succ]
    exact Proof.Scrypt.Memory.copy_mem s.mem _ _ k 16
      (hsep.sep (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_arith)
        (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_arith)) (by omega_arith)

/-- `copyLoop` copies `16 n` bytes from `eax` to `ecx` (`edx = n > 0` blocks). -/
theorem copyLoop_ok {s : State} {src dst : BitVec 32} {n : Nat} (hn : 0 < n) (hlt : n < 2 ^ 32)
    (fs : src.toNat + 16 * n ≤ 2 ^ 32) (fd : dst.toNat + 16 * n ≤ 2 ^ 32)
    (h0 : s.gpr .eax = src) (h1 : s.gpr .ecx = dst) (h2 : s.gpr .edx = BitVec.ofNat 32 n)
    (hin : ∀ k < n, InRegions (s.rd ++ s.wr) (src.setWidth 64 + BitVec.ofNat 64 (16 * k)) 16)
    (hout : ∀ k < n, InRegions s.wr (dst.setWidth 64 + BitVec.ofNat 64 (16 * k)) 16)
    (hsep : Region.Disjoint ⟨src.setWidth 64, 16 * n⟩ ⟨dst.setWidth 64, 16 * n⟩) :
    WP isa copyLoop s fun s' => s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → s'.gpr r = s.gpr r) ∧
      s'.mem = writeBytes s.mem (dst.setWidth 64) (bytesAt s.mem (src.setWidth 64) (16 * n)) := by
  refine WP.mono (count_loop hn (CopyInv s src dst n)
    (fun k hk t h => copy_step hlt fs fd hin hout hsep hk h) ?_)
    fun t h => ⟨h.rd, h.wr, h.other, h.mem⟩
  exact ⟨rfl, rfl, fun _ _ _ _ _ => rfl, by rw [ofNat_zero_add16, h0],
    by rw [ofNat_zero_add16, h1], by rw [h2, Nat.sub_zero],
    by rw [Nat.mul_zero]; exact (writeBytes_nil _ _).symm⟩

/-! ## `xorLoop` -/

/-- After `k` blocks of `xorLoop`. -/
structure XorInv (s : State) (x y d : BitVec 32) (n k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  other : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → r ≠ .esi → t.gpr r = s.gpr r
  eax : t.gpr .eax = x + BitVec.ofNat 32 (16 * k)
  ecx : t.gpr .ecx = y + BitVec.ofNat 32 (16 * k)
  edx : t.gpr .edx = d + BitVec.ofNat 32 (16 * k)
  edi : t.gpr .edi = BitVec.ofNat 32 (n - k)
  mem : t.mem = writeBytes s.mem (d.setWidth 64)
    (xorBytes (bytesAt s.mem (x.setWidth 64) (16 * k)) (bytesAt s.mem (y.setWidth 64) (16 * k)))

theorem xor_step {s : State} {x y d : BitVec 32} {n : Nat} (hn : n < 2 ^ 32)
    (fx : x.toNat + 16 * n ≤ 2 ^ 32) (fy : y.toNat + 16 * n ≤ 2 ^ 32) (fd : d.toNat + 16 * n ≤ 2 ^ 32)
    (hinx : ∀ k < n, InRegions (s.rd ++ s.wr) (x.setWidth 64 + BitVec.ofNat 64 (16 * k)) 16)
    (hiny : ∀ k < n, InRegions (s.rd ++ s.wr) (y.setWidth 64 + BitVec.ofNat 64 (16 * k)) 16)
    (hout : ∀ k < n, InRegions s.wr (d.setWidth 64 + BitVec.ofNat 64 (16 * k)) 16)
    (hdx : Region.Disjoint ⟨d.setWidth 64, 16 * n⟩ ⟨x.setWidth 64, 16 * n⟩)
    (hdy : Region.Disjoint ⟨d.setWidth 64, 16 * n⟩ ⟨y.setWidth 64, 16 * n⟩)
    {k : Nat} (hk : k < n) {t : State} (h : XorInv s x y d n k t) :
    WP isa (.block [.movdquLoad .xmm0 (at_ .eax 0), .movdquLoad .xmm1 (at_ .ecx 0), xb .pxor .xmm0 .xmm1,
      .movdquStore (at_ .edx 0) .xmm0, .alu .add .eax (.imm 16), .alu .add .ecx (.imm 16),
      .alu .add .edx (.imm 16), .alu .sub .edi (.imm 1)]) t
      fun t' => XorInv s x y d n (k + 1) t' ∧ t'.zf = some (decide (k + 1 = n)) := by
  refine wp_ldq (a := x.setWidth 64 + BitVec.ofNat 64 (16 * k))
    (by rw [ea_at, h.eax, block_addr fx hk]) (by rw [h.rd, h.wr]; exact hinx k hk) fun t₁ R₁ m₁ x₁ _ => ?_
  refine wp_ldq (a := y.setWidth 64 + BitVec.ofNat 64 (16 * k))
    (by rw [ea_at, R₁.gpr, h.ecx, block_addr fy hk])
    (by rw [R₁.rd, R₁.wr, h.rd, h.wr]; exact hiny k hk) fun t₂ R₂ m₂ x₂ o₂ => ?_
  refine wp_xbin fun t₃ R₃ m₃ x₃ _ => ?_
  refine wp_stq (a := d.setWidth 64 + BitVec.ofNat 64 (16 * k))
    (by rw [ea_at, R₃.gpr, R₂.gpr, R₁.gpr, h.edx, block_addr fd hk])
    (by rw [R₃.wr, R₂.wr, R₁.wr, h.wr]; exact hout k hk) fun t₄ R₄ m₄ _ => ?_
  refine wp_addi fun t₅ u₅ => wp_addi fun t₆ u₆ => wp_addi fun t₇ u₇ => wp_subi fun t₈ u₈ z₈ =>
    WP.block_nil ?_
  have g : t₄.gpr = t.gpr := by rw [R₄.gpr, R₃.gpr, R₂.gpr, R₁.gpr]
  have e7 : t₇.gpr .edi = BitVec.ofNat 32 (n - k) := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), g, h.edi]
  refine ⟨⟨by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, R₄.rd, R₃.rd, R₂.rd, R₁.rd, h.rd],
    by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, R₄.wr, R₃.wr, R₂.wr, R₁.wr, h.wr],
    fun r h0 h1 h2 h3 h4 => ?_, ?_, ?_, ?_, by rw [u₈.gpr, e7, dec_count hk], ?_⟩,
    by rw [z₈, e7, dec_z hk hn]⟩
  · rw [u₈.other r h3, u₇.other r h2, u₆.other r h1, u₅.other r h0, g, h.other r h0 h1 h2 h3 h4]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, g, h.eax, next16]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), g, h.ecx, next16]
  · rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), g, h.edx, next16]
  · rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, m₄, x₃, o₂ .xmm0 (by decide), x₁, x₂, m₃, m₂, m₁, h.mem]
    exact xor_mem16 s.mem hk (by omega_arith) hdx hdy

/-- `xorLoop` writes `[eax] xor [ecx]` to `edx`, `16 n` bytes (`edi = n > 0` blocks). -/
theorem xorLoop_ok {s : State} {x y d : BitVec 32} {n : Nat} (hn : 0 < n) (hlt : n < 2 ^ 32)
    (fx : x.toNat + 16 * n ≤ 2 ^ 32) (fy : y.toNat + 16 * n ≤ 2 ^ 32) (fd : d.toNat + 16 * n ≤ 2 ^ 32)
    (h0 : s.gpr .eax = x) (h1 : s.gpr .ecx = y) (h2 : s.gpr .edx = d)
    (h3 : s.gpr .edi = BitVec.ofNat 32 n)
    (hinx : ∀ k < n, InRegions (s.rd ++ s.wr) (x.setWidth 64 + BitVec.ofNat 64 (16 * k)) 16)
    (hiny : ∀ k < n, InRegions (s.rd ++ s.wr) (y.setWidth 64 + BitVec.ofNat 64 (16 * k)) 16)
    (hout : ∀ k < n, InRegions s.wr (d.setWidth 64 + BitVec.ofNat 64 (16 * k)) 16)
    (hdx : Region.Disjoint ⟨d.setWidth 64, 16 * n⟩ ⟨x.setWidth 64, 16 * n⟩)
    (hdy : Region.Disjoint ⟨d.setWidth 64, 16 * n⟩ ⟨y.setWidth 64, 16 * n⟩) :
    WP isa xorLoop s fun s' => s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → r ≠ .esi → s'.gpr r = s.gpr r) ∧
      s'.mem = writeBytes s.mem (d.setWidth 64)
        (xorBytes (bytesAt s.mem (x.setWidth 64) (16 * n)) (bytesAt s.mem (y.setWidth 64) (16 * n))) := by
  refine WP.mono (count_loop hn (XorInv s x y d n)
    (fun k hk t h => xor_step hlt fx fy fd hinx hiny hout hdx hdy hk h) ?_)
    fun t h => ⟨h.rd, h.wr, h.other, h.mem⟩
  exact ⟨rfl, rfl, fun _ _ _ _ _ _ => rfl, by rw [ofNat_zero_add16, h0],
    by rw [ofNat_zero_add16, h1], by rw [ofNat_zero_add16, h2], by rw [h3, Nat.sub_zero],
    by rw [Nat.mul_zero]; exact (writeBytes_nil _ _).symm⟩

/-! ## `nLoop` -/

/-- After `k` doublings. -/
structure NInv (s : State) (r : Nat) (k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : t.mem = s.mem
  other : ∀ r', r' ≠ .eax → r' ≠ .ecx → t.gpr r' = s.gpr r'
  eax : t.gpr .eax = BitVec.ofNat 32 (r * 2 ^ k)
  ecx : t.gpr .ecx = BitVec.ofNat 32 (2 ^ k)

theorem dbl_pow32 (x k : Nat) : BitVec.ofNat 32 (x * 2 ^ k) + BitVec.ofNat 32 (x * 2 ^ k) =
    BitVec.ofNat 32 (x * 2 ^ (k + 1)) := by
  rw [← BitVec.ofNat_add, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_two]

theorem n_step {s : State} {r e : Nat} (hr : 0 < r) (hlt : r * 2 ^ (e + 1) < 2 ^ 32)
    (h2 : s.gpr .edx = BitVec.ofNat 32 (r * 2 ^ (e + 1))) {k : Nat} (hk : k < e + 1) {t : State}
    (h : NInv s r k t) :
    WP isa (.block [.alu .add .eax (.reg .eax), .alu .add .ecx (.reg .ecx), .alu .cmp .eax (.reg .edx)]) t
      fun t' => NInv s r (k + 1) t' ∧ t'.zf = some (decide (k + 1 = e + 1)) := by
  refine wp_add fun t₁ u₁ => wp_add fun t₂ u₂ => wp_cmp fun t₃ f₃ _ z₃ => WP.block_nil ?_
  have ax : t₂.gpr .eax = BitVec.ofNat 32 (r * 2 ^ (k + 1)) := by
    rw [u₂.other _ (by decide), u₁.gpr, h.eax, dbl_pow32]
  have le : r * 2 ^ (k + 1) ≤ r * 2 ^ (e + 1) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega_arith))
  refine ⟨⟨by rw [f₃.rd, u₂.rd, u₁.rd, h.rd], by rw [f₃.wr, u₂.wr, u₁.wr, h.wr],
    by rw [f₃.mem, u₂.mem, u₁.mem, h.mem], fun r' h0 h1 => ?_, by rw [f₃.gpr, ax], ?_⟩, ?_⟩
  · rw [f₃.gpr, u₂.other r' h1, u₁.other r' h0, h.other r' h0 h1]
  · rw [f₃.gpr, u₂.gpr, u₁.other _ (by decide), h.ecx, ← Nat.one_mul (2 ^ k), dbl_pow32, Nat.one_mul]
  · rw [z₃, ax, u₂.other _ (by decide), u₁.other _ (by decide),
      h.other _ (by decide) (by decide), h2, sub_beq (by omega_arith) hlt]
    by_cases hh : k + 1 = e + 1
    · simp [hh]
    · have : r * 2 ^ (k + 1) ≠ r * 2 ^ (e + 1) := fun h' =>
        hh ((Nat.pow_right_inj (by decide)).mp (Nat.eq_of_mul_eq_mul_left hr h'))
      simp only [this, decide_false, hh]

/-- `nLoop` doubles `eax` (from `r`) and `ecx` (from 1) until `eax = edx = r * 2^(e+1)`. -/
theorem nLoop_ok {s : State} {r e : Nat} (hr : 0 < r) (hlt : r * 2 ^ (e + 1) < 2 ^ 32)
    (h0 : s.gpr .eax = BitVec.ofNat 32 r) (h1 : s.gpr .ecx = 1)
    (h2 : s.gpr .edx = BitVec.ofNat 32 (r * 2 ^ (e + 1))) :
    WP isa nLoop s fun s' => s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r', r' ≠ .eax → r' ≠ .ecx → s'.gpr r' = s.gpr r') ∧
      s'.gpr .ecx = BitVec.ofNat 32 (2 ^ (e + 1)) := by
  refine WP.mono (count_loop (Nat.succ_pos e) (NInv s r)
    (fun k hk t h => n_step hr hlt h2 hk h) ?_) fun t h => ⟨h.rd, h.wr, h.mem, h.other, h.ecx⟩
  exact ⟨rfl, rfl, rfl, fun _ _ _ => rfl, by rw [h0, Nat.pow_zero, Nat.mul_one],
    by rw [h1]; rfl⟩

end VG.Proof.Scrypt.X86.RoMix

end

/-!
# scryptROMix on x86 (32-bit): correctness

The prologue saves our caller's registers in `scratch`; `N` is computed by
doubling; step 2 and step 3 are loops whose bodies call `vg_scrypt_blockmix`
(through `BlockMixSpec`) in a frame of its arguments; the epilogue restores
the registers. As on 32-bit ARM (`Proof/Scrypt/Arm/RoMixCT.lean`), with the
pointers and `r` read from the arguments when needed.
-/

namespace VG.Proof.Scrypt.X86.RoMix

open VG VG.X86 VG.Impl.Scrypt.X86
open VG.Spec.Scrypt (bytesAt blockMix roMix)
open VG.Proof.Sha256.Stream (writeBytes)
open VG.Proof.Sha256.X86.Stream (Upd Mupd wp_mov wp_movi wp_movm wp_add wp_addi wp_subi wp_shr)
open VG.Proof.Scrypt (vList vList_getD roMix_eq roMixIndices_eq mixLoop_succ_fst mixLoop_succ_snd)
open VG.Proof.Scrypt.Memory (add_ofNat contains_off sub_off InRegions.of_mem
  InRegions.right frame_bytesAt bytesAt_writeBytes_self bytesAt_writeBytes_sep bytesAt_length
  xorBytes_length)

/-! ## The prologue -/

theorem prologue_eq : rmPrologue =
    .mov .eax (.mem (at_ .esp 20)) :: (rmSaved.map (fun p => Instr.store (at_ .eax p.2) p.1) ++
      ([.mov .eax (.mem (at_ .esp 8)), .mov .ecx (.imm 1), .mov .edx (.mem (at_ .esp 16)),
        .alu .add .edx (.reg .edx)] : List Instr)) := rfl

theorem rmSaved_fits : Spill.Fits 144 rmSaved := by decide

theorem rmSaved_addr (s₀ : State) (hp : Pre s₀) :
    ∀ p ∈ rmSaved, addr (sc s₀) p.2 = scA s₀ + BitVec.ofNat 64 p.2 :=
  Spill.addr_eq_of_fits (by have := hp.s_nw; omega_arith) rmSaved_fits

theorem save_ok {s₀ : State} (hp : Pre s₀) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s₁, (∀ r, r ≠ .eax → s₁.gpr r = s₀.gpr r) → s₁.rd = s₀.rd →
      s₁.wr = s₀.wr → Frame [scR s₀] s₀.mem s₁.mem → Saved s₀ s₁.mem → WP isa (.block rest) s₁ Q) :
    WP isa (.block (.mov .eax (.mem (at_ .esp 20)) ::
      (rmSaved.map (fun p => Instr.store (at_ .eax p.2) p.1) ++ rest))) s₀ Q := by
  have hs := hp.s_nw
  refine wp_movm (a := addr (esp₀ s₀) 20) rfl (arg_in hp (by omega_arith) (by omega_arith)) fun s₁ u₁ => ?_
  have e : s₁.gpr .eax = sc s₀ := u₁.gpr
  have ha := rmSaved_addr s₀ hp
  refine Spill.save_ok rmSaved (fun p hp' => ?_) fun s₂ u₂ => ?_
  · rw [e, u₁.wr, hp.wr, ha p hp']
    exact InRegions.of_mem (by simp) (in_s s₀ (by have := rmSaved_fits.1 p hp'; omega_arith))
  refine k s₂ (fun r hr => by rw [u₂.gpr, u₁.other r hr]) (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr]) ?_ ?_
  · rw [u₂.mem, e, u₁.mem]
    exact Spill.saveMem_frame List.mem_cons_self _ _ _ _ fun p hp' => by
      rw [ha p hp']; exact in_s s₀ (by have := rmSaved_fits.1 p hp'; omega_arith)
  · rw [u₂.mem, e, u₁.mem]
    exact (Spill.saveMem_saved_addr _ _ rmSaved_fits (by have := hp.s_nw; omega_arith)).congr ha
      fun p hp' => u₁.other _ (saved_offs p hp').2.2

/-- The memory and registers the function starts each piece with. -/
structure Base (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  esp : s.gpr .esp = esp₀ s₀
  frame : Frame (frs s₀) s₀.mem s.mem

theorem Base.arg {s₀ s : State} (hp : Pre s₀) (h : Base s₀ s) {i : Nat} (hi : i < 6) :
    s.mem.readW (addr (s.gpr .esp) (4 + 4 * i)) 32 = VG.X86.arg s₀ i := by
  rw [h.esp]; exact arg_read hp h.frame hi

theorem Base.arg_in {s₀ s : State} (hp : Pre s₀) (h : Base s₀ s) {i : Nat} (hi : i < 6) :
    InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) (4 + 4 * i)) 4 := by
  rw [h.esp, h.rd, h.wr]; exact RoMix.arg_in hp (by omega_arith) (by omega_arith)

/-- A `mov` of argument `i` into `d`. -/
theorem wp_arg {s₀ : State} (hp : Pre s₀) {s : State} (h : Base s₀ s) {d : Reg} {i : Nat} (hi : i < 6)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' d (VG.X86.arg s₀ i) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.mem (at_ .esp (4 + 4 * i))) :: is)) s Q :=
  wp_movm (by rw [ea_at]) (h.arg_in hp hi) fun s' u => k s' (by rw [← h.arg hp hi]; exact u)

theorem Base.upd {s₀ s s' : State} (h : Base s₀ s) {d : Reg} {v : BitVec 32} (u : Upd s s' d v)
    (hd : d ≠ .esp) : Base s₀ s' :=
  ⟨u.rd.trans h.rd, u.wr.trans h.wr, (u.other _ (Ne.symm hd)).trans h.esp, by rw [u.mem]; exact h.frame⟩

theorem toNat_rr (s₀ : State) : BitVec.ofNat 32 (rr s₀) = VG.X86.arg s₀ 1 :=
  (ofNat_toNat32 _).symm

/-- After the prologue. -/
structure P1 (s₀ s : State) : Prop extends Base s₀ s where
  scf : Frame [scR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem
  eax : s.gpr .eax = BitVec.ofNat 32 (rr s₀)
  ecx : s.gpr .ecx = 1
  edx : s.gpr .edx = BitVec.ofNat 32 (2 * vl s₀)

theorem dbl32 (x : BitVec 32) : x + x = BitVec.ofNat 32 (2 * x.toNat) := by
  conv_lhs => rw [ofNat_toNat32 x]
  rw [← BitVec.ofNat_add, Nat.two_mul]

theorem prologue_ok {s₀ : State} (hp : Pre s₀) : WP isa (.block rmPrologue) s₀ (P1 s₀) := by
  rw [prologue_eq]
  refine save_ok hp fun s₁ g hrd hwr hf hsv => ?_
  have b₁ : Base s₀ s₁ := ⟨hrd, hwr, g _ (by decide), hf.mono (by simp)⟩
  refine wp_arg (i := 1) hp b₁ (by omega_arith) fun a ua => ?_
  refine wp_movi fun b ub => ?_
  have bb : Base s₀ b := (b₁.upd ua (by decide)).upd ub (by decide)
  refine wp_arg (i := 3) hp bb (by omega_arith) fun c uc => wp_add fun d ud => WP.block_nil ?_
  have bc := bb.upd uc (by decide)
  refine ⟨bc.upd ud (by decide), by rw [ud.mem, uc.mem, ub.mem, ua.mem]; exact hf,
    by rw [ud.mem, uc.mem, ub.mem, ua.mem]; exact hsv, ?_, ?_, ?_⟩
  · rw [ud.other _ (by decide), uc.other _ (by decide), ub.other _ (by decide), ua.gpr, toNat_rr]
  · rw [ud.other _ (by decide), uc.other _ (by decide), ub.gpr]
  · rw [ud.gpr, uc.gpr, dbl32]

/-! ## Computing `N` -/

/-- After the loop computing `N`. -/
structure N1 (s₀ s : State) : Prop extends Base s₀ s where
  scf : Frame [scR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem
  ecx : s.gpr .ecx = BitVec.ofNat 32 (2 * NN s₀)

theorem nloop_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : P1 s₀ s) : WP isa nLoop s (N1 s₀) := by
  obtain ⟨e, he⟩ := hp.pow
  have lt := v_lt hp
  have e2 : rr s₀ * 2 ^ (e + 1) = 2 * vl s₀ := by
    rw [hp.vl_eq, he, Nat.pow_succ, Nat.mul_comm (2 ^ e) 2, Nat.mul_left_comm]
  have hNe : 2 * vl s₀ < 2 ^ 32 := by have := vl_mul hp; omega_arith
  refine WP.mono (nLoop_ok (r := rr s₀) (e := e) hp.pos (by omega_arith) h.eax h.ecx
    (by rw [h.edx, e2])) fun t ⟨rd, wr, mem, oth, r1⟩ => ?_
  exact ⟨⟨by rw [rd, h.rd], by rw [wr, h.wr], by rw [oth _ (by decide) (by decide), h.esp],
    by rw [mem]; exact h.frame⟩, by rw [mem]; exact h.scf, by rw [mem]; exact h.saved,
    by rw [r1, he, Nat.pow_succ, Nat.mul_comm]⟩

/-! ## Step 2 -/

/-- After `i` iterations of step 2. -/
structure Inv2 (s₀ : State) (i : Nat) (s : State) : Prop extends Base s₀ s where
  i_le : i ≤ NN s₀
  ebx : s.gpr .ebx = BitVec.ofNat 32 (NN s₀ - i)
  esi : s.gpr .esi = vAt32 s₀ i
  ebp : s.gpr .ebp = BitVec.ofNat 32 (NN s₀)
  saved : Saved s₀ s.mem
  x : bytesAt s.mem (bA s₀) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) i (B s₀)
  done : ∀ k < i, bytesAt s.mem (vAt s₀ k) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) k (B s₀)

theorem setup2_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : N1 s₀ s) :
    WP isa (.block rmSetup) s (Inv2 s₀ 0) := by
  have lt := v_lt hp
  have n1 := NN_pos hp
  have : 2 * NN s₀ < 2 ^ 32 := by
    have : 2 * NN s₀ ≤ 128 * rr s₀ * NN s₀ := by
      have := hp.pos
      have : 2 ≤ 128 * rr s₀ := by omega_arith
      exact Nat.mul_le_mul_right _ this
    omega_arith
  unfold rmSetup
  refine wp_shr (by decide) fun t1 u1 => wp_mov fun t2 u2 => wp_mov fun t3 u3 => ?_
  have hd : t1.gpr .ecx = BitVec.ofNat 32 (NN s₀) := by
    rw [u1.gpr, h.ecx, shr_ofNat32 _ (by omega_arith), Nat.pow_one, Nat.mul_div_cancel_left _ (by decide)]
  have b3 : Base s₀ t3 := ((h.toBase.upd u1 (by decide)).upd u2 (by decide)).upd u3 (by decide)
  refine wp_arg (i := 2) hp b3 (by omega_arith) fun t4 u4 => WP.block_nil ?_
  have hm : t4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, u1.mem]
  refine ⟨b3.upd u4 (by decide), Nat.zero_le _, ?_, ?_, ?_, by rw [hm]; exact h.saved, ?_,
    fun k hk => absurd hk (by omega_arith)⟩
  · rw [u4.other _ (by decide), u3.gpr, u2.other _ (by decide), hd, Nat.sub_zero]
  · rw [u4.gpr]; simp
  · rw [u4.other _ (by decide), u3.other _ (by decide), u2.gpr, hd]
  · rw [hm]
    refine frame_bytesAt h.scf (fun r hr => ?_) (by have := r_lt hp; omega_arith)
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.b_s.sub_left (b_sub' (s₀ := s₀))

/-! ## A call of `vg_scrypt_blockmix` into `b` -/

theorem b_in {s₀ : State} (hp : Pre s₀) : InRegions s₀.wr (bA s₀) (128 * rr s₀) := by
  rw [hp.wr]
  refine InRegions.of_mem (R := bR s₀) (by simp) ?_
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_arith

theorem w_in {s₀ : State} (hp : Pre s₀) : InRegions s₀.wr (scA s₀) 128 := by
  rw [hp.wr]
  refine InRegions.of_mem (R := scR s₀) (by simp) ?_
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_arith

/-- A block that may be the source of a call of `vg_scrypt_blockmix` into `b`. -/
structure SrcOK (s₀ : State) (A : BitVec 32) : Prop where
  b : Region.Disjoint ⟨A.setWidth 64, 128 * rr s₀⟩ ⟨bA s₀, 128 * rr s₀⟩
  w : Region.Disjoint ⟨A.setWidth 64, 128 * rr s₀⟩ ⟨scA s₀, 128⟩
  stk : (stkR s₀).Disjoint ⟨A.setWidth 64, 128 * rr s₀⟩
  nw : A.toNat + 128 * rr s₀ ≤ 2 ^ 32
  inr : InRegions (s₀.rd ++ s₀.wr) (A.setWidth 64) (128 * rr s₀)

/-- The call's memory frame: `b`, the block-mix working space and the stack. -/
abbrev cfr (s₀ : State) : List Region := [⟨bA s₀, 128 * rr s₀⟩, ⟨scA s₀, 128⟩, stkR s₀]

/-- Making the call, with its arguments set. -/
theorem bmFrame_ok {c : Prog isa} (hS : BlockMixSpec c) {s₀ : State} (hp : Pre s₀) {s : State}
    {A : BitVec 32} (hA : SrcOK s₀ A) (h : Base s₀ s) (hsi : s.gpr .esi = A)
    (hax : s.gpr .eax = sc s₀) (hcx : s.gpr .ecx = BitVec.ofNat 32 (rr s₀)) (hdx : s.gpr .edx = bP s₀)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame (cfr s₀) s.mem s'.mem →
      bytesAt s'.mem (bA s₀) (128 * rr s₀) =
        blockMix (rr s₀) (bytesAt s.mem (A.setWidth 64) (128 * rr s₀)) → Q s') :
    WP isa (.frame (.push [.eax, .ecx, .edx, .ecx, .esi]) (.call "vg_scrypt_blockmix" c) (.pop .eax 5))
      s Q := by
  have lt := r_lt hp
  have hsub : Region.Sub ⟨scA s₀, 128⟩ (scR s₀) := w_sub
  exact hS s A (bP s₀) (sc s₀) (rr s₀) hsi hcx hdx hax hp.pos lt
    ((hp.b_s.sub_left b_sub').sub_right hsub) hA.b hA.w hA.nw (by have := hp.b_nw; omega_arith)
    (by have := hp.s_nw; omega_arith) (by rw [h.esp]; exact hp.sp_lo) (by rw [h.esp]; exact hA.stk)
    (by rw [h.esp]; exact hp.stk_b.sub_right b_sub') (by rw [h.esp]; exact hp.stk_s.sub_right hsub)
    (by rw [h.rd, h.wr]; exact hA.inr) (by rw [h.wr]; exact b_in hp) (by rw [h.wr]; exact w_in hp)
    Q fun s' hrd hwr hcs hf hb => hQ s' hrd hwr hcs (by rw [h.esp] at hf; exact hf) hb

/-- Setting up the arguments of the call. -/
theorem bmArgs_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Base s₀ s) {Q : State → Prop}
    (k : ∀ s', Base s₀ s' → s'.mem = s.mem → (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r) →
      s'.gpr .eax = sc s₀ → s'.gpr .ecx = BitVec.ofNat 32 (rr s₀) → s'.gpr .edx = bP s₀ → Q s') :
    WP isa (.block bmArgs) s Q := by
  unfold bmArgs
  refine wp_arg (i := 4) hp h (by omega_arith) fun a ua => ?_
  have ba := h.upd ua (by decide)
  refine wp_arg (i := 1) hp ba (by omega_arith) fun b ub => ?_
  have bb := ba.upd ub (by decide)
  refine wp_arg (i := 0) hp bb (by omega_arith) fun d ud => WP.block_nil ?_
  exact k d (bb.upd ud (by decide)) (by rw [ud.mem, ub.mem, ua.mem])
    (fun r h1 h2 h3 => by rw [ud.other _ h3, ub.other _ h2, ua.other _ h1])
    (by rw [ud.other _ (by decide), ub.other _ (by decide), ua.gpr]) (by rw [ud.other _ (by decide),
      ub.gpr, toNat_rr]) ud.gpr

/-- Setting up the arguments and making the call, with `esi = A`. -/
theorem bm_ok {c : Prog isa} (hS : BlockMixSpec c) {s₀ : State} (hp : Pre s₀) {s : State}
    {A : BitVec 32} (hA : SrcOK s₀ A) (h : Base s₀ s) (hsi : s.gpr .esi = A) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame (cfr s₀) s.mem s'.mem →
      bytesAt s'.mem (bA s₀) (128 * rr s₀) =
        blockMix (rr s₀) (bytesAt s.mem (A.setWidth 64) (128 * rr s₀)) → Q s') :
    WP isa (blockMixTo c) s Q := by
  unfold blockMixTo
  refine WP.seq (bmArgs_ok hp h fun d bd em k hax hcx hdx => ?_)
  refine bmFrame_ok hS hp hA bd (by rw [k _ (by decide) (by decide) (by decide), hsi]) hax hcx hdx
    fun s' hrd hwr hcs hf hb => hQ s' (by rw [hrd, bd.rd, h.rd]) (by rw [hwr, bd.wr, h.wr])
      (fun r hr => by
        rw [hcs r hr]
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact k _ (by decide) (by decide) (by decide))
      (by rw [em] at hf; exact hf) (by rw [em] at hb; exact hb)

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem vAt_in {i : Nat} (hi : i < NN s₀) : InRegions s₀.wr (vAt s₀ i) (128 * rr s₀) := by
  rw [hp.wr]
  have e := vl_mul hp
  have := v_le hi
  have lt := v_lt hp
  exact InRegions.of_mem (R := vR s₀) (by simp) (contains_off (by rw [e]; omega_arith) (by omega_arith))

/-- `(V[i]'(by omega_arith))` and the parts of `scratch` we use. -/
theorem vAt_b {i : Nat} (hi : i < NN s₀) : Region.Disjoint ⟨vAt s₀ i, 128 * rr s₀⟩ (bR s₀) :=
  hp.b_v.symm.sub_left (vAt_sub hp hi)
theorem vAt_s {i : Nat} (hi : i < NN s₀) : Region.Disjoint ⟨vAt s₀ i, 128 * rr s₀⟩ (scR s₀) :=
  hp.v_s.sub_left (vAt_sub hp hi)
theorem vAt_stk {i : Nat} (hi : i < NN s₀) : (stkR s₀).Disjoint ⟨vAt s₀ i, 128 * rr s₀⟩ :=
  hp.stk_v.sub_right (vAt_sub hp hi)

omit hp in
/-- The frame of a call writing `b`, from the one we keep. -/
theorem call_frame {m m' : Mem} (hf : Frame (cfr s₀) m m') : Frame (frs s₀) m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨bR s₀, by simp, b_sub'⟩
    · exact ⟨scR s₀, by simp, w_sub⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩

/-- What a call writing `b` keeps: `(V[k]'(by omega_arith))`. -/
theorem call_keeps_v {m m' : Mem} (hf : Frame (cfr s₀) m m') {k : Nat} (hk : k < NN s₀) :
    bytesAt m' (vAt s₀ k) (128 * rr s₀) = bytesAt m (vAt s₀ k) (128 * rr s₀) := by
  refine frame_bytesAt hf (fun r hr => ?_) (by have := r_lt hp; omega_arith)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (vAt_b hp hk).sub_right b_sub'
  · exact (vAt_s hp hk).sub_right w_sub
  · exact (vAt_stk hp hk).symm

theorem call_saved {m m' : Mem} (hf : Frame (cfr s₀) m m') (h : Saved s₀ m) : Saved s₀ m' :=
  h.frame hf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (keep_b hp).sub_right b_sub'
    · exact keep_w
    · exact keep_stk hp

theorem srcOK_v {i : Nat} (hi : i < NN s₀) : SrcOK s₀ (vAt32 s₀ i) := by
  have e := vAt_addr hp hi
  exact ⟨by rw [e]; exact (vAt_b hp hi).sub_right b_sub', by rw [e]; exact (vAt_s hp hi).sub_right w_sub,
    by rw [e]; exact vAt_stk hp hi, vAt_nw hp hi, by rw [e]; exact InRegions.right (vAt_in hp hi)⟩

theorem t_b : Region.Disjoint ⟨tP s₀, 128 * rr s₀⟩ ⟨bA s₀, 128 * rr s₀⟩ :=
  (hp.b_s.symm.sub_left (t_sub hp)).sub_right b_sub'

theorem t_in : InRegions s₀.wr (tP s₀) (128 * rr s₀) := by
  have := hp.s_nw
  rw [hp.wr]
  exact InRegions.of_mem (R := scR s₀) (by simp) (contains_off (by omega_arith) (by omega_arith))

theorem srcOK_t : SrcOK s₀ (tP32 s₀) := by
  have e := t_addr hp
  exact ⟨by rw [e]; exact t_b hp, by rw [e]; exact t_w hp,
    by rw [e]; exact hp.stk_s.sub_right (t_sub hp), t_nw hp,
    by rw [e]; exact InRegions.right (t_in hp)⟩

/-- The memory after iteration `i` of step 2. -/
theorem mem2_ok {i : Nat} (hi : i < NN s₀) {s : State} (h : Inv2 s₀ i s) {m₃ : Mem}
    (f₃ : Frame (cfr s₀) (writeBytes s.mem (vAt s₀ i) (bytesAt s.mem (bA s₀) (128 * rr s₀))) m₃)
    (b₃ : bytesAt m₃ (bA s₀) (128 * rr s₀) = blockMix (rr s₀)
      (bytesAt (writeBytes s.mem (vAt s₀ i) (bytesAt s.mem (bA s₀) (128 * rr s₀))) (vAt s₀ i)
        (128 * rr s₀))) :
    Frame (frs s₀) s₀.mem m₃ ∧ Saved s₀ m₃ ∧
    bytesAt m₃ (bA s₀) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) (i + 1) (B s₀) ∧
    ∀ k < i + 1, bytesAt m₃ (vAt s₀ k) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) k (B s₀) := by
  have lt := r_lt hp
  have hl : (bytesAt s.mem (bA s₀) (128 * rr s₀)).length = 128 * rr s₀ := bytesAt_length _ _ _
  have hself : bytesAt (writeBytes s.mem (vAt s₀ i) (bytesAt s.mem (bA s₀) (128 * rr s₀))) (vAt s₀ i)
      (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) i (B s₀) := by
    have := bytesAt_writeBytes_self s.mem (vAt s₀ i) (bytesAt s.mem (bA s₀) (128 * rr s₀))
      (by rw [hl]; omega_arith)
    rw [hl] at this
    rw [this, h.x]
  have f₂ : Frame [⟨vAt s₀ i, 128 * rr s₀⟩] s.mem
      (writeBytes s.mem (vAt s₀ i) (bytesAt s.mem (bA s₀) (128 * rr s₀))) :=
    Proof.Sha256.Stream.writeBytes_frame _ _ _ (by rw [hl]; exact Region.contains_self _ _)
  have f₂' : Frame (frs s₀) s.mem
      (writeBytes s.mem (vAt s₀ i) (bytesAt s.mem (bA s₀) (128 * rr s₀))) :=
    f₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨vR s₀, by simp, vAt_sub hp hi⟩
  refine ⟨(h.frame.trans f₂').trans (call_frame f₃), call_saved hp f₃ (h.saved.frame f₂ fun r hr => ?_),
    by rw [b₃, hself]; rfl, fun k hk => ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact (keep_v hp).sub_right (vAt_sub hp hi)
  · rw [call_keeps_v hp f₃ (by omega_arith)]
    by_cases hki : k = i
    · subst hki; exact hself
    · rw [bytesAt_writeBytes_sep _ _ (by rw [hl]; exact vAt_disj hp (by omega_arith) hi hki) (by omega_arith)]
      exact h.done k (by omega_arith)

end

theorem vAt_succ (s₀ : State) (i : Nat) :
    vAt32 s₀ i + BitVec.ofNat 32 (rr s₀ * 128) = vAt32 s₀ (i + 1) := by
  show _ = vP s₀ + BitVec.ofNat 32 (128 * rr s₀ * (i + 1))
  rw [add32, Nat.mul_succ (128 * rr s₀) i, Nat.mul_comm (rr s₀) 128]

theorem b_word {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < 8 * rr s₀) :
    InRegions (s₀.rd ++ s₀.wr) (bA s₀ + BitVec.ofNat 64 (16 * k)) 16 := by
  have := r_lt hp
  rw [hp.rd, hp.wr]
  exact InRegions.of_mem (R := bR s₀) (by simp) (contains_off (by omega_arith) (by omega_arith))

theorem v_word {s₀ : State} (hp : Pre s₀) {i k : Nat} (hi : i < NN s₀) (hk : k < 8 * rr s₀) :
    InRegions s₀.wr ((vAt32 s₀ i).setWidth 64 + BitVec.ofNat 64 (16 * k)) 16 := by
  rw [hp.wr, vAt_addr hp hi]
  have e := vl_mul hp
  have := v_le hi
  have lt := v_lt hp
  show InRegions _ (vA s₀ + BitVec.ofNat 64 (128 * rr s₀ * i) + BitVec.ofNat 64 (16 * k)) 16
  rw [add_ofNat]
  exact InRegions.of_mem (R := vR s₀) (by simp) (contains_off (by rw [e]; omega_arith) (by omega_arith))

theorem t_word {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < 8 * rr s₀) :
    InRegions s₀.wr ((tP32 s₀).setWidth 64 + BitVec.ofNat 64 (16 * k)) 16 := by
  have := hp.s_nw
  rw [hp.wr, t_addr hp, add_ofNat]
  exact InRegions.of_mem (R := scR s₀) (by simp) (contains_off (by omega_arith) (by omega_arith))

theorem mul8 (s₀ : State) :
    BitVec.ofNat 32 ((VG.X86.arg s₀ 1).toNat * (8 : BitVec 32).toNat) = BitVec.ofNat 32 (8 * rr s₀) := by
  rw [show (8 : BitVec 32).toNat = 8 from rfl, Nat.mul_comm]

theorem mul128 (s₀ : State) :
    BitVec.ofNat 32 ((VG.X86.arg s₀ 1).toNat * (128 : BitVec 32).toNat) = BitVec.ofNat 32 (rr s₀ * 128) := by
  rw [show (128 : BitVec 32).toNat = 128 from rfl]

/-- One iteration of step 2. -/
theorem step2_ok {c : Prog isa} (hS : BlockMixSpec c) {s₀ : State} (hp : Pre s₀) {i : Nat}
    (hi : i < NN s₀) {s : State} (h : Inv2 s₀ i s) :
    WP isa (step2 c) s fun s' => Inv2 s₀ (i + 1) s' ∧ s'.zf = some (decide (i + 1 = NN s₀)) := by
  have lt := r_lt hp
  have pos := hp.pos
  have hN := NN_lt hp
  have hb := hp.b_nw
  unfold step2
  refine WP.seq (timesR_ok (r := VG.X86.arg s₀ 1) (h.arg hp (i := 1) (by omega_arith))
    (h.arg_in hp (i := 1) (by omega_arith)) fun t e o mt rdt wrt => ?_)
  have bt : Base s₀ t := ⟨rdt.trans h.rd, wrt.trans h.wr,
    (o _ (by decide) (by decide) (by decide)).trans h.esp, by rw [mt]; exact h.frame⟩
  refine wp_mov fun a ua => wp_arg (i := 0) hp (bt.upd ua (by decide)) (by omega_arith) fun b ub =>
    wp_mov fun d ud => WP.block_nil ?_
  have bd : Base s₀ d := ((bt.upd ua (by decide)).upd ub (by decide)).upd ud (by decide)
  have ke : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → d.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [ud.other _ h2, ub.other _ h1, ua.other _ h3, o r h1 h2 h3]
  have hme : d.mem = s.mem := by rw [ud.mem, ub.mem, ua.mem, mt]
  have e4 : 16 * (8 * rr s₀) = 128 * rr s₀ := by omega_arith
  refine WP.seq (WP.mono (copyLoop_ok (src := bP s₀) (dst := vAt32 s₀ i) (n := 8 * rr s₀)
    (by omega_arith) (by omega_arith) (by omega_arith) (by rw [e4]; exact vAt_nw hp hi)
    (by rw [ud.other _ (by decide), ub.gpr])
    (by rw [ud.gpr, ub.other _ (by decide), ua.other _ (by decide), o _ (by decide) (by decide)
      (by decide), h.esi])
    (by rw [ud.other _ (by decide), ub.other _ (by decide), ua.gpr, e, mul8 s₀])
    (fun k hk => by rw [bd.rd, bd.wr]; exact b_word hp hk)
    (fun k hk => by rw [bd.wr]; exact v_word hp hi hk)
    (by rw [e4, vAt_addr hp hi]; exact (vAt_b hp hi).symm.sub_left b_sub'))
    fun t' ⟨rdt', wrt', gt', mt'⟩ => ?_)
  rw [hme, e4, vAt_addr hp hi] at mt'
  have kt : ∀ r ∈ calleeSaved, r ≠ .edi → t'.gpr r = s.gpr r := fun r hr h4 => by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      first | exact absurd rfl h4 | rw [gt' _ (by decide) (by decide) (by decide) (by decide),
        ke _ (by decide) (by decide) (by decide)]
  have ft : Frame (frs s₀) s₀.mem t'.mem := by
    rw [mt']
    refine h.frame.trans (Proof.Sha256.Stream.writeBytes_frame (R := ⟨vAt s₀ i, 128 * rr s₀⟩)
      _ _ _ ?_ |>.sub fun r hr => ?_)
    · rw [bytesAt_length]; exact Region.contains_self _ _
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨vR s₀, by simp, vAt_sub hp hi⟩
  have bt' : Base s₀ t' := ⟨by rw [rdt', bd.rd], by rw [wrt', bd.wr],
    by rw [kt _ (by simp [calleeSaved]) (by decide), h.esp], ft⟩
  refine WP.seq (bm_ok hS hp (srcOK_v hp hi) bt' (by rw [kt _ (by simp [calleeSaved]) (by decide), h.esi])
    fun s4 rd4 wr4 cs4 f4 b4 => ?_)
  rw [mt'] at f4 b4
  rw [vAt_addr hp hi] at b4
  obtain ⟨F, K, X, D⟩ := mem2_ok hp hi h f4 b4
  have k4 : ∀ r ∈ calleeSaved, r ≠ .edi → s4.gpr r = s.gpr r := fun r hr h4 => by
    rw [cs4 r hr, kt r hr h4]
  have b4' : Base s₀ s4 := ⟨by rw [rd4, bt'.rd], by rw [wr4, bt'.wr],
    by rw [k4 _ (by simp [calleeSaved]) (by decide), h.esp], F⟩
  refine timesR_ok (r := VG.X86.arg s₀ 1) (b4'.arg hp (i := 1) (by omega_arith))
    (b4'.arg_in hp (i := 1) (by omega_arith)) fun t5 e5 o5 m5 rd5 wr5 => ?_
  refine wp_add fun s6 u6 => wp_subi fun s7 u7 z7 => WP.block_nil ?_
  have e3 : s6.gpr .ebx = BitVec.ofNat 32 (NN s₀ - i) := by
    rw [u6.other _ (by decide), o5 _ (by decide) (by decide) (by decide),
      k4 _ (by simp [calleeSaved]) (by decide), h.ebx]
  have m7 : s7.mem = s4.mem := by rw [u7.mem, u6.mem, m5]
  refine ⟨⟨⟨by rw [u7.rd, u6.rd, rd5, b4'.rd], by rw [u7.wr, u6.wr, wr5, b4'.wr],
    by rw [u7.other _ (by decide), u6.other _ (by decide), o5 _ (by decide) (by decide) (by decide),
      b4'.esp], by rw [m7]; exact F⟩, by omega_arith, by rw [u7.gpr, e3, dec_count hi], ?_, ?_,
    by rw [m7]; exact K, by rw [m7]; exact X, by rw [m7]; exact D⟩, by rw [z7, e3, dec_z hi hN]⟩
  · rw [u7.other _ (by decide), u6.gpr, o5 _ (by decide) (by decide) (by decide), e5,
      k4 _ (by simp [calleeSaved]) (by decide), h.esi, mul128 s₀, vAt_succ]
  · rw [u7.other _ (by decide), u6.other _ (by decide), o5 _ (by decide) (by decide) (by decide),
      k4 _ (by simp [calleeSaved]) (by decide), h.ebp]

theorem loop2_ok {c : Prog isa} (hS : BlockMixSpec c) {s₀ : State} (hp : Pre s₀) {s : State}
    (h : Inv2 s₀ 0 s) : WP isa (.loop (step2 c) .ne) s (Inv2 s₀ (NN s₀)) :=
  count_loop (NN_pos hp) (Inv2 s₀) (fun _ hi _ h => step2_ok hS hp hi h) h

/-! ## Step 3 -/

/-- After `i` iterations of step 3. -/
structure Inv3 (s₀ : State) (i : Nat) (s : State) : Prop extends Base s₀ s where
  i_le : i ≤ NN s₀
  ebx : s.gpr .ebx = BitVec.ofNat 32 (NN s₀ - i)
  ebp : s.gpr .ebp = BitVec.ofNat 32 (NN s₀)
  saved : Saved s₀ s.mem
  v : ∀ k < NN s₀, bytesAt s.mem (vAt s₀ k) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) k (B s₀)
  x : (Spec.Scrypt.mixLoop (rr s₀) (NN s₀) (vList (rr s₀) (NN s₀) (B s₀)) (NN s₀ - i)
    (bytesAt s.mem (bA s₀) (128 * rr s₀))).1 = roMix (rr s₀) (NN s₀) (B s₀)
  /-- The indices still to come. -/
  js : (Spec.Scrypt.mixLoop (rr s₀) (NN s₀) (vList (rr s₀) (NN s₀) (B s₀)) (NN s₀ - i)
    (bytesAt s.mem (bA s₀) (128 * rr s₀))).2 =
      (Spec.Scrypt.roMixIndices (rr s₀) (NN s₀) (B s₀)).drop i

theorem mid_ok {s₀ : State} {s : State} (h : Inv2 s₀ (NN s₀) s) :
    WP isa (.block rmMid) s (Inv3 s₀ 0) := by
  unfold rmMid
  refine wp_mov fun b ub => WP.block_nil ?_
  have hm : b.mem = s.mem := ub.mem
  refine ⟨h.toBase.upd ub (by decide), Nat.zero_le _, by rw [ub.gpr, h.ebp]; rfl,
    by rw [ub.other _ (by decide), h.ebp], by rw [hm]; exact h.saved,
    fun k hk => by rw [hm]; exact h.done k hk, ?_, ?_⟩
  · rw [hm, h.x, Nat.sub_zero]
    exact (roMix_eq _ _ _).symm
  · rw [hm, h.x, Nat.sub_zero, List.drop_zero]
    exact (roMixIndices_eq _ _ _).symm

/-- The index `j`. -/
abbrev jOf (s₀ : State) (m : Mem) : Nat :=
  Spec.Scrypt.integerify (rr s₀) (bytesAt m (bA s₀) (128 * rr s₀)) % NN s₀

theorem jOf_lt {s₀ : State} (hp : Pre s₀) (m : Mem) : jOf s₀ m < NN s₀ :=
  Nat.mod_lt _ (NN_pos hp)

/-- `j` as the code computes it. -/
theorem jOf_eq {s₀ : State} (hp : Pre s₀) (m : Mem) :
    m.readW (bA s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64)) 32 &&& BitVec.ofNat 32 (NN s₀ - 1) =
      BitVec.ofNat 32 (jOf s₀ m) := by
  obtain ⟨e, he⟩ := hp.pow
  have hN := NN_lt hp
  have he' : e ≤ 32 := by
    by_contra hc
    have : 2 ^ 32 < 2 ^ e := Nat.pow_lt_pow_right (by decide) (by omega_arith)
    omega_arith
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := jOf_lt hp m; omega_arith), he, and_mask32 _ he',
    jOf, he, integerify_mod32 _ _ hp.pos he']

theorem jOf_lt32 {s₀ : State} (hp : Pre s₀) (m : Mem) : jOf s₀ m < 2 ^ 32 := by
  have := jOf_lt hp m; have := NN_lt hp; omega_arith

/-- The memory after iteration `i` of step 3. -/
theorem mem3_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < NN s₀) {s : State} (h : Inv3 s₀ i s)
    {m₄ : Mem}
    (f₄ : Frame (cfr s₀)
      (writeBytes s.mem (tP s₀) (Spec.Pbkdf2.xorBytes (bytesAt s.mem (bA s₀) (128 * rr s₀))
        (bytesAt s.mem (vAt s₀ (jOf s₀ s.mem)) (128 * rr s₀)))) m₄)
    (b₄ : bytesAt m₄ (bA s₀) (128 * rr s₀) = blockMix (rr s₀)
      (bytesAt (writeBytes s.mem (tP s₀) (Spec.Pbkdf2.xorBytes (bytesAt s.mem (bA s₀) (128 * rr s₀))
        (bytesAt s.mem (vAt s₀ (jOf s₀ s.mem)) (128 * rr s₀)))) (tP s₀) (128 * rr s₀))) :
    Frame (frs s₀) s₀.mem m₄ ∧ Saved s₀ m₄ ∧
    (∀ k < NN s₀, bytesAt m₄ (vAt s₀ k) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) k (B s₀)) ∧
    (Spec.Scrypt.mixLoop (rr s₀) (NN s₀) (vList (rr s₀) (NN s₀) (B s₀)) (NN s₀ - (i + 1))
      (bytesAt m₄ (bA s₀) (128 * rr s₀))).1 = roMix (rr s₀) (NN s₀) (B s₀) ∧
    (Spec.Scrypt.mixLoop (rr s₀) (NN s₀) (vList (rr s₀) (NN s₀) (B s₀)) (NN s₀ - (i + 1))
      (bytesAt m₄ (bA s₀) (128 * rr s₀))).2 =
        (Spec.Scrypt.roMixIndices (rr s₀) (NN s₀) (B s₀)).drop (i + 1) := by
  have lt := r_lt hp
  have hj := jOf_lt hp s.mem
  set T := Spec.Pbkdf2.xorBytes (bytesAt s.mem (bA s₀) (128 * rr s₀))
    (bytesAt s.mem (vAt s₀ (jOf s₀ s.mem)) (128 * rr s₀)) with hT
  have hl : T.length = 128 * rr s₀ := by
    rw [hT, xorBytes_length _ _ (by simp [bytesAt_length]), bytesAt_length]
  have hself : bytesAt (writeBytes s.mem (tP s₀) T) (tP s₀) (128 * rr s₀) = T := by
    have := bytesAt_writeBytes_self s.mem (tP s₀) T (by rw [hl]; omega_arith)
    rwa [hl] at this
  have f₂ : Frame [⟨tP s₀, 128 * rr s₀⟩] s.mem (writeBytes s.mem (tP s₀) T) :=
    Proof.Sha256.Stream.writeBytes_frame _ _ _ (by rw [hl]; exact Region.contains_self _ _)
  have f₂' : Frame (frs s₀) s.mem (writeBytes s.mem (tP s₀) T) :=
    f₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scR s₀, by simp, t_sub hp⟩
  have hv : ∀ k < NN s₀, bytesAt m₄ (vAt s₀ k) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) k (B s₀) :=
    fun k hk => by
      rw [call_keeps_v hp f₄ hk, bytesAt_writeBytes_sep _ _
        (by rw [hl]; exact (vAt_s hp hk).sub_right (t_sub hp)) (by omega_arith)]
      exact h.v k hk
  have e : NN s₀ - i = NN s₀ - (i + 1) + 1 := by omega_arith
  refine ⟨(h.frame.trans f₂').trans (call_frame f₄),
    call_saved hp f₄ (h.saved.frame f₂ fun r hr => ?_), hv, ?_, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact keep_t hp
  · rw [← h.x, e, mixLoop_succ_fst, b₄, hself, hT, vList_getD _ hj, h.v _ hj]
  · have hs := h.js
    rw [e, mixLoop_succ_snd, vList_getD _ hj, ← h.v _ hj] at hs
    rw [← List.tail_drop, ← hs, b₄, hself, hT]
    rfl

/-- `jBlock`: `eax = j`, `edi = 128 r`. -/
theorem j_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Base s₀ s)
    (hbp : s.gpr .ebp = BitVec.ofNat 32 (NN s₀)) :
    WP isa (.block jBlock) s fun s' => s'.gpr .eax = BitVec.ofNat 32 (jOf s₀ s.mem) ∧
      s'.gpr .edi = BitVec.ofNat 32 (rr s₀ * 128) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → s'.gpr r = s.gpr r) ∧ Base s₀ s' ∧
      s'.mem = s.mem := by
  have lt := r_lt hp
  have := hp.pos
  have hb := hp.b_nw
  have n1 := NN_pos hp
  unfold jBlock
  refine timesR_ok (r := VG.X86.arg s₀ 1) (h.arg hp (i := 1) (by omega_arith))
    (h.arg_in hp (i := 1) (by omega_arith)) fun t e o mt rdt wrt => ?_
  rw [mul128] at e
  have bt : Base s₀ t := ⟨rdt.trans h.rd, wrt.trans h.wr,
    (o _ (by decide) (by decide) (by decide)).trans h.esp, by rw [mt]; exact h.frame⟩
  refine wp_mov fun a ua => wp_arg (i := 0) hp (bt.upd ua (by decide)) (by omega_arith) fun b ub =>
    wp_add fun c uc => wp_subi fun d ud _ => ?_
  have bd : Base s₀ d :=
    (((bt.upd ua (by decide)).upd ub (by decide)).upd uc (by decide)).upd ud (by decide)
  have ed : d.gpr .eax = bP s₀ + BitVec.ofNat 32 (128 * rr s₀ - 64) := by
    rw [ud.gpr, uc.gpr, ub.other _ (by decide), ua.other _ (by decide), e, ub.gpr, BitVec.add_comm,
      sub32 _ (by omega_arith), Nat.mul_comm]
  have md : d.mem = s.mem := by rw [ud.mem, uc.mem, ub.mem, ua.mem, mt]
  refine wp_movm (a := bA s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64))
    (by rw [ea_at, ed, addr_zero, addr_add (by omega_arith)])
    (by rw [bd.rd, bd.wr, hp.rd, hp.wr]
        exact InRegions.of_mem (R := bR s₀) (by simp) (contains_off (by omega_arith) (by omega_arith)))
    fun f uf => wp_mov fun g ug => wp_subi fun i ui _ => wp_and fun l ul => WP.block_nil ?_
  have ki : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → l.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 => by
      rw [ul.other _ h1, ui.other _ h2, ug.other _ h2, uf.other _ h1, ud.other _ h1, uc.other _ h1,
        ub.other _ h2, ua.other _ h4, o r h1 h2 h3]
  refine ⟨?_, ?_, ki, ?_, by rw [ul.mem, ui.mem, ug.mem, uf.mem, md]⟩
  · rw [ul.gpr, ui.other _ (by decide), ug.other _ (by decide), uf.gpr, ui.gpr, ug.gpr,
      uf.other _ (by decide), ud.other _ (by decide), uc.other _ (by decide), ub.other _ (by decide),
      ua.other _ (by decide), o _ (by decide) (by decide) (by decide), hbp, ofNat_pred32 n1, md,
      jOf_eq hp]
  · rw [ul.other _ (by decide), ui.other _ (by decide), ug.other _ (by decide), uf.other _ (by decide),
      ud.other _ (by decide), uc.other _ (by decide), ub.other _ (by decide), ua.gpr, e]
  · exact (((bd.upd uf (by decide)).upd ug (by decide)).upd ui (by decide)).upd ul (by decide)

/-- `vjBlock`: `ecx = (V[j]'(by omega_arith))`, `eax = X`, `edx = T`, `edi = 8 r`. -/
theorem vj_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Base s₀ s) {j : Nat} (hj : j < NN s₀)
    (hax : s.gpr .eax = BitVec.ofNat 32 j) (hdi : s.gpr .edi = BitVec.ofNat 32 (rr s₀ * 128)) :
    WP isa (.block vjBlock) s fun s' => s'.gpr .ecx = vAt32 s₀ j ∧ s'.gpr .eax = bP s₀ ∧
      s'.gpr .edx = tP32 s₀ ∧ s'.gpr .edi = BitVec.ofNat 32 (8 * rr s₀) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → s'.gpr r = s.gpr r) ∧ Base s₀ s' ∧
      s'.mem = s.mem := by
  have lt := r_lt hp
  have hN := NN_lt hp
  unfold vjBlock
  refine wp_mul fun a ea oa ma rda wra => ?_
  have ba : Base s₀ a := ⟨rda.trans h.rd, wra.trans h.wr, (oa _ (by decide) (by decide)).trans h.esp,
    by rw [ma]; exact h.frame⟩
  refine wp_arg (i := 2) hp ba (by omega_arith) fun b ub => wp_add fun c uc =>
    wp_arg (i := 0) hp ((ba.upd ub (by decide)).upd uc (by decide)) (by omega_arith) fun d ud => ?_
  have bd := ((ba.upd ub (by decide)).upd uc (by decide)).upd ud (by decide)
  refine wp_arg (i := 4) hp bd (by omega_arith) fun f uf => wp_addi fun g ug => wp_shr (by decide) fun l ul =>
    WP.block_nil ?_
  have eax : a.gpr .eax = BitVec.ofNat 32 (128 * rr s₀ * j) := by
    rw [ea, hax, hdi, Proof.Sha256.X86.Stream.toNat_ofNat_lt (by omega_arith),
      Proof.Sha256.X86.Stream.toNat_ofNat_lt (by omega_arith), Nat.mul_comm, Nat.mul_comm (rr s₀) 128]
  refine ⟨?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_, ?_, ?_⟩
  · rw [ul.other _ (by decide), ug.other _ (by decide), uf.other _ (by decide), ud.other _ (by decide),
      uc.gpr, ub.gpr, ub.other _ (by decide), eax]
  · rw [ul.other _ (by decide), ug.other _ (by decide), uf.other _ (by decide), ud.gpr]
  · rw [ul.other _ (by decide), ug.gpr, uf.gpr]; rfl
  · rw [ul.gpr, ug.other _ (by decide), uf.other _ (by decide), ud.other _ (by decide),
      uc.other _ (by decide), ub.other _ (by decide), oa _ (by decide) (by decide), hdi,
      shr_ofNat32 _ (by omega_arith)]
    congr 1; omega_arith
  · rw [ul.other _ h4, ug.other _ h3, uf.other _ h3, ud.other _ h1, uc.other _ h2, ub.other _ h2,
      oa _ h1 h3]
  · exact ((bd.upd uf (by decide)).upd ug (by decide)).upd ul (by decide)
  · rw [ul.mem, ug.mem, uf.mem, ud.mem, uc.mem, ub.mem, ma]

/-- One iteration of step 3. -/
theorem step3_ok {c : Prog isa} (hS : BlockMixSpec c) {s₀ : State} (hp : Pre s₀) {i : Nat}
    (hi : i < NN s₀) {s : State} (h : Inv3 s₀ i s) :
    WP isa (step3 c) s fun s' => Inv3 s₀ (i + 1) s' ∧ s'.zf = some (decide (i + 1 = NN s₀)) := by
  have lt := r_lt hp
  have pos := hp.pos
  have hN := NN_lt hp
  have hj := jOf_lt hp s.mem
  have hb := hp.b_nw
  have e4 : 16 * (8 * rr s₀) = 128 * rr s₀ := by omega_arith
  unfold step3
  refine WP.seq (WP.mono (j_ok hp h.toBase h.ebp) fun a ⟨aax, adi, oa, ba, ma⟩ => ?_)
  refine WP.seq (WP.mono (vj_ok hp ba hj aax adi) fun b ⟨bcx, bax, bdx, bdi, ob, bb, mb⟩ => ?_)
  refine WP.seq (WP.mono (xorLoop_ok (x := bP s₀) (y := vAt32 s₀ (jOf s₀ s.mem)) (d := tP32 s₀)
    (n := 8 * rr s₀) (by omega_arith) (by omega_arith) (by omega_arith)
    (by rw [e4]; exact vAt_nw hp hj) (by rw [e4]; exact t_nw hp) bax bcx bdx bdi
    (fun k hk => by rw [bb.rd, bb.wr]; exact b_word hp hk)
    (fun k hk => by rw [bb.rd, bb.wr]; exact InRegions.right (v_word hp hj hk))
    (fun k hk => by rw [bb.wr]; exact t_word hp hk)
    (by rw [e4, t_addr hp]; exact t_b hp)
    (by rw [e4, t_addr hp, vAt_addr hp hj]; exact (vAt_s hp hj).symm.sub_left (t_sub hp)))
    fun t ⟨rdt, wrt, gt, mt⟩ => ?_)
  rw [mb, ma, e4, t_addr hp, vAt_addr hp hj] at mt
  have kt : ∀ r ∈ calleeSaved, r ≠ .edi → r ≠ .esi → t.gpr r = s.gpr r := fun r hr h4 h5 => by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      first | exact absurd rfl h4 | exact absurd rfl h5 |
      rw [gt _ (by decide) (by decide) (by decide) (by decide) (by decide),
        ob _ (by decide) (by decide) (by decide) (by decide), oa _ (by decide) (by decide) (by decide)
        (by decide)]
  have ft : Frame (frs s₀) s₀.mem t.mem := by
    rw [mt]
    refine h.frame.trans (Proof.Sha256.Stream.writeBytes_frame (R := ⟨tP s₀, 128 * rr s₀⟩)
      _ _ _ ?_ |>.sub fun r hr => ?_)
    · rw [xorBytes_length _ _ (by simp [bytesAt_length]), bytesAt_length]
      exact Region.contains_self _ _
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scR s₀, by simp, t_sub hp⟩
  have bt : Base s₀ t := ⟨by rw [rdt, bb.rd], by rw [wrt, bb.wr],
    by rw [kt _ (by simp [calleeSaved]) (by decide) (by decide), h.esp], ft⟩
  refine WP.seq (wp_arg (i := 4) hp bt (by omega_arith) fun q uq => wp_addi fun q1 v1 => WP.block_nil ?_)
  have bq := (bt.upd uq (by decide)).upd v1 (by decide)
  have kq : ∀ r ∈ calleeSaved, r ≠ .edi → r ≠ .esi → q1.gpr r = s.gpr r := fun r hr h4 h5 => by
    rw [v1.other _ h5, uq.other _ h5, kt r hr h4 h5]
  refine WP.seq (bm_ok hS hp (srcOK_t hp) bq (by rw [v1.gpr, uq.gpr]; rfl)
    fun s4 rd4 wr4 cs4 f4 b4 => ?_)
  rw [v1.mem, uq.mem, mt] at f4 b4
  rw [t_addr hp] at b4
  obtain ⟨F, K, V, X, J⟩ := mem3_ok hp hi h f4 b4
  have k4 : ∀ r ∈ calleeSaved, r ≠ .edi → r ≠ .esi → s4.gpr r = s.gpr r := fun r hr h4 h5 => by
    rw [cs4 r hr, kq r hr h4 h5]
  refine wp_subi fun s5 u5 z5 => WP.block_nil ?_
  have e8 : s4.gpr .ebx = BitVec.ofNat 32 (NN s₀ - i) := by
    rw [k4 _ (by simp [calleeSaved]) (by decide) (by decide), h.ebx]
  refine ⟨⟨⟨by rw [u5.rd, rd4, bq.rd], by rw [u5.wr, wr4, bq.wr],
    by rw [u5.other _ (by decide), k4 _ (by simp [calleeSaved]) (by decide) (by decide), h.esp],
    by rw [u5.mem]; exact F⟩, by omega_arith, by rw [u5.gpr, e8, dec_count hi],
    by rw [u5.other _ (by decide), k4 _ (by simp [calleeSaved]) (by decide) (by decide), h.ebp],
    by rw [u5.mem]; exact K, by rw [u5.mem]; exact V, by rw [u5.mem]; exact X,
    by rw [u5.mem]; exact J⟩, by rw [z5, e8, dec_z hi hN]⟩

theorem loop3_ok {c : Prog isa} (hS : BlockMixSpec c) {s₀ : State} (hp : Pre s₀) {s : State}
    (h : Inv3 s₀ 0 s) : WP isa (.loop (step3 c) .ne) s (Inv3 s₀ (NN s₀)) :=
  count_loop (NN_pos hp) (Inv3 s₀) (fun _ hi _ h => step3_ok hS hp hi h) h

/-! ## The epilogue -/

theorem epilogue_eq : rmEpilogue =
    .mov .eax (.mem (at_ .esp 20)) :: (rmSaved.map (fun p => Instr.mov p.1 (.mem (at_ .eax p.2))) ++ []) :=
  rfl

theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Inv3 s₀ (NN s₀) s) :
    WP isa (.block rmEpilogue) s fun s' => s'.mem = s.mem ∧ (∀ r ∈ calleeSaved, s'.gpr r = s₀.gpr r) := by
  have hs := hp.s_nw
  rw [epilogue_eq]
  refine wp_arg (i := 4) hp h.toBase (by omega_arith) fun s₁ u₁ => ?_
  have e : s₁.gpr .eax = sc s₀ := u₁.gpr
  have ha := rmSaved_addr s₀ hp
  refine Spill.restore_ok rmSaved (by decide) (fun p hp' => ?_)
    (by rw [e, u₁.mem]; exact h.saved.congr (fun p hp' => (ha p hp').symm) fun _ _ => rfl)
    fun s₂ u => WP.block_nil ⟨by rw [u.mem, u₁.mem],
      u.abi (by decide) (by decide) (by rw [u₁.other _ (by decide), h.esp])⟩
  rw [e, u₁.rd, u₁.wr, h.rd, h.wr, hp.rd, hp.wr, ha p hp']
  exact InRegions.of_mem (by simp) (in_s s₀ (by have := rmSaved_fits.1 p hp'; omega_arith))

/-! ## The whole function -/

theorem correct {c : Prog isa} (hS : BlockMixSpec c) {s₀ : State} (hp : Pre s₀) :
    WP isa (roMixWith c) s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Scrypt.roMixX86.post s₀ s' := by
  unfold roMixWith
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (nloop_ok hp h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (setup2_ok hp h₂) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (loop2_ok hS hp h₃) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (mid_ok h₄) fun s₅ h₅ => ?_)
  refine WP.seq (WP.mono (loop3_ok hS hp h₅) fun s₆ h₆ => ?_)
  refine WP.mono (restore_ok hp h₆) fun s' ⟨hm', hg'⟩ => ⟨⟨hg', ?_⟩, ?_⟩
  · rw [hm']
    refine h₆.frame.readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [hp.ret_b, hp.ret_v, hp.ret_s, ret_stk hp]
  · show bytesAt s'.mem (bA s₀) (128 * rr s₀) = roMix (rr s₀) (NN s₀) (B s₀)
    rw [hm', ← h₆.x, Nat.sub_self]
    rfl

end VG.Proof.Scrypt.X86.RoMix
