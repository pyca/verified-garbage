module

public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Common
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.PadKey
import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.RISCV64.Target

/-!
# HMAC over any streaming hash function on RISC-V: `init`'s steps

`init`'s frame (`fr`, `ibytes` bytes) holds the streaming state a long key
is hashed in (`S` bytes at `fr`), its digest (`D` bytes after it), and our
caller's `ra` and `s7`–`s11` (at `iso`). The proofs here start from the
state the frame's body starts in (`s₀`, with the stack pointer at the frame),
whose precondition is `Pre`, and cover the steps once the key `K₀` is made
from is in place (`kq`, `kn` bytes: the key, or the long key's digest),
`KeyOK`: setting both states' hash values with the streaming `init`, writing
`K₀ ⊕ ipad` into the outer state's buffer (`padKey_ok`) and absorbing it into
the inner state (`updBlock_ok`), then `K₀ ⊕ opad` into the inner state's
buffer and absorbing it into the outer state, zeroing the start of the frame
and restoring the registers (`core_ok`). A state representing the empty
message or a whole block does not use its buffer (`HashOK.repr_keep`). Every
write is in the two states, the frame or the `F` bytes below it, where the
callees' frames go.
-/

@[expose] public section

namespace VG.Proof.Hmac.Stream.RISCV64.Init

open VG.RISCV64
open VG.RISCV64.Steps (Upd Mupd wp_li wp_mv wp_addi)
open VG.Impl.Hmac.Stream.RISCV64 (Hash mov)
open VG.WriteBytes (writeBytes)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad blockKey)

/-! ## The precondition -/

section
variable (H : Hash) (s₀ : State)

/-- The frame. -/
abbrev fr : Addr := s₀.sp
abbrev inn : Addr := s₀.gpr .a0
abbrev out : Addr := s₀.gpr .a1
abbrev kp : Addr := s₀.gpr .a2
abbrev kl : Nat := (s₀.gpr .a3).toNat
/-- The key. -/
abbrev K : List Byte := bytesAt s₀.mem (kp s₀) (kl s₀)
abbrev inR : Region := ⟨inn s₀, H.S⟩
abbrev outR : Region := ⟨out s₀, H.S⟩
abbrev kR : Region := ⟨kp s₀, kl s₀⟩
abbrev frR : Region := ⟨fr s₀, H.ibytes⟩
/-- The stack below the frame, where the callees' frames go. -/
abbrev stk : Region := below (fr s₀) H.F
/-- Where our caller's registers are saved. -/
abbrev svR : Region := ⟨fr s₀ + BitVec.ofNat 64 H.iso, 48⟩

end

/-- The state the frame's body starts in. -/
structure Pre (H : Hash) (s₀ : State) : Prop where
  rd : s₀.rd = [kR s₀]
  wr : s₀.wr = [frR H s₀, inR H s₀, outR H s₀]
  i_o : (inR H s₀).Disjoint (outR H s₀)
  k_i : (kR s₀).Disjoint (inR H s₀)
  k_o : (kR s₀).Disjoint (outR H s₀)
  f_i : (frR H s₀).Disjoint (inR H s₀)
  f_o : (frR H s₀).Disjoint (outR H s₀)
  f_k : (frR H s₀).Disjoint (kR s₀)
  al : s₀.sp.toNat % 16 = 0
  spF : H.F ≤ s₀.sp.toNat
  top : s₀.sp.toNat + H.ibytes ≤ 2 ^ 64
  s_i : (stk H s₀).Disjoint (inR H s₀)
  s_o : (stk H s₀).Disjoint (outR H s₀)
  s_k : (stk H s₀).Disjoint (kR s₀)

variable {H : Hash} {s₀ : State}

theorem cover_off {rs : List Region} {R : Region} (h : R ∈ rs) {o n : Nat} (hn : o + n ≤ R.len) :
    Covers [⟨R.base + BitVec.ofNat 64 o, n⟩] rs :=
  VG.Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨R, h, o, rfl, hn⟩

theorem cover_self {rs : List Region} {R : Region} (h : R ∈ rs) : Covers [R] rs :=
  VG.Covers.of_mem fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h

theorem cover_pre {rs : List Region} {R : Region} (h : R ∈ rs) {n : Nat} (hn : n ≤ R.len) :
    Covers [⟨R.base, n⟩] rs :=
  VG.Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨R, h, 0, by simp, by simpa using hn⟩

/-- The hash value at the start of a state. -/
theorem hv_sub (p : Addr) : Region.Sub ⟨p, H.N⟩ ⟨p, H.S⟩ := Region.sub_prefix (by simp)

/-- The buffer of a state. -/
theorem buf_sub (p : Addr) : Region.Sub ⟨p + BitVec.ofNat 64 H.N, H.B⟩ ⟨p, H.S⟩ :=
  Offset.sub_base p (by simp)

/-- A state's hash value and its buffer are disjoint. -/
theorem hv_buf (hl : Lay H) (p : Addr) : Region.Disjoint ⟨p, H.N⟩ ⟨p + BitVec.ofNat 64 H.N, H.B⟩ :=
  Offset.base_disjoint p (Nat.le_refl _) (by have := hl.N; have := hl.B; omega_arith)

theorem Pre.f_s (hp : Pre H s₀) : (frR H s₀).Disjoint (stk H s₀) :=
  Offset.base_disjoint_below _ (by have := hp.top; have := hp.spF; have := s₀.sp.isLt; omega_arith)

/-- The save area, in the frame. -/
theorem sv_sub (hl : Lay H) : Region.Sub (svR H s₀) (frR H s₀) :=
  Offset.sub_base _ hl.ibytes.1

/-- The long key's streaming state, in the frame. -/
theorem lst_sub (hl : Lay H) : Region.Sub ⟨fr s₀, H.S⟩ (frR H s₀) :=
  Region.sub_prefix (by have := hl.iso; have := hl.ibytes; omega_arith)

/-- The long key's digest, in the frame. -/
theorem ldg_sub (hl : Lay H) : Region.Sub ⟨fr s₀ + BitVec.ofNat 64 H.S, H.D⟩ (frR H s₀) :=
  Offset.sub_base _ (by have := hl.iso; have := hl.ibytes; omega_arith)

/-- What `wipe` zeroes, in the frame. -/
theorem wipe_sub (hl : Lay H) : Region.Sub ⟨fr s₀, 8 * (H.iso / 8)⟩ (frR H s₀) :=
  Region.sub_prefix (by have := hl.iso; have := hl.ibytes; omega_arith)

theorem lst_sv (hl : Lay H) : Region.Disjoint ⟨fr s₀, H.S⟩ (svR H s₀) :=
  Offset.base_disjoint _ (by have := hl.iso; omega_arith) (by have := hl.ibytes; omega_arith)

theorem ldg_sv (hl : Lay H) : Region.Disjoint ⟨fr s₀ + BitVec.ofNat 64 H.S, H.D⟩ (svR H s₀) :=
  Offset.disjoint _ (.inl hl.iso.1) (by have := hl.iso; have := hl.ibytes; omega_arith)
    (by have := hl.ibytes; omega_arith)

theorem wipe_sv (hl : Lay H) : Region.Disjoint ⟨fr s₀, 8 * (H.iso / 8)⟩ (svR H s₀) :=
  Offset.base_disjoint _ (by omega_arith) (by have := hl.ibytes; omega_arith)

theorem lst_ldg (hl : Lay H) : Region.Disjoint ⟨fr s₀, H.S⟩ ⟨fr s₀ + BitVec.ofNat 64 H.S, H.D⟩ :=
  Offset.base_disjoint _ (Nat.le_refl _) (by have := hl.iso; have := hl.ibytes; omega_arith)

/-! ## The registers -/

/-- Where the code keeps a state: `rd`, `wr` and the stack pointer as on entry. -/
structure Regs (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

/-- Our variables in `s7`–`s11`, and the callee-saved registers we never
write. -/
structure Vars (s₀ s : State) (kq : Addr) (kn : Nat) : Prop where
  s7 : s.gpr .s7 = inn s₀
  s8 : s.gpr .s8 = fr s₀
  s9 : s.gpr .s9 = out s₀
  s10 : s.gpr .s10 = kq
  s11 : s.gpr .s11 = BitVec.ofNat 64 kn
  nv : ∀ r ∈ nvRegs, s.gpr r = s₀.gpr r

theorem nv_pres : ∀ r ∈ nvRegs, r ∈ preserved := by decide

/-- `Vars` after a call, which preserves the callee-saved registers. -/
theorem Vars.of_pres {s s' : State} {kq : Addr} {kn : Nat} (h : Vars s₀ s kq kn)
    (hc : ∀ r ∈ preserved, s'.gpr r = s.gpr r) : Vars s₀ s' kq kn :=
  ⟨(hc _ (by decide)).trans h.s7, (hc _ (by decide)).trans h.s8, (hc _ (by decide)).trans h.s9,
    (hc _ (by decide)).trans h.s10, (hc _ (by decide)).trans h.s11,
    fun r hr => (hc r (nv_pres r hr)).trans (h.nv r hr)⟩

/-- `Vars` after code writing only `a0`–`a3` and `t1`–`t6`. -/
theorem Vars.of_keep {s s' : State} {kq : Addr} {kn : Nat} (h : Vars s₀ s kq kn)
    (hc : ∀ r, r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → r ≠ .a3 → r ≠ .t1 → r ≠ .t2 → r ≠ .t3 → r ≠ .t4 →
      r ≠ .t5 → r ≠ .t6 → s'.gpr r = s.gpr r) : Vars s₀ s' kq kn := by
  have k : ∀ r ∈ [Reg.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11], s'.gpr r = s.gpr r := by
    intro r hr
    exact hc r (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
      (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
      (by revert r; decide) (by revert r; decide)
  exact ⟨(k _ (by simp)).trans h.s7, (k _ (by simp)).trans h.s8, (k _ (by simp)).trans h.s9,
    (k _ (by simp)).trans h.s10, (k _ (by simp)).trans h.s11,
    fun r hr => (k r (by revert r; decide)).trans (h.nv r hr)⟩

/-! ## The key `K₀` is made from -/

/-- The `kn` bytes at `kq`: at most a block, readable, and outside the
states and the stack below the frame. -/
structure KeyOK (H : Hash) (s₀ : State) (kq : Addr) (kn : Nat) : Prop where
  le : kn ≤ H.B
  cov : ∀ j < kn, InRegions (s₀.rd ++ s₀.wr) (kq + BitVec.ofNat 64 j) 1
  d_i : Region.Disjoint ⟨kq, kn⟩ (inR H s₀)
  d_o : Region.Disjoint ⟨kq, kn⟩ (outR H s₀)
  d_s : Region.Disjoint ⟨kq, kn⟩ (stk H s₀)

/-- The key bytes survive writes in the states and below the frame. -/
theorem KeyOK.keep {kq : Addr} {kn : Nat} (hk : KeyOK H s₀ kq kn) (hl : Lay H) {rs : List Region}
    (hrs : ∀ r ∈ rs, r = inR H s₀ ∨ r = outR H s₀ ∨ r = stk H s₀ ∨ Region.Sub r (inR H s₀) ∨
      Region.Sub r (outR H s₀))
    {m m' : Mem} (hf : Frame rs m m') : bytesAt m' kq kn = bytesAt m kq kn := by
  have := hk.le
  have := hl.B
  refine Proof.Sha256.Stream.bytesAt_congr fun i hi => hf.bytes (R := ⟨kq, kn⟩) (fun r hr => ?_)
    (by show kn ≤ 2 ^ 64; omega_arith) hi
  rcases hrs r hr with rfl | rfl | rfl | h | h
  exacts [hk.d_i, hk.d_o, hk.d_s, hk.d_i.sub_right h, hk.d_o.sub_right h]

/-! ## `padKey` and `updBlock` -/

theorem pad36 : (BitVec.ofNat 8 0x36 : Byte) = ipad := rfl
theorem pad5c : (BitVec.ofNat 8 0x5c : Byte) = opad := rfl

/-- `padKey dst c`: `K₀ ⊕ c` into the buffer of the state at `q`, the inner
or the outer one. -/
theorem padKey_ok (hp : Pre H s₀) (hl : Lay H) {dst : Reg}
    (hdst : dst ≠ .t1 ∧ dst ≠ .t2 ∧ dst ≠ .t3 ∧ dst ≠ .t4 ∧ dst ≠ .t5 ∧ dst ≠ .t6) {c : Nat}
    (hc : c < 2048) {q : Addr} (hq : q = inn s₀ ∨ q = out s₀) {kq : Addr} {kn : Nat} {Kb : List Byte}
    (hko : KeyOK H s₀ kq kn) {s : State} (hr : Regs s₀ s) (hd : s.gpr dst = q)
    (h10 : s.gpr .s10 = kq) (h11 : s.gpr .s11 = BitVec.ofNat 64 kn) (hk : bytesAt s.mem kq kn = Kb)
    {Q : State → Prop}
    (hQ : ∀ s', Regs s₀ s' → (∀ r, r ≠ .t1 → r ≠ .t2 → r ≠ .t3 → r ≠ .t4 → r ≠ .t5 → r ≠ .t6 →
        s'.gpr r = s.gpr r) →
      s'.mem = writeBytes s.mem (q + BitVec.ofNat 64 H.N) (xorPad (PadKey.K0 Kb H.B) (BitVec.ofNat 8 c)) →
      Q s') :
    WP isa (H.padKey dst c) s Q := by
  have hN := hl.N
  have hB := hl.B
  have hkl := hko.le
  have hw : (⟨q, H.S⟩ : Region) ∈ s₀.wr ∧ Region.Disjoint ⟨kq, kn⟩ ⟨q, H.S⟩ := by
    rcases hq with rfl | rfl
    · exact ⟨by simp [hp.wr], hko.d_i⟩
    · exact ⟨by simp [hp.wr], hko.d_o⟩
  have hy : PadKey.Hyp H s dst kn Kb := ⟨by omega_arith, by omega_arith, hkl, h11, by rw [h10, hk],
    fun j hj => by rw [hr.rd, hr.wr, h10]; exact hko.cov j hj,
    fun j hj => ⟨⟨q, H.S⟩, by rw [hr.wr]; exact hw.1, by
      simp only [PadKey.bp]
      rw [hd, Offset.add_add]; exact Offset.contains_base _ (by simp only [Hash.S]; omega_arith)
        (by omega_arith)⟩,
    by simp only [PadKey.bp]; rw [h10, hd]; exact hw.2.sub_right (buf_sub _), hdst⟩
  refine PadKey.padKey_ok hy hc fun s' hi => ?_
  refine hQ s' ⟨hi.rd.trans hr.rd, hi.wr.trans hr.wr, hi.sp.trans hr.sp⟩ hi.keep ?_
  rw [hi.mem, PadKey.blk_full hy]
  simp only [PadKey.bp]
  rw [hd]

/-- `padKey`'s writes: the buffer of the state at `q`. -/
theorem pad_frame {K : List Byte} (hK : K.length ≤ H.B) (m : Mem) (q : Addr) (c : Byte) :
    Frame [⟨q + BitVec.ofNat 64 H.N, H.B⟩] m
      (writeBytes m (q + BitVec.ofNat 64 H.N) (xorPad (PadKey.K0 K H.B) c)) :=
  VG.WriteBytes.writeBytes_frame _ _ _ (by
    rw [show (xorPad (PadKey.K0 K H.B) c).length = H.B by simp [xorPad, PadKey.K0_length hK]]
    exact Region.contains_self _ _)

theorem pad_bytes (hB : H.B ≤ 128) {K : List Byte} (hK : K.length ≤ H.B) (m : Mem) (q : Addr) (c : Byte) :
    bytesAt (writeBytes m (q + BitVec.ofNat 64 H.N) (xorPad (PadKey.K0 K H.B) c))
      (q + BitVec.ofNat 64 H.N) H.B = xorPad (PadKey.K0 K H.B) c := by
  have e : (xorPad (PadKey.K0 K H.B) c).length = H.B := by simp [xorPad, PadKey.K0_length hK]
  have := VG.Proof.Hmac.Common.bytesAt_writeBytes_self m (q + BitVec.ofNat 64 H.N)
    (xorPad (PadKey.K0 K H.B) c) (by rw [e]; omega_arith)
  rwa [e] at this

variable (hH : HashOK H)
include hH

/-- `updBlock st src`: the block in the buffer of the state at `q` into the
state at `p`, from a `count` of 0. -/
theorem updBlock_ok (hp : Pre H s₀) {st src : Reg} (hsrc : src ≠ .a0 ∧ src ≠ .a1)
    {p q : Addr} (hpq : (p = inn s₀ ∧ q = out s₀) ∨ (p = out s₀ ∧ q = inn s₀)) {s : State} (hr : Regs s₀ s)
    (h_st : s.gpr st = p) (h_src : s.gpr src = q) {Q : State → Prop}
    (hQ : ∀ s', Regs s₀ s' → Frame ([⟨p, H.S⟩] ++ [stk H s₀]) s.mem s'.mem →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      (hH.SH.Repr s.mem p [] → hH.SH.Repr s'.mem p (bytesAt s.mem (q + BitVec.ofNat 64 H.N) H.B)) → Q s') :
    WP isa (H.updBlock st src) s Q := by
  have hl := hH.lay
  have hN := hl.N
  have hB := hl.B
  have hp' : (⟨p, H.S⟩ : Region) ∈ s₀.wr ∧ (⟨q, H.S⟩ : Region) ∈ s₀.wr ∧
      Region.Disjoint ⟨p, H.S⟩ ⟨q, H.S⟩ ∧ (stk H s₀).Disjoint ⟨p, H.S⟩ ∧
      (stk H s₀).Disjoint ⟨q, H.S⟩ := by
    rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨by simp [hp.wr], by simp [hp.wr], hp.i_o, hp.s_i, hp.s_o⟩
    · exact ⟨by simp [hp.wr], by simp [hp.wr], hp.i_o.symm, hp.s_o, hp.s_i⟩
  obtain ⟨wp, wq, dpq, sp_, sq⟩ := hp'
  unfold Hash.updBlock
  refine WP.seq (wp_mv fun s₁ u₁ => wp_li (by decide) fun s₂ u₂ =>
    wp_addi (by omega_arith) fun s₃ u₃ => wp_li (by omega_arith) fun s₄ u₄ => WP.block_nil ?_)
  have k : ∀ r, r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → r ≠ .a3 → s₄.gpr r = s.gpr r :=
    fun r a b c d => by rw [u₄.other r d, u₃.other r c, u₂.other r b, u₁.other r a]
  have r₄ : Regs s₀ s₄ :=
    ⟨by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd, hr.rd], by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, hr.wr],
      by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp, hr.sp]⟩
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have a1 : s₄.gpr .a1 = BitVec.ofNat 64 ([] : List Byte).length := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
    rfl
  refine hH.callUpd_ok (st := p) (dat := q + BitVec.ofNat 64 H.N) (len := H.B)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h_st])
    (by rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ hsrc.2, u₁.other _ hsrc.1, h_src])
    (by rw [u₄.gpr, BitVec.toNat_ofNat]; omega_arith)
    (dpq.symm.sub_left (buf_sub _)) (by rw [r₄.sp]; exact hp.al) (by rw [r₄.sp]; exact hp.spF)
    (by rw [r₄.sp]; exact sp_) (by rw [r₄.sp]; exact sq.sub_right (buf_sub _))
    (by
      rw [r₄.rd, r₄.wr]
      exact VG.Covers.append_left
        (cover_off (R := ⟨q, H.S⟩) (o := H.N) (n := H.B) (List.mem_append_right _ wq) (Nat.le_refl _))
        (cover_self (List.mem_append_right _ wp)))
    (by rw [r₄.wr]; exact cover_self wp)
    fun s' rd' wr' sp' f' cs' hpost => hQ s' ⟨rd'.trans r₄.rd, wr'.trans r₄.wr, sp'.trans r₄.sp⟩
      (by rw [r₄.sp, m₄] at f'; exact f')
      (fun r hr => by
        rw [cs' r hr]
        exact k r (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide))
      fun h => by
        have := hpost [] (by rw [m₄]; exact h) a1
        rwa [List.nil_append, m₄] at this

/-! ## The steps once the key is in place -/

omit hH in
/-- What holds between the steps: the registers, the key bytes and the
saved registers. -/
structure St (s₀ s : State) (kq : Addr) (kn : Nat) (Kb : List Byte) : Prop where
  regs : Regs s₀ s
  vars : Vars s₀ s kq kn
  key : bytesAt s.mem kq kn = Kb
  sv : Spill.Saved (fr s₀) s₀.gpr (Hash.savedAt H.iso) s.mem

omit hH in
/-- `St` after writes in the states and below the frame. -/
theorem St.frame (hp : Pre H s₀) (hl : Lay H) {kq : Addr} {kn : Nat} {Kb : List Byte}
    (hko : KeyOK H s₀ kq kn) {s s' : State} (h : St (H := H) s₀ s kq kn Kb) (hr : Regs s₀ s')
    (hv : Vars s₀ s' kq kn) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hrs : ∀ r ∈ rs, r = inR H s₀ ∨ r = outR H s₀ ∨ r = stk H s₀ ∨ Region.Sub r (inR H s₀) ∨
      Region.Sub r (outR H s₀)) : St (H := H) s₀ s' kq kn Kb := by
  refine ⟨hr, hv, by rw [hko.keep hl hrs hf]; exact h.key, h.sv.frame_in savedAt_in hf fun r hr => ?_⟩
  have sv_i : (svR H s₀).Disjoint (inR H s₀) := hp.f_i.sub_left (sv_sub hl)
  have sv_o : (svR H s₀).Disjoint (outR H s₀) := hp.f_o.sub_left (sv_sub hl)
  have sv_s : (svR H s₀).Disjoint (stk H s₀) := hp.f_s.sub_left (sv_sub hl)
  rcases hrs r hr with rfl | rfl | rfl | h | h
  exacts [sv_i, sv_o, sv_s, sv_i.sub_right h, sv_o.sub_right h]

omit hH in
/-- `St` after writes to registers only. -/
theorem St.regs_only {kq : Addr} {kn : Nat} {Kb : List Byte} {s s' : State}
    (h : St (H := H) s₀ s kq kn Kb) (hr : Regs s₀ s') (hv : Vars s₀ s' kq kn) (hm : s'.mem = s.mem) :
    St (H := H) s₀ s' kq kn Kb :=
  ⟨hr, hv, by rw [hm]; exact h.key, by rw [hm]; exact h.sv⟩

/-- `init`'s steps once the key is in place. -/
def core (H : Hash) : Prog isa :=
  .seq (.block [mov .a0 .s7]) (.seq H.callInit (.seq (.block [mov .a0 .s9]) (.seq H.callInit
  (.seq (H.padKey .s9 0x36) (.seq (H.updBlock .s7 .s9) (.seq (H.padKey .s7 0x5c) (.seq (H.updBlock .s9 .s7)
    (.block (H.wipe ++ Hash.restoreAt H.iso)))))))))

/-- `init`'s postcondition, in its frame. -/
def Post (s₀ s' : State) : Prop :=
  (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧ s'.sp = s₀.sp ∧ s'.wr = s₀.wr ∧
    hH.SH.Repr s'.mem (inn s₀) (xorPad (blockKey hH.SH.H (K s₀)) ipad) ∧
    hH.SH.Repr s'.mem (out s₀) (xorPad (blockKey hH.SH.H (K s₀)) opad)

theorem core_ok (hp : Pre H s₀) {kq : Addr} {kn : Nat} {Kb : List Byte} (hko : KeyOK H s₀ kq kn)
    (hk0 : PadKey.K0 Kb H.B = blockKey hH.SH.H (K s₀)) {s : State} (h : St (H := H) s₀ s kq kn Kb) :
    WP isa (core H) s (Post hH s₀) := by
  have hl := hH.lay
  have hN := hl.N
  have hB := hl.B
  have hB' : H.B ≤ 128 := by omega_arith
  have hKl : Kb.length ≤ H.B := by rw [← h.key]; simp only [bytesAt, List.length_map, List.length_range]; exact hko.le
  have hwi : inR H s₀ ∈ s₀.wr := by simp [hp.wr]
  have hwo : outR H s₀ ∈ s₀.wr := by simp [hp.wr]
  have hrw : ∀ R ∈ s₀.wr, R ∈ s₀.rd ++ s₀.wr := fun R h => List.mem_append_right _ h
  have i_s : (inR H s₀).Disjoint (stk H s₀) := hp.s_i.symm
  have o_s : (outR H s₀).Disjoint (stk H s₀) := hp.s_o.symm
  unfold core
  -- The inner state's hash value.
  refine WP.seq (wp_mv fun s₁ u₁ => WP.block_nil ?_)
  have r₁ : Regs s₀ s₁ := ⟨by rw [u₁.rd, h.regs.rd], by rw [u₁.wr, h.regs.wr], by rw [u₁.sp, h.regs.sp]⟩
  have v₁ : Vars s₀ s₁ kq kn := h.vars.of_keep fun r a _ _ _ _ _ _ _ _ _ => u₁.other r a
  have t₁ := h.regs_only r₁ v₁ u₁.mem
  refine WP.seq (hH.callInit_ok (st := inn s₀) (by rw [u₁.gpr, h.vars.s7])
    (by rw [r₁.rd, r₁.wr]; exact cover_self (hrw _ hwi)) (by rw [r₁.wr]; exact cover_self hwi)
    fun s₂ rd₂ wr₂ sp₂ f₂ cs₂ hrI₂ => ?_)
  rw [r₁.sp] at f₂
  have r₂ : Regs s₀ s₂ := ⟨rd₂.trans r₁.rd, wr₂.trans r₁.wr, sp₂.trans r₁.sp⟩
  have t₂ := t₁.frame hp hl hko r₂ (v₁.of_pres cs₂) f₂ (by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    exacts [.inl rfl, .inr (.inr (.inl rfl))])
  -- The outer state's.
  refine WP.seq (wp_mv fun s₃ u₃ => WP.block_nil ?_)
  have r₃ : Regs s₀ s₃ := ⟨by rw [u₃.rd, r₂.rd], by rw [u₃.wr, r₂.wr], by rw [u₃.sp, r₂.sp]⟩
  have v₃ : Vars s₀ s₃ kq kn := t₂.vars.of_keep fun r a _ _ _ _ _ _ _ _ _ => u₃.other r a
  have t₃ := t₂.regs_only r₃ v₃ u₃.mem
  refine WP.seq (hH.callInit_ok (st := out s₀) (by rw [u₃.gpr, t₂.vars.s9])
    (by rw [r₃.rd, r₃.wr]; exact cover_self (hrw _ hwo)) (by rw [r₃.wr]; exact cover_self hwo)
    fun s₄ rd₄ wr₄ sp₄ f₄ cs₄ hrO₄ => ?_)
  rw [r₃.sp, u₃.mem] at f₄
  have r₄ : Regs s₀ s₄ := ⟨rd₄.trans r₃.rd, wr₄.trans r₃.wr, sp₄.trans r₃.sp⟩
  have t₄ := t₂.frame hp hl hko r₄ (v₃.of_pres cs₄) f₄ (by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    exacts [.inr (.inl rfl), .inr (.inr (.inl rfl))])
  have hrI₄ : hH.SH.Repr s₄.mem (inn s₀) [] :=
    hH.repr_keep f₄ (by simp) (by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact hp.i_o.sub_left (hv_sub _)
      · exact i_s.sub_left (hv_sub _)) hrI₂
  -- `K₀ ⊕ ipad` into the outer state's buffer.
  refine WP.seq (padKey_ok hp hl (dst := .s9) (by decide) (c := 0x36) (by decide) (q := out s₀) (.inr rfl)
    hko t₄.regs t₄.vars.s9 t₄.vars.s10 t₄.vars.s11 t₄.key fun s₅ r₅ k₅ m₅ => ?_)
  have fB₅ := pad_frame hKl s₄.mem (out s₀) (BitVec.ofNat 8 0x36)
  rw [← m₅] at fB₅
  have t₅ := t₄.frame hp hl hko r₅ (t₄.vars.of_keep fun r _ _ _ _ a b c d e f => k₅ r a b c d e f) fB₅ (by
    simp only [List.mem_singleton]; rintro r rfl; exact .inr (.inr (.inr (.inr (buf_sub _)))))
  have hrI₅ : hH.SH.Repr s₅.mem (inn s₀) [] :=
    hH.repr_keep fB₅ (by simp) (by
      simp only [List.mem_singleton]; rintro r rfl
      exact (hp.i_o.sub_left (hv_sub _)).sub_right (buf_sub _)) hrI₄
  have hrO₅ : hH.SH.Repr s₅.mem (out s₀) [] :=
    hH.repr_keep fB₅ (by simp) (by
      simp only [List.mem_singleton]; rintro r rfl; exact hv_buf hl _) hrO₄
  -- Absorb it into the inner state.
  refine WP.seq (updBlock_ok hH hp (st := .s7) (src := .s9) (by decide) (.inl ⟨rfl, rfl⟩)
    t₅.regs t₅.vars.s7 t₅.vars.s9 fun s₆ r₆ f₆ cs₆ hup => ?_)
  have t₆ := t₅.frame hp hl hko r₆ (t₅.vars.of_pres cs₆) f₆ (by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    exacts [.inl rfl, .inr (.inr (.inl rfl))])
  have hrI₆ : hH.SH.Repr s₆.mem (inn s₀) (xorPad (PadKey.K0 Kb H.B) ipad) := by
    have := hup hrI₅
    rwa [m₅, pad_bytes hB' hKl] at this
  have hrO₆ : hH.SH.Repr s₆.mem (out s₀) [] :=
    hH.repr_keep f₆ (by simp) (by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact hp.i_o.symm.sub_left (hv_sub _)
      · exact o_s.sub_left (hv_sub _)) hrO₅
  -- `K₀ ⊕ opad` into the inner state's buffer.
  refine WP.seq (padKey_ok hp hl (dst := .s7) (by decide) (c := 0x5c) (by decide) (q := inn s₀) (.inl rfl)
    hko t₆.regs t₆.vars.s7 t₆.vars.s10 t₆.vars.s11 t₆.key fun s₇ r₇ k₇ m₇ => ?_)
  have fB₇ := pad_frame hKl s₆.mem (inn s₀) (BitVec.ofNat 8 0x5c)
  rw [← m₇] at fB₇
  have t₇ := t₆.frame hp hl hko r₇ (t₆.vars.of_keep fun r _ _ _ _ a b c d e f => k₇ r a b c d e f) fB₇ (by
    simp only [List.mem_singleton]; rintro r rfl; exact .inr (.inr (.inr (.inl (buf_sub _)))))
  have hrI₇ : hH.SH.Repr s₇.mem (inn s₀) (xorPad (PadKey.K0 Kb H.B) ipad) :=
    hH.repr_keep fB₇ (by simp [xorPad, PadKey.K0_length hKl]) (by
      simp only [List.mem_singleton]; rintro r rfl; exact hv_buf hl _) hrI₆
  have hrO₇ : hH.SH.Repr s₇.mem (out s₀) [] :=
    hH.repr_keep fB₇ (by simp) (by
      simp only [List.mem_singleton]; rintro r rfl
      exact (hp.i_o.symm.sub_left (hv_sub _)).sub_right (buf_sub _)) hrO₆
  -- Absorb it into the outer state.
  refine WP.seq (updBlock_ok hH hp (st := .s9) (src := .s7) (by decide) (.inr ⟨rfl, rfl⟩)
    t₇.regs t₇.vars.s9 t₇.vars.s7 fun s₈ r₈ f₈ cs₈ hup' => ?_)
  have t₈ := t₇.frame hp hl hko r₈ (t₇.vars.of_pres cs₈) f₈ (by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    exacts [.inr (.inl rfl), .inr (.inr (.inl rfl))])
  have hrO₈ : hH.SH.Repr s₈.mem (out s₀) (xorPad (PadKey.K0 Kb H.B) opad) := by
    have := hup' hrO₇
    rwa [m₇, pad_bytes hB' hKl] at this
  have hrI₈ : hH.SH.Repr s₈.mem (inn s₀) (xorPad (PadKey.K0 Kb H.B) ipad) :=
    hH.repr_keep f₈ (by simp [xorPad, PadKey.K0_length hKl]) (by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact hp.i_o.sub_left (hv_sub _)
      · exact i_s.sub_left (hv_sub _)) hrI₇
  -- Zero the start of the frame, and restore our caller's registers.
  rw [wipe_eq, List.cons_append]
  refine wp_li (by decide) fun s₉ u₉ => ?_
  have hal8 : (fr s₀).toNat % 8 = 0 := by show s₀.sp.toNat % 8 = 0; have := hp.al; omega_arith
  have hiso := hl.iso
  have hib := hl.ibytes
  refine stores_ok (H.iso / 8) (fr := fr s₀) hal8 (by omega_arith)
    (by rw [u₉.other _ (by decide)]; exact t₈.vars.s8)
    (fun j hj => ⟨frR H s₀, by rw [u₉.wr, r₈.wr, hp.wr]; simp,
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    fun s₁₀ g₁₀ rd₁₀ wr₁₀ sp₁₀ f₁₀ => ?_
  rw [restoreAt_eq, ← List.append_nil (Spill.restoreCode _ _)]
  have sv₁₀ : Spill.Saved (fr s₀) s₀.gpr (Hash.savedAt H.iso) s₁₀.mem := by
    refine t₈.sv.frame_in savedAt_in (by rw [u₉.mem] at f₁₀; exact f₁₀) fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr; exact (wipe_sv hl).symm
  refine Spill.restore_ok (B := fr s₀) hal8 (by rw [g₁₀, u₉.other _ (by decide)]; exact t₈.vars.s8)
    (fun p hp' => savedAt_off ⟨hiso.2, by omega_arith⟩ p (restList_mem.mp hp')) (restorable _)
    (fun p hp' => ⟨frR H s₀, by rw [rd₁₀, wr₁₀, u₉.rd, u₉.wr, r₈.rd, r₈.wr, hp.wr]; simp,
      Offset.contains_base _ (by have := savedAt_in p (restList_mem.mp hp'); omega_arith)
        (by have := savedAt_in p (restList_mem.mp hp'); omega_arith)⟩)
    (sv₁₀.sub fun p hp' => restList_mem.mp hp') fun s' hs' => WP.block_nil ?_
  have m' : Frame [⟨fr s₀, 8 * (H.iso / 8)⟩] s₈.mem s'.mem := by rw [hs'.mem, ← u₉.mem]; exact f₁₀
  refine ⟨preserved_of (so := H.iso) (fun p hp' => hs'.gpr p (restList_mem.mpr hp')) fun r hr => ?_,
    hs'.gpr (.ra, H.iso) (by simp [restList]), by rw [hs'.sp, sp₁₀, u₉.sp, r₈.sp],
    by rw [hs'.wr, wr₁₀, u₉.wr, r₈.wr], ?_, ?_⟩
  · rw [hs'.other r (by rw [restList_fst]; revert r; decide), g₁₀, u₉.other r (by revert r; decide)]
    exact t₈.vars.nv r hr
  · rw [← hk0]
    exact hH.repr_keep m' (by simp [xorPad, PadKey.K0_length hKl]) (by
      simp only [List.mem_singleton]; rintro r rfl
      exact (hp.f_i.symm.sub_left (hv_sub _)).sub_right (wipe_sub hl)) hrI₈
  · rw [← hk0]
    exact hH.repr_keep m' (by simp [xorPad, PadKey.K0_length hKl]) (by
      simp only [List.mem_singleton]; rintro r rfl
      exact (hp.f_o.symm.sub_left (hv_sub _)).sub_right (wipe_sub hl)) hrO₈

end VG.Proof.Hmac.Stream.RISCV64.Init
