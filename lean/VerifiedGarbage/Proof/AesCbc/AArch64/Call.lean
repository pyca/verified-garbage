import VerifiedGarbage.Proof.AesCbc.Mem
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Aes.AArch64.BlocksVariant
import VerifiedGarbage.Impl.AesCbc.AArch64

/-!
# AES-CBC on AArch64: the contracts, and a call of a block function

The artifacts' contracts are the shared ones of `Spec/Cbc/Contract.lean`,
which imply these (`Verified.lean`): `cbcAArch64 enc`, for encryption
(`enc = true`) and decryption. A call (`bl`) stores nothing in memory, so no
stack is used.

`blk_call`: a call of any implementation of `vg_aes_encrypt_blocks` or
`vg_aes_decrypt_blocks` (`f` being `Spec.Aes.cipher` or
`Spec.Aes.invCipher`) on one block `D` in place, with working space `S`,
from its contract (with `WP.call`): `D` then holds `f` of it, and only `D`
and `S` change in memory. `blk_rel`: such calls, with the same arguments in
both runs, are constant time.
-/

namespace VG.Proof.AesCbc.AArch64

open VG VG.AArch64
open VG.Spec.Aes (bytesAt)

/-- `vg_aes_cbc_encrypt` (`enc`) or `vg_aes_cbc_decrypt`
`(schedule = x0, rounds = x1, iv = x2, data = x3, n = x4, scratch = x5)`. -/
def cbcAArch64 (enc : Bool) : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .x0, 240⟩
    let iv : Region := ⟨s.gpr .x2, 16⟩
    let data : Region := ⟨s.gpr .x3, 16 * (s.gpr .x4).toNat⟩
    let scr : Region := ⟨s.gpr .x5, 2176⟩
    s.rd = [sched] ∧ s.wr = [iv, data, scr] ∧
      sched.Disjoint iv ∧ sched.Disjoint data ∧ sched.Disjoint scr ∧ iv.Disjoint data ∧
      iv.Disjoint scr ∧ data.Disjoint scr ∧
      (s.gpr .x2).toNat + 16 ≤ 2 ^ 64 ∧ (s.gpr .x3).toNat + 16 * (s.gpr .x4).toNat ≤ 2 ^ 64 ∧
      (s.gpr .x5).toNat + 2176 ≤ 2 ^ 64 ∧
      ((s.gpr .x1).toNat = 10 ∨ (s.gpr .x1).toNat = 12 ∨ (s.gpr .x1).toNat = 14)
  post s s' :=
    let ciph := ciphOf enc (s.gpr .x1).toNat (bytesAt s.mem (s.gpr .x0) (16 * ((s.gpr .x1).toNat + 1)))
    let iv := bytesAt s.mem (s.gpr .x2) 16
    let xs := Spec.Cbc.blocksAt s.mem (s.gpr .x3) (s.gpr .x4).toNat
    let ys := cbc enc ciph iv xs
    Spec.Cbc.blocksAt s'.mem (s.gpr .x3) (s.gpr .x4).toNat = ys ∧
      bytesAt s'.mem (s.gpr .x2) 16 = Spec.Cbc.next iv (cts enc xs ys)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧ s₁.sp = s₂.sp

/-! ## A call of a block function -/

theorem toNat_rounds {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) : (BitVec.ofNat 64 R).toNat = R := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)

theorem one_toNat : (1 : BitVec 64).toNat = 1 := rfl

theorem callEntry_x0 (s : State) : s.callEntry.gpr .x0 = s.gpr .x0 := s.callEntry_gpr (by decide)
theorem callEntry_x1 (s : State) : s.callEntry.gpr .x1 = s.gpr .x1 := s.callEntry_gpr (by decide)
theorem callEntry_x2 (s : State) : s.callEntry.gpr .x2 = s.gpr .x2 := s.callEntry_gpr (by decide)
theorem callEntry_x3 (s : State) : s.callEntry.gpr .x3 = s.gpr .x3 := s.callEntry_gpr (by decide)
theorem callEntry_x4 (s : State) : s.callEntry.gpr .x4 = s.gpr .x4 := s.callEntry_gpr (by decide)

/-- What a call of a block function on one block needs. -/
structure CallPre (s : State) (W D S : Addr) (R : Nat) : Prop where
  x0 : s.gpr .x0 = W
  x1 : s.gpr .x1 = BitVec.ofNat 64 R
  x2 : s.gpr .x2 = D
  x3 : s.gpr .x3 = 1
  x4 : s.gpr .x4 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  wd : (⟨W, 240⟩ : Region).Disjoint ⟨D, 16⟩
  ws : (⟨W, 240⟩ : Region).Disjoint ⟨S, 2048⟩
  ds : (⟨D, 16⟩ : Region).Disjoint ⟨S, 2048⟩
  wrap : D.toNat + 16 ≤ 2 ^ 64
  reads : Covers ([⟨W, 240⟩] ++ [⟨D, 16⟩, ⟨S, 2048⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨D, 16⟩, ⟨S, 2048⟩] s.wr

/-- What a call of a block function on one block leaves. -/
structure CallPost (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) (s : State) (W D S : Addr)
    (R : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r
  frame : Frame [⟨D, 16⟩, ⟨S, 2048⟩] s.mem s'.mem
  out : bytesAt s'.mem D 16 = (f R (bytesAt s.mem W (16 * (R + 1))) (Spec.Aes.stateAt s.mem D)).toList

/-- The block function's precondition, on entry to a call with the regions it is given. -/
theorem CallPre.blk_pre {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {s : State} {W D S : Addr}
    {R : Nat} (h : CallPre s W D S R) :
    (Proof.Aes.blocksAArch64 f).pre (s.callEntry.withRegions [⟨W, 240⟩] [⟨D, 16⟩, ⟨S, 2048⟩]) := by
  have hR := toNat_rounds h.rounds
  simp only [Proof.Aes.blocksAArch64, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, callEntry_x4,
    h.x0, h.x1, h.x2, h.x3, h.x4, hR, one_toNat, Nat.mul_one]
  exact ⟨trivial, trivial, h.wd, h.ws, h.ds, h.wrap, h.rounds⟩

theorem blk_call {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {b : Impl.Aes.AArch64.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksAArch64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksAArch64 f).post s s')
    (nf : b.code.noFrames = true)
    {s : State} {W D S : Addr} {R : Nat} (h : CallPre s W D S R) :
    WP isa (.call b.name b.code) s (CallPost f s W D S R) := by
  have hR := toNat_rounds h.rounds
  refine WP.call (k := Proof.Aes.blocksAArch64 f) ok (rd := [⟨W, 240⟩])
    (wr := [⟨D, 16⟩, ⟨S, 2048⟩]) h.blk_pre h.reads h.writes ?_ nf
  intro s' hrd hwr hsp hf hsaved _ hpost
  refine ⟨hrd, hwr, hsp, hsaved, hf, ?_⟩
  simp only [Proof.Aes.blocksAArch64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, h.x0, h.x1, h.x2, h.x3, hR, one_toNat] at hpost
  rw [bytesAt_of_statesAt hpost]

/-- Calls of a block function on one block, with the same arguments in both
runs, are constant time. -/
theorem blk_rel {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {b : Impl.Aes.AArch64.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksAArch64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksAArch64 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksAArch64 f).pre (Proof.Aes.blocksAArch64 f).pub b.code)
    {W D S : Addr} {R : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → CallPre s₁ W D S R ∧ CallPre s₂ W D S R ∧ s₁.sp = s₂.sp) :
    RelCT isa P (.call b.name b.code) fun _ _ => True := by
  refine RelCT.call ok ct [⟨W, 240⟩] [⟨D, 16⟩, ⟨S, 2048⟩] fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨h₁.blk_pre, h₂.blk_pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes⟩
  simp only [Proof.Aes.blocksAArch64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, callEntry_x4,
    h₁.x0, h₁.x1, h₁.x2, h₁.x3, h₁.x4, h₂.x0, h₂.x1, h₂.x2, h₂.x3, h₂.x4, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

end VG.Proof.AesCbc.AArch64
