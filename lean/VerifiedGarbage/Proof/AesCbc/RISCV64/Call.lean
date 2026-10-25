module

public import VerifiedGarbage.Proof.AesCbc.Spec
public import VerifiedGarbage.Proof.Aes.RISCV64.Blocks
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Framework.RISCV64.Inline
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.Contract

/-!
# AES-CBC on RISC-V: the contracts, and a call of a block function

The artifacts' contracts are the shared ones of `Spec/Cbc/Contract.lean`,
which imply these (`Verified.lean`): `modeRISCV64 M` for a mode on whole
blocks (`Proof/AesCbc/Spec.lean`), as on PPC64LE
(`Proof/AesCbc/PPC64LE/Call.lean`).

`blk_call`: a call of `vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks`
(`f` being `Spec.Aes.cipher` or `Spec.Aes.invCipher`) on one block `D` in
place, with working space `S`, from its contract (with `WP.call`): `D` then
holds `f` of it, only `D` and `S` change, and so do no callee-saved
registers.
-/

@[expose] public section

namespace VG.Proof.AesCbc.RISCV64

open VG VG.RISCV64
open VG.Spec.Aes (bytesAt)

/-- A function of `M` with the arguments of `vg_aes_cbc_encrypt`
`(schedule = a0, rounds = a1, iv = a2, data = a3, n = a4, scratch = a5)`. -/
def modeRISCV64 (M : Mode) : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .a0, 240⟩
    let iv : Region := ⟨s.gpr .a2, 16⟩
    let data : Region := ⟨s.gpr .a3, 16 * (s.gpr .a4).toNat⟩
    let scr : Region := ⟨s.gpr .a5, 2176⟩
    s.rd = [sched] ∧ s.wr = [iv, data, scr] ∧
      sched.Disjoint iv ∧ sched.Disjoint data ∧ sched.Disjoint scr ∧ iv.Disjoint data ∧
      iv.Disjoint scr ∧ data.Disjoint scr ∧
      (s.gpr .a2).toNat + 16 ≤ 2 ^ 64 ∧ (s.gpr .a3).toNat + 16 * (s.gpr .a4).toNat ≤ 2 ^ 64 ∧
      (s.gpr .a5).toNat + 2176 ≤ 2 ^ 64 ∧
      ((s.gpr .a1).toNat = 10 ∨ (s.gpr .a1).toNat = 12 ∨ (s.gpr .a1).toNat = 14)
  post s s' :=
    let w := bytesAt s.mem (s.gpr .a0) (16 * ((s.gpr .a1).toNat + 1))
    let iv := bytesAt s.mem (s.gpr .a2) 16
    let xs := Spec.Cbc.blocksAt s.mem (s.gpr .a3) (s.gpr .a4).toNat
    Spec.Cbc.blocksAt s'.mem (s.gpr .a3) (s.gpr .a4).toNat = M.out (s.gpr .a1).toNat w iv xs ∧
      bytesAt s'.mem (s.gpr .a2) 16 = M.chain (s.gpr .a1).toNat w iv xs
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧ s₁.sp = s₂.sp

/-! ## A call of a block function -/

/-- Bytes outside a frame are unchanged. -/
theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n :=
  Proof.Cmac.bytesAt_frame hf hd hn

theorem toNat_rounds {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) : (BitVec.ofNat 64 R).toNat = R := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)

theorem one_toNat : (BitVec.ofNat 64 1).toNat = 1 := rfl

/-- What a call of a block function on one block needs. -/
structure CallPre (s : State) (W D S : Addr) (R : Nat) : Prop where
  a0 : s.gpr .a0 = W
  a1 : s.gpr .a1 = BitVec.ofNat 64 R
  a2 : s.gpr .a2 = D
  a3 : s.gpr .a3 = BitVec.ofNat 64 1
  a4 : s.gpr .a4 = S
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
  saved : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  frame : Frame [⟨D, 16⟩, ⟨S, 2048⟩] s.mem s'.mem
  out : bytesAt s'.mem D 16 = (f R (bytesAt s.mem W (16 * (R + 1))) (Spec.Aes.stateAt s.mem D)).toList

/-- The block function's precondition, on entry to a call with the regions it is given. -/
theorem CallPre.blk_pre {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {s : State} {W D S : Addr}
    {R : Nat} (h : CallPre s W D S R) :
    (Proof.Aes.blocksRISCV64 f).pre (s.callEntry.withRegions [⟨W, 240⟩] [⟨D, 16⟩, ⟨S, 2048⟩]) := by
  have hR := toNat_rounds h.rounds
  simp only [Proof.Aes.blocksRISCV64, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a3 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a4 ∉ linkRegs),
    h.a0, h.a1, h.a2, h.a3, h.a4, hR, one_toNat, Nat.mul_one]
  exact ⟨trivial, trivial, h.wd, h.ws, h.ds, h.wrap, h.rounds⟩

theorem blk_call {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {name : String} {c : Prog isa}
    (ok : ∀ s, (Proof.Aes.blocksRISCV64 f).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksRISCV64 f).post s s')
    (nf : c.noFrames = true)
    {s : State} {W D S : Addr} {R : Nat} (h : CallPre s W D S R) :
    WP isa (.call name c) s (CallPost f s W D S R) := by
  have hR := toNat_rounds h.rounds
  refine WP.call (k := Proof.Aes.blocksRISCV64 f) ok (rd := [⟨W, 240⟩]) (wr := [⟨D, 16⟩, ⟨S, 2048⟩])
    h.blk_pre h.reads h.writes ?_ nf
  intro s' hrd hwr hsp hf hcs _ hpost
  refine ⟨hrd, hwr, hsp, hcs, hf, ?_⟩
  simp only [Proof.Aes.blocksRISCV64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a3 ∉ linkRegs),
    h.a0, h.a1, h.a2, h.a3, hR, one_toNat] at hpost
  exact bytesAt_of_statesAt hpost

end VG.Proof.AesCbc.RISCV64
