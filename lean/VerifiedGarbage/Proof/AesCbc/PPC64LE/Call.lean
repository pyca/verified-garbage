module

public import VerifiedGarbage.Proof.AesCbc.Spec
public import VerifiedGarbage.Proof.Aes.PPC64LE.Blocks
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Aes.PPC64LE.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.PPC64LE.Inline

/-!
# AES-CBC on PPC64LE: the contracts, and a call of a block function

The artifacts' contracts are the shared ones of `Spec/Cbc/Contract.lean`,
which imply these (`Verified.lean`): `cbcPPC64LE enc`, for encryption
(`enc = true`) and decryption, `modePPC64LE` for CBC (`cbcMode`). A call
(`bl`) stores nothing in memory, so no stack is used.

`blk_call`: a call of `vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks`
(`f` being `Spec.Aes.cipher` or `Spec.Aes.invCipher`) on one block `D` in
place, with working space `S`, from its contract (with `WP.call`): `D` then
holds `f` of it, only `D` and `S` change, and so do no nonvolatile
registers. `blk_rel`: such calls, with the same arguments in both runs, are
constant time.
-/

@[expose] public section

namespace VG.Proof.AesCbc.PPC64LE

open VG VG.PPC64LE
open VG.Spec.Aes (bytesAt)

/-- A function of `M` with the arguments of `vg_aes_cbc_encrypt`
`(schedule = r3, rounds = r4, iv = r5, data = r6, n = r7, scratch = r8)`. -/
def modePPC64LE (M : Mode) : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .r3, 240⟩
    let iv : Region := ⟨s.gpr .r5, 16⟩
    let data : Region := ⟨s.gpr .r6, 16 * (s.gpr .r7).toNat⟩
    let scr : Region := ⟨s.gpr .r8, 2176⟩
    s.rd = [sched] ∧ s.wr = [iv, data, scr] ∧
      sched.Disjoint iv ∧ sched.Disjoint data ∧ sched.Disjoint scr ∧ iv.Disjoint data ∧
      iv.Disjoint scr ∧ data.Disjoint scr ∧
      (s.gpr .r5).toNat + 16 ≤ 2 ^ 64 ∧ (s.gpr .r6).toNat + 16 * (s.gpr .r7).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + 2176 ≤ 2 ^ 64 ∧
      ((s.gpr .r4).toNat = 10 ∨ (s.gpr .r4).toNat = 12 ∨ (s.gpr .r4).toNat = 14)
  post s s' :=
    let w := bytesAt s.mem (s.gpr .r3) (16 * ((s.gpr .r4).toNat + 1))
    let iv := bytesAt s.mem (s.gpr .r5) 16
    let xs := Spec.Cbc.blocksAt s.mem (s.gpr .r6) (s.gpr .r7).toNat
    Spec.Cbc.blocksAt s'.mem (s.gpr .r6) (s.gpr .r7).toNat = M.out (s.gpr .r4).toNat w iv xs ∧
      bytesAt s'.mem (s.gpr .r5) 16 = M.chain (s.gpr .r4).toNat w iv xs
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.sp = s₂.sp

/-- `vg_aes_cbc_encrypt` (`enc`) or `vg_aes_cbc_decrypt`. -/
abbrev cbcPPC64LE (enc : Bool) : Contract isa := modePPC64LE (cbcMode enc)

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
  r3 : s.gpr .r3 = W
  r4 : s.gpr .r4 = BitVec.ofNat 64 R
  r5 : s.gpr .r5 = D
  r6 : s.gpr .r6 = BitVec.ofNat 64 1
  r7 : s.gpr .r7 = S
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

theorem callEntry_gpr' (s : State) {r : Reg} (h : r ∉ linkRegs) : s.callEntry.gpr r = s.gpr r :=
  State.callEntry_gpr _ h

/-- The block function's precondition, on entry to a call with the regions it is given. -/
theorem CallPre.blk_pre {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {s : State} {W D S : Addr}
    {R : Nat} (h : CallPre s W D S R) :
    (Proof.Aes.blocksPPC64LE f).pre (s.callEntry.withRegions [⟨W, 240⟩] [⟨D, 16⟩, ⟨S, 2048⟩]) := by
  have hR := toNat_rounds h.rounds
  simp only [Proof.Aes.blocksPPC64LE, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, callEntry_gpr' s (by decide : Reg.r3 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.r4 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r5 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.r6 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r7 ∉ linkRegs),
    h.r3, h.r4, h.r5, h.r6, h.r7, hR, one_toNat, Nat.mul_one]
  exact ⟨trivial, trivial, h.wd, h.ws, h.ds, h.wrap, h.rounds⟩

theorem blk_call {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {name : String} {c : Prog isa}
    (ok : ∀ s, (Proof.Aes.blocksPPC64LE f).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksPPC64LE f).post s s')
    (nf : c.noFrames = true)
    {s : State} {W D S : Addr} {R : Nat} (h : CallPre s W D S R) :
    WP isa (.call name c) s (CallPost f s W D S R) := by
  have hR := toNat_rounds h.rounds
  refine WP.call (k := Proof.Aes.blocksPPC64LE f) ok (rd := [⟨W, 240⟩]) (wr := [⟨D, 16⟩, ⟨S, 2048⟩])
    h.blk_pre h.reads h.writes ?_ nf
  intro s' hrd hwr hsp hf hcs _ hpost
  refine ⟨hrd, hwr, hsp, hcs, hf, ?_⟩
  simp only [Proof.Aes.blocksPPC64LE, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    callEntry_gpr' s (by decide : Reg.r3 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r4 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.r5 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r6 ∉ linkRegs),
    h.r3, h.r4, h.r5, h.r6, hR, one_toNat] at hpost
  exact bytesAt_of_statesAt hpost

/-- Calls of a block function on one block, with the same arguments in both
runs, are constant time. -/
theorem blk_rel {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {name : String} {c : Prog isa}
    (ok : ∀ s, (Proof.Aes.blocksPPC64LE f).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksPPC64LE f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksPPC64LE f).pre (Proof.Aes.blocksPPC64LE f).pub c)
    {P : State → State → Prop} {W D S : Addr} {R : Nat}
    (h : ∀ s₁ s₂, P s₁ s₂ → CallPre s₁ W D S R ∧ CallPre s₂ W D S R ∧ s₁.sp = s₂.sp) :
    RelCT isa P (.call name c) fun _ _ => True := by
  refine RelCT.call ok ct [⟨W, 240⟩] [⟨D, 16⟩, ⟨S, 2048⟩] fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨h₁.blk_pre, h₂.blk_pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes⟩
  simp only [Proof.Aes.blocksPPC64LE, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    callEntry_gpr' _ (by decide : Reg.r3 ∉ linkRegs), callEntry_gpr' _ (by decide : Reg.r4 ∉ linkRegs),
    callEntry_gpr' _ (by decide : Reg.r5 ∉ linkRegs), callEntry_gpr' _ (by decide : Reg.r6 ∉ linkRegs),
    callEntry_gpr' _ (by decide : Reg.r7 ∉ linkRegs),
    h₁.r3, h₁.r4, h₁.r5, h₁.r6, h₁.r7, h₂.r3, h₂.r4, h₂.r5, h₂.r6, h₂.r7, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

end VG.Proof.AesCbc.PPC64LE
