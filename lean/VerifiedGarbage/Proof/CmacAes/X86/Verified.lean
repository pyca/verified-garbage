import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Proof.Aes.X86.VariantProof
import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Impl.CmacAes.X86
import VerifiedGarbage.Proof.MdStream.X86.Words
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.X86.ArgTaint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Cmac.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.X86.Save`. -/
section

section

section

/-!
# AES-CMAC on x86: the contracts the proofs are written against

The artifacts' contracts are the shared ones of `Spec/Cmac/Contract.lean`,
which imply these (`Verified.lean`). The arguments are on the stack, from
`[esp + 4]` (cdecl). Each call of `vg_aes_ctr32` pushes its six arguments and
the return address in the 28 bytes below `esp`, which may not overlap any
buffer.
-/

namespace VG.Proof.CmacAes.X86

open VG VG.X86

/-- `CIPH_K` for AES with the key schedule at `w` for `R` rounds, in `m`. -/
abbrev ciphAt (m : Mem) (w : Addr) (R : Nat) : Spec.Cmac.Cipher :=
  Spec.Cmac.aesWith R (Spec.Aes.bytesAt m w (16 * (R + 1)))

/-- `vg_cmac_aes_update(schedule, rounds, state, data, n, scratch)`. -/
def updateX86 : Contract isa where
  pre s :=
    let sched : Region := ⟨(VG.X86.arg s 0).setWidth 64, 240⟩
    let state : Region := ⟨(VG.X86.arg s 2).setWidth 64, 16⟩
    let data : Region := ⟨(VG.X86.arg s 3).setWidth 64, 16 * (VG.X86.arg s 4).toNat⟩
    let scr : Region := ⟨(VG.X86.arg s 5).setWidth 64, 2176⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 28, 28⟩
    s.rd = [sched, data, args] ∧ s.wr = [state, scr] ∧
      sched.Disjoint state ∧ sched.Disjoint scr ∧ data.Disjoint state ∧ data.Disjoint scr ∧
      state.Disjoint scr ∧ args.Disjoint state ∧ args.Disjoint scr ∧
      ret.Disjoint state ∧ ret.Disjoint scr ∧
      stack.Disjoint sched ∧ stack.Disjoint data ∧ stack.Disjoint state ∧ stack.Disjoint scr ∧
      (VG.X86.arg s 0).toNat + 240 ≤ 2 ^ 32 ∧ (VG.X86.arg s 2).toNat + 16 ≤ 2 ^ 32 ∧
      (VG.X86.arg s 3).toNat + 16 * (VG.X86.arg s 4).toNat ≤ 2 ^ 32 ∧ (VG.X86.arg s 5).toNat + 2176 ≤ 2 ^ 32 ∧
      28 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 ∧
      ((VG.X86.arg s 1).toNat = 10 ∨ (VG.X86.arg s 1).toNat = 12 ∨ (VG.X86.arg s 1).toNat = 14)
  post s s' :=
    Spec.Aes.bytesAt s'.mem ((VG.X86.arg s 2).setWidth 64) 16 =
      Spec.Cmac.chain (VG.Proof.CmacAes.X86.ciphAt s.mem ((VG.X86.arg s 0).setWidth 64) (VG.X86.arg s 1).toNat)
        (Spec.Aes.bytesAt s.mem ((VG.X86.arg s 2).setWidth 64) 16)
        (Spec.Cmac.blocksAt s.mem ((VG.X86.arg s 3).setWidth 64) 16 (VG.X86.arg s 4).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 6, VG.X86.arg s₁ i = VG.X86.arg s₂ i

/-- `vg_cmac_aes_subkeys(schedule, rounds, subkeys, scratch)`. -/
def subkeysX86 : Contract isa where
  pre s :=
    let sched : Region := ⟨(VG.X86.arg s 0).setWidth 64, 240⟩
    let subk : Region := ⟨(VG.X86.arg s 2).setWidth 64, 32⟩
    let scr : Region := ⟨(VG.X86.arg s 3).setWidth 64, 2176⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 28, 28⟩
    s.rd = [sched, args] ∧ s.wr = [subk, scr] ∧
      sched.Disjoint subk ∧ sched.Disjoint scr ∧ subk.Disjoint scr ∧
      args.Disjoint subk ∧ args.Disjoint scr ∧ ret.Disjoint subk ∧ ret.Disjoint scr ∧
      stack.Disjoint sched ∧ stack.Disjoint subk ∧ stack.Disjoint scr ∧
      (VG.X86.arg s 0).toNat + 240 ≤ 2 ^ 32 ∧ (VG.X86.arg s 2).toNat + 32 ≤ 2 ^ 32 ∧
      (VG.X86.arg s 3).toNat + 2176 ≤ 2 ^ 32 ∧ 28 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 ∧
      ((VG.X86.arg s 1).toNat = 10 ∨ (VG.X86.arg s 1).toNat = 12 ∨ (VG.X86.arg s 1).toNat = 14)
  post s s' :=
    let ks := Spec.Cmac.subkeys (VG.Proof.CmacAes.X86.ciphAt s.mem ((VG.X86.arg s 0).setWidth 64) (VG.X86.arg s 1).toNat) 16
    Spec.Aes.bytesAt s'.mem ((VG.X86.arg s 2).setWidth 64) 32 = ks.1 ++ ks.2
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 4, VG.X86.arg s₁ i = VG.X86.arg s₂ i

/-- `vg_cmac_aes_finalize(key, rounds, state, last, last_len, scratch)`. -/
def finalizeX86 : Contract isa where
  pre s :=
    let key : Region := ⟨(VG.X86.arg s 0).setWidth 64, 272⟩
    let state : Region := ⟨(VG.X86.arg s 2).setWidth 64, 16⟩
    let last : Region := ⟨(VG.X86.arg s 3).setWidth 64, (VG.X86.arg s 4).toNat⟩
    let scr : Region := ⟨(VG.X86.arg s 5).setWidth 64, 2176⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 28, 28⟩
    s.rd = [key, last, args] ∧ s.wr = [state, scr] ∧
      key.Disjoint state ∧ key.Disjoint scr ∧ last.Disjoint state ∧ last.Disjoint scr ∧
      state.Disjoint scr ∧ args.Disjoint state ∧ args.Disjoint scr ∧
      ret.Disjoint state ∧ ret.Disjoint scr ∧
      stack.Disjoint key ∧ stack.Disjoint last ∧ stack.Disjoint state ∧ stack.Disjoint scr ∧
      (VG.X86.arg s 0).toNat + 272 ≤ 2 ^ 32 ∧ (VG.X86.arg s 2).toNat + 16 ≤ 2 ^ 32 ∧
      (VG.X86.arg s 3).toNat + (VG.X86.arg s 4).toNat ≤ 2 ^ 32 ∧ (VG.X86.arg s 5).toNat + 2176 ≤ 2 ^ 32 ∧
      28 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 ∧
      ((VG.X86.arg s 1).toNat = 10 ∨ (VG.X86.arg s 1).toNat = 12 ∨ (VG.X86.arg s 1).toNat = 14) ∧ (VG.X86.arg s 4).toNat ≤ 16
  post s s' :=
    let ciph := VG.Proof.CmacAes.X86.ciphAt s.mem ((VG.X86.arg s 0).setWidth 64) (VG.X86.arg s 1).toNat
    let ks := Spec.Cmac.subkeys ciph 16
    Spec.Aes.bytesAt s.mem ((VG.X86.arg s 0).setWidth 64 + 240) 32 = ks.1 ++ ks.2 →
    ∀ msg : List Byte, msg.length % 16 = 0 → (msg = [] ∨ 0 < (VG.X86.arg s 4).toNat) →
      Spec.Aes.bytesAt s.mem ((VG.X86.arg s 2).setWidth 64) 16 =
        Spec.Cmac.chain ciph (Spec.Cmac.zeros 16) (Spec.Cmac.blocks 16 msg) →
      Spec.Aes.bytesAt s'.mem ((VG.X86.arg s 2).setWidth 64) 16 =
        Spec.Cmac.macFull ciph 16 (msg ++ Spec.Aes.bytesAt s.mem ((VG.X86.arg s 3).setWidth 64) (VG.X86.arg s 4).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 6, VG.X86.arg s₁ i = VG.X86.arg s₂ i

end VG.Proof.CmacAes.X86

end

/-!
# AES-CMAC on x86: blocks formed a word at a time

Weakest preconditions of the instruction sequences the functions build blocks
with: the XOR of the blocks at `pb + pd` and `qb + qd` stored at `cb + cd`
through `eax` and `ecx` (`xor4`, which leaves `Cmac.xor4Mem`), and four stores
of a zeroed `eax` (`zero4`, which leaves `Cmac.zero4`).
-/

namespace VG.Proof.CmacAes.X86

open VG VG.X86 VG.Impl.CmacAes.X86
open VG.Proof.MdStream.X86 (Upd Mupd WP.cons wp_movm wp_movi wp_store)

/-- The `xor4` instructions, written out. -/
def xorBlk (pb qb cb : Reg) (pd qd cd : Nat) : List Instr :=
  [.mov .eax (.mem (at_ pb pd)), .mov .ecx (.mem (at_ qb qd)), .alu .xor .eax (.reg .ecx), .store (at_ cb cd) .eax,
   .mov .eax (.mem (at_ pb (pd + 4))), .mov .ecx (.mem (at_ qb (qd + 4))), .alu .xor .eax (.reg .ecx),
   .store (at_ cb (cd + 4)) .eax,
   .mov .eax (.mem (at_ pb (pd + 8))), .mov .ecx (.mem (at_ qb (qd + 8))), .alu .xor .eax (.reg .ecx),
   .store (at_ cb (cd + 8)) .eax,
   .mov .eax (.mem (at_ pb (pd + 12))), .mov .ecx (.mem (at_ qb (qd + 12))), .alu .xor .eax (.reg .ecx),
   .store (at_ cb (cd + 12)) .eax]

theorem xor4_eq (pb qb cb : Reg) (pd qd cd : Nat) : xor4 pb qb cb pd qd cd = VG.Proof.CmacAes.X86.xorBlk pb qb cb pd qd cd := rfl

theorem zero4_eq (b : Reg) (d : Nat) : zero4 b d =
    [.mov .eax (.imm 0), .store (at_ b d) .eax, .store (at_ b (d + 4)) .eax, .store (at_ b (d + 8)) .eax,
     .store (at_ b (d + 12)) .eax] := rfl

/-- `s'` is `s` with memory `m`, and `eax` and `ecx` (and the flags) clobbered. -/
structure Step (s s' : State) (m : Mem) : Prop where
  gpr : ∀ r, r ≠ .eax → r ≠ .ecx → s'.gpr r = s.gpr r
  mem : s'.mem = m
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem wp_xor {is : List Instr} {s : State} {Q : State → Prop} {d r : Reg}
    (k : ∀ s', Upd s s' d (s.gpr d ^^^ s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .xor d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (MdStream.X86.Upd.flags _ _ _ _ _ _))

theorem ea_at' (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = addr (s.gpr b) d := rfl

/-- One word. -/
theorem xw_ok {pb qb cb : Reg} {pd qd cd : Nat} {is : List Instr} {s : State} {Q : State → Prop}
    {P Q' C : Addr} (hq : qb ≠ .eax) (hc₁ : cb ≠ .eax) (hc₂ : cb ≠ .ecx)
    (hP : addr (s.gpr pb) pd = P) (hQ : addr (s.gpr qb) qd = Q') (hC : addr (s.gpr cb) cd = C)
    (rP : InRegions (s.rd ++ s.wr) P 4) (rQ : InRegions (s.rd ++ s.wr) Q' 4) (wC : InRegions s.wr C 4)
    (k : ∀ s', VG.Proof.CmacAes.X86.Step s s' (s.mem.writeW C (s.mem.readW P 32 ^^^ s.mem.readW Q' 32)) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov .eax (.mem (at_ pb pd)) :: .mov .ecx (.mem (at_ qb qd)) :: .alu .xor .eax (.reg .ecx) ::
      .store (at_ cb cd) .eax :: is)) s Q := by
  subst hP hQ hC
  refine wp_movm (VG.Proof.CmacAes.X86.ea_at' _ _ _) rP fun s₁ u₁ => ?_
  refine wp_movm (by rw [VG.Proof.CmacAes.X86.ea_at', u₁.other _ hq]) (by rw [u₁.rd, u₁.wr]; exact rQ) fun s₂ u₂ => ?_
  refine VG.Proof.CmacAes.X86.wp_xor fun s₃ u₃ => ?_
  refine wp_store (by rw [VG.Proof.CmacAes.X86.ea_at', u₃.other _ hc₁, u₂.other _ hc₂, u₁.other _ hc₁])
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact wC) fun s₄ u₄ => k s₄ ⟨fun r h₁ h₂ => ?_, ?_, ?_, ?_⟩
  · rw [u₄.gpr, u₃.other _ h₁, u₂.other _ h₂, u₁.other _ h₁]
  · rw [u₄.mem, u₃.gpr, u₂.other _ (by decide), u₂.gpr, u₁.gpr, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]

/-- Word `i` of a block that does not wrap the 32-bit space. -/
theorem addr_word {b : BitVec 32} {d : Nat} (i : Nat) (h : b.toNat + d + 16 ≤ 2 ^ 32) (hi : i ≤ 12) :
    addr b (d + i) = b.setWidth 64 + BitVec.ofNat 64 d + BitVec.ofNat 64 i := by
  rw [addr_eq (by omega), Offset.add_add]

theorem in_word {rs : List Region} {P : Addr} (h : Covers [⟨P, 16⟩] rs) {i : Nat} (hi : i ≤ 12) :
    InRegions rs (P + BitVec.ofNat 64 i) 4 :=
  h _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base P (by omega) (by omega)⟩

theorem in_word0 {rs : List Region} {P : Addr} (h : Covers [⟨P, 16⟩] rs) : InRegions rs P 4 := by
  have c := Offset.contains_base P (d := 0) (n := 4) (k := 16) (by decide) (by decide)
  rw [show P + BitVec.ofNat 64 0 = P from BitVec.add_zero P] at c
  exact h _ _ ⟨_, List.mem_singleton_self _, c⟩

/-- The XOR of the blocks at `pb + pd` and `qb + qd`, stored at `cb + cd`. -/
theorem xor4_ok {pb qb cb : Reg} {pd qd cd : Nat} {is : List Instr} {s : State} {Q : State → Prop}
    (hp₁ : pb ≠ .eax) (hp₂ : pb ≠ .ecx) (hq₁ : qb ≠ .eax) (hq₂ : qb ≠ .ecx) (hc₁ : cb ≠ .eax)
    (hc₂ : cb ≠ .ecx)
    (fp : (s.gpr pb).toNat + pd + 16 ≤ 2 ^ 32) (fq : (s.gpr qb).toNat + qd + 16 ≤ 2 ^ 32)
    (fc : (s.gpr cb).toNat + cd + 16 ≤ 2 ^ 32)
    (rP : Covers [⟨(s.gpr pb).setWidth 64 + BitVec.ofNat 64 pd, 16⟩] (s.rd ++ s.wr))
    (rQ : Covers [⟨(s.gpr qb).setWidth 64 + BitVec.ofNat 64 qd, 16⟩] (s.rd ++ s.wr))
    (wC : Covers [⟨(s.gpr cb).setWidth 64 + BitVec.ofNat 64 cd, 16⟩] s.wr)
    (k : ∀ s', VG.Proof.CmacAes.X86.Step s s' (Proof.Cmac.xor4Mem s.mem ((s.gpr cb).setWidth 64 + BitVec.ofNat 64 cd)
        ((s.gpr pb).setWidth 64 + BitVec.ofNat 64 pd) ((s.gpr qb).setWidth 64 + BitVec.ofNat 64 qd)) →
      WP isa (.block is) s' Q) :
    WP isa (.block (xor4 pb qb cb pd qd cd ++ is)) s Q := by
  rw [VG.Proof.CmacAes.X86.xor4_eq]
  simp only [VG.Proof.CmacAes.X86.xorBlk, List.cons_append, List.nil_append]
  refine VG.Proof.CmacAes.X86.xw_ok hq₁ hc₁ hc₂ (addr_eq (by omega)) (addr_eq (by omega)) (addr_eq (by omega))
    (VG.Proof.CmacAes.X86.in_word0 rP) (VG.Proof.CmacAes.X86.in_word0 rQ) (VG.Proof.CmacAes.X86.in_word0 wC) fun s₁ g₁ => ?_
  have e₁ : ∀ r, r ≠ .eax → r ≠ .ecx → s₁.gpr r = s.gpr r := g₁.gpr
  refine VG.Proof.CmacAes.X86.xw_ok (P := (s.gpr pb).setWidth 64 + BitVec.ofNat 64 pd + BitVec.ofNat 64 4)
    (Q' := (s.gpr qb).setWidth 64 + BitVec.ofNat 64 qd + BitVec.ofNat 64 4)
    (C := (s.gpr cb).setWidth 64 + BitVec.ofNat 64 cd + BitVec.ofNat 64 4) hq₁ hc₁ hc₂
    (by rw [e₁ _ hp₁ hp₂]; exact VG.Proof.CmacAes.X86.addr_word 4 fp (by decide))
    (by rw [e₁ _ hq₁ hq₂]; exact VG.Proof.CmacAes.X86.addr_word 4 fq (by decide))
    (by rw [e₁ _ hc₁ hc₂]; exact VG.Proof.CmacAes.X86.addr_word 4 fc (by decide))
    (by rw [g₁.rd, g₁.wr]; exact VG.Proof.CmacAes.X86.in_word rP (by decide)) (by rw [g₁.rd, g₁.wr]; exact VG.Proof.CmacAes.X86.in_word rQ (by decide))
    (by rw [g₁.wr]; exact VG.Proof.CmacAes.X86.in_word wC (by decide)) fun s₂ g₂ => ?_
  have e₂ : ∀ r, r ≠ .eax → r ≠ .ecx → s₂.gpr r = s.gpr r := fun r h₁ h₂ => by rw [g₂.gpr r h₁ h₂, e₁ r h₁ h₂]
  refine VG.Proof.CmacAes.X86.xw_ok (P := (s.gpr pb).setWidth 64 + BitVec.ofNat 64 pd + BitVec.ofNat 64 8)
    (Q' := (s.gpr qb).setWidth 64 + BitVec.ofNat 64 qd + BitVec.ofNat 64 8)
    (C := (s.gpr cb).setWidth 64 + BitVec.ofNat 64 cd + BitVec.ofNat 64 8) hq₁ hc₁ hc₂
    (by rw [e₂ _ hp₁ hp₂]; exact VG.Proof.CmacAes.X86.addr_word 8 fp (by decide))
    (by rw [e₂ _ hq₁ hq₂]; exact VG.Proof.CmacAes.X86.addr_word 8 fq (by decide))
    (by rw [e₂ _ hc₁ hc₂]; exact VG.Proof.CmacAes.X86.addr_word 8 fc (by decide))
    (by rw [g₂.rd, g₂.wr, g₁.rd, g₁.wr]; exact VG.Proof.CmacAes.X86.in_word rP (by decide))
    (by rw [g₂.rd, g₂.wr, g₁.rd, g₁.wr]; exact VG.Proof.CmacAes.X86.in_word rQ (by decide))
    (by rw [g₂.wr, g₁.wr]; exact VG.Proof.CmacAes.X86.in_word wC (by decide)) fun s₃ g₃ => ?_
  have e₃ : ∀ r, r ≠ .eax → r ≠ .ecx → s₃.gpr r = s.gpr r := fun r h₁ h₂ => by rw [g₃.gpr r h₁ h₂, e₂ r h₁ h₂]
  refine VG.Proof.CmacAes.X86.xw_ok (P := (s.gpr pb).setWidth 64 + BitVec.ofNat 64 pd + BitVec.ofNat 64 12)
    (Q' := (s.gpr qb).setWidth 64 + BitVec.ofNat 64 qd + BitVec.ofNat 64 12)
    (C := (s.gpr cb).setWidth 64 + BitVec.ofNat 64 cd + BitVec.ofNat 64 12) hq₁ hc₁ hc₂
    (by rw [e₃ _ hp₁ hp₂]; exact VG.Proof.CmacAes.X86.addr_word 12 fp (by decide))
    (by rw [e₃ _ hq₁ hq₂]; exact VG.Proof.CmacAes.X86.addr_word 12 fq (by decide))
    (by rw [e₃ _ hc₁ hc₂]; exact VG.Proof.CmacAes.X86.addr_word 12 fc (by decide))
    (by rw [g₃.rd, g₃.wr, g₂.rd, g₂.wr, g₁.rd, g₁.wr]; exact VG.Proof.CmacAes.X86.in_word rP (by decide))
    (by rw [g₃.rd, g₃.wr, g₂.rd, g₂.wr, g₁.rd, g₁.wr]; exact VG.Proof.CmacAes.X86.in_word rQ (by decide))
    (by rw [g₃.wr, g₂.wr, g₁.wr]; exact VG.Proof.CmacAes.X86.in_word wC (by decide)) fun s₄ g₄ => k s₄ ⟨?_, ?_, ?_, ?_⟩
  · intro r h₁ h₂; rw [g₄.gpr r h₁ h₂, e₃ r h₁ h₂]
  · rw [g₄.mem, g₃.mem, g₂.mem, g₁.mem]; rfl
  · rw [g₄.rd, g₃.rd, g₂.rd, g₁.rd]
  · rw [g₄.wr, g₃.wr, g₂.wr, g₁.wr]

/-- The block at `b + d` zeroed (`b` not `eax`). -/
theorem zero4_ok {b : Reg} {d : Nat} {is : List Instr} {s : State} {Q : State → Prop} (hb : b ≠ .eax)
    (fb : (s.gpr b).toNat + d + 16 ≤ 2 ^ 32)
    (wB : Covers [⟨(s.gpr b).setWidth 64 + BitVec.ofNat 64 d, 16⟩] s.wr)
    (k : ∀ s', (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) →
      s'.mem = Proof.Cmac.zero4 s.mem ((s.gpr b).setWidth 64 + BitVec.ofNat 64 d) →
      s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (zero4 b d ++ is)) s Q := by
  rw [VG.Proof.CmacAes.X86.zero4_eq]
  simp only [List.cons_append, List.nil_append]
  refine wp_movi fun s₀ u₀ => ?_
  have b₀ : s₀.gpr b = s.gpr b := u₀.other _ hb
  refine wp_store (a := (s.gpr b).setWidth 64 + BitVec.ofNat 64 d) (by rw [VG.Proof.CmacAes.X86.ea_at', b₀]; exact addr_eq (by omega))
    (by rw [u₀.wr]; exact VG.Proof.CmacAes.X86.in_word0 wB) fun s₁ u₁ => ?_
  refine wp_store (a := (s.gpr b).setWidth 64 + BitVec.ofNat 64 d + BitVec.ofNat 64 4)
    (by rw [VG.Proof.CmacAes.X86.ea_at', u₁.gpr, b₀]; exact VG.Proof.CmacAes.X86.addr_word 4 fb (by decide))
    (by rw [u₁.wr, u₀.wr]; exact VG.Proof.CmacAes.X86.in_word wB (by decide)) fun s₂ u₂ => ?_
  refine wp_store (a := (s.gpr b).setWidth 64 + BitVec.ofNat 64 d + BitVec.ofNat 64 8)
    (by rw [VG.Proof.CmacAes.X86.ea_at', u₂.gpr, u₁.gpr, b₀]; exact VG.Proof.CmacAes.X86.addr_word 8 fb (by decide))
    (by rw [u₂.wr, u₁.wr, u₀.wr]; exact VG.Proof.CmacAes.X86.in_word wB (by decide)) fun s₃ u₃ => ?_
  refine wp_store (a := (s.gpr b).setWidth 64 + BitVec.ofNat 64 d + BitVec.ofNat 64 12)
    (by rw [VG.Proof.CmacAes.X86.ea_at', u₃.gpr, u₂.gpr, u₁.gpr, b₀]; exact VG.Proof.CmacAes.X86.addr_word 12 fb (by decide))
    (by rw [u₃.wr, u₂.wr, u₁.wr, u₀.wr]; exact VG.Proof.CmacAes.X86.in_word wB (by decide)) fun s₄ u₄ => k s₄ ?_ ?_ ?_ ?_
  · intro r hr; rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr, u₀.other _ hr]
  · rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₃.gpr, u₂.gpr, u₁.gpr, u₀.gpr, u₀.mem]; rfl
  · rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd, u₀.rd]
  · rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, u₀.wr]

end VG.Proof.CmacAes.X86

end

section

/-!
# AES-CMAC on x86: calling `vg_aes_ctr32` on one block

`ctr_call`: the frame that pushes `vg_aes_ctr32`'s six arguments (`eax` the
schedule, `ecx` the rounds, `edx` the counter block `C`, `ebx` the data
block `D` holding zeros, `edi = 1` and `ebp` the working space `S`) around
its call: `D` then holds `CIPH_K(C)`, as bytes (`Cmac.aesWith`), and only
`C`, `D`, `S` and the 28 bytes below `esp` change in memory. `ctr_rel`: such
calls are constant time, by `vg_aes_ctr32`'s own proof.
-/

namespace VG.Proof.CmacAes.X86

open VG VG.X86 VG.Impl.CmacAes.X86
open VG.Proof.Aes.X86 (Ctr32Impl)

variable (v : Ctr32Impl)

theorem ofBytes_zeros : Spec.Gcm.ofBytes (Spec.Cmac.zeros 16) = 0 := by decide

theorem toNat_rounds {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) : (BitVec.ofNat 32 R).toNat = R := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)

theorem ctr_nosp : NoSp v.callee.code := v.nosp

theorem ctr_stack : stackUse v.callee.code = 0 := v.stack

/-- The registers the call pushes, as `vg_aes_ctr32`'s arguments. -/
abbrev ctrRegs : List Reg := [.ebp, .edi, .ebx, .edx, .ecx, .eax]

/-- What a call of `vg_aes_ctr32` on one block needs. -/
structure CtrPre (s : State) (W C D S : BitVec 32) (R : Nat) : Prop where
  eax : s.gpr .eax = W
  ecx : s.gpr .ecx = BitVec.ofNat 32 R
  edx : s.gpr .edx = C
  ebx : s.gpr .ebx = D
  edi : s.gpr .edi = 1
  ebp : s.gpr .ebp = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  esp : 28 ≤ (s.gpr .esp).toNat
  wc : (⟨W.setWidth 64, 240⟩ : Region).Disjoint ⟨C.setWidth 64, 16⟩
  wd : (⟨W.setWidth 64, 240⟩ : Region).Disjoint ⟨D.setWidth 64, 16⟩
  ws : (⟨W.setWidth 64, 240⟩ : Region).Disjoint ⟨S.setWidth 64, 2048⟩
  cd : (⟨C.setWidth 64, 16⟩ : Region).Disjoint ⟨D.setWidth 64, 16⟩
  cs : (⟨C.setWidth 64, 16⟩ : Region).Disjoint ⟨S.setWidth 64, 2048⟩
  ds : (⟨D.setWidth 64, 16⟩ : Region).Disjoint ⟨S.setWidth 64, 2048⟩
  bw : (below (s.gpr .esp) 28).Disjoint ⟨W.setWidth 64, 240⟩
  bc : (below (s.gpr .esp) 28).Disjoint ⟨C.setWidth 64, 16⟩
  bd : (below (s.gpr .esp) 28).Disjoint ⟨D.setWidth 64, 16⟩
  bs : (below (s.gpr .esp) 28).Disjoint ⟨S.setWidth 64, 2048⟩
  hW : W.toNat + 240 ≤ 2 ^ 32
  hC : C.toNat + 16 ≤ 2 ^ 32
  hD : D.toNat + 16 ≤ 2 ^ 32
  hS : S.toNat + 2048 ≤ 2 ^ 32
  reads : Covers [⟨W.setWidth 64, 240⟩] (s.rd ++ s.wr)
  writes : Covers [⟨C.setWidth 64, 16⟩, ⟨D.setWidth 64, 16⟩, ⟨S.setWidth 64, 2048⟩] s.wr
  zero : Spec.Aes.bytesAt s.mem (D.setWidth 64) 16 = Spec.Cmac.zeros 16

/-- What a call of `vg_aes_ctr32` on one block leaves. -/
structure CtrPost (s : State) (W C D S : BitVec 32) (R : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨C.setWidth 64, 16⟩, ⟨D.setWidth 64, 16⟩, ⟨S.setWidth 64, 2048⟩, below (s.gpr .esp) 28]
    s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem (D.setWidth 64) 16 =
    Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem (W.setWidth 64) (16 * (R + 1)))
      (Spec.Aes.bytesAt s.mem (C.setWidth 64) 16)

/-- The regions `vg_aes_ctr32` is called with. -/
abbrev ctrRd (E W : BitVec 32) : List Region := [⟨W.setWidth 64, 240⟩, ⟨(E - BitVec.ofNat 32 24).setWidth 64, 24⟩]
abbrev ctrWr (C D S : BitVec 32) : List Region :=
  [⟨C.setWidth 64, 16⟩, ⟨D.setWidth 64, 16⟩, ⟨S.setWidth 64, 2048⟩]

theorem hrs : Reg.esp ∉ VG.Proof.CmacAes.X86.ctrRegs := by decide

namespace CtrPre
variable {s : State} {W C D S : BitVec 32} {R : Nat} (h : VG.Proof.CmacAes.X86.CtrPre s W C D S R)
include h

theorem fit : 4 * ctrRegs.length + 4 ≤ (s.gpr .esp).toNat := by
  have := h.esp; simp only [List.length_cons, List.length_nil]; omega

theorem args : VG.X86.arg (pushed VG.Proof.CmacAes.X86.ctrRegs s).callEntry 0 = W ∧ VG.X86.arg (pushed VG.Proof.CmacAes.X86.ctrRegs s).callEntry 1 = BitVec.ofNat 32 R ∧
    VG.X86.arg (pushed VG.Proof.CmacAes.X86.ctrRegs s).callEntry 2 = C ∧ VG.X86.arg (pushed VG.Proof.CmacAes.X86.ctrRegs s).callEntry 3 = D ∧
    VG.X86.arg (pushed VG.Proof.CmacAes.X86.ctrRegs s).callEntry 4 = 1 ∧ VG.X86.arg (pushed VG.Proof.CmacAes.X86.ctrRegs s).callEntry 5 = S := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  rw [callEntry_arg h.fit VG.Proof.CmacAes.X86.hrs (by decide)] <;> simp [h.eax, h.ecx, h.edx, h.ebx, h.edi, h.ebp]

theorem sub24 : Region.Sub (below (s.gpr .esp) 24) (below (s.gpr .esp) 28) := below_sub (by omega) h.esp

theorem sub4 : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 28).setWidth 64, 4⟩ (below (s.gpr .esp) 28) := by
  have := below_inner (sp := s.gpr .esp) (a := 4) (b := 28) (k := 24) (by omega) h.esp
  rw [show s.gpr .esp - BitVec.ofNat 32 28 = s.gpr .esp - BitVec.ofNat 32 24 - BitVec.ofNat 32 4 by
    rw [← VG.Offset.sub_add_eq]; rfl]
  exact this

theorem callPre : CallPre Proof.Aes.ctr32X86 VG.Proof.CmacAes.X86.ctrRegs (VG.Proof.CmacAes.X86.ctrRd (s.gpr .esp) W) (VG.Proof.CmacAes.X86.ctrWr C D S) s := by
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := h.args
  have hR := VG.Proof.CmacAes.X86.toNat_rounds h.rounds
  have eA : argAddr (pushed VG.Proof.CmacAes.X86.ctrRegs s).callEntry 0 = (s.gpr .esp - BitVec.ofNat 32 24).setWidth 64 := by
    rw [callEntry_argAddr0]; rfl
  have eSp : (pushed VG.Proof.CmacAes.X86.ctrRegs s).callEntry.gpr .esp = s.gpr .esp - BitVec.ofNat 32 28 := by
    rw [callEntry_esp']; rfl
  refine ⟨?_, ?_, ?_⟩
  · simp only [Proof.Aes.ctr32X86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, a4, a5, eA, eSp, hR,
      show (1 : BitVec 32).toNat = 1 from rfl, Nat.mul_one]
    refine ⟨trivial, trivial, h.wc, h.wd, h.ws, h.cd, h.cs, h.ds, (h.bc.sub_left h.sub24).symm.symm,
      (h.bd.sub_left h.sub24), (h.bs.sub_left h.sub24), h.bc.sub_left h.sub4, h.bd.sub_left h.sub4,
      h.bs.sub_left h.sub4, h.hW, h.hC, h.hD, h.hS, ?_, h.rounds⟩
    rw [sub_toNat (by have := h.esp; omega)]; have := (s.gpr .esp).isLt; omega
  · intro a n ⟨r, hr, hcn⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · obtain ⟨r', hr', hc'⟩ := h.reads a n ⟨_, List.mem_singleton_self _, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', hr', hc'⟩)
    · exact InRegions_append_cons.mpr (.inl hcn)
    all_goals
      obtain ⟨r', hr', hc'⟩ := h.writes a n ⟨_, by simp, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', List.mem_append_right _ hr', hc'⟩)
  · intro a n hi
    obtain ⟨r', hr', hc'⟩ := h.writes a n hi
    exact ⟨r', List.mem_cons_of_mem _ hr', hc'⟩

end CtrPre

theorem ctr_call {s : State} {W C D S : BitVec 32} {R : Nat} (h : VG.Proof.CmacAes.X86.CtrPre s W C D S R) :
    WP isa (ctrCall v.callee) s (VG.Proof.CmacAes.X86.CtrPost s W C D S R) := by
  have hR := VG.Proof.CmacAes.X86.toNat_rounds h.rounds
  have hR' : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h' | h' | h' <;> omega
  unfold ctrCall
  refine WP.callWith (rs := VG.Proof.CmacAes.X86.ctrRegs) (k := Proof.Aes.ctr32X86) v.ok v.nosp (by decide) VG.Proof.CmacAes.X86.hrs
    (by rw [v.stack]; have := h.esp; simp only [List.length_cons, List.length_nil]; omega) h.callPre
    fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := h.args
  rw [v.stack] at f'
  have fE := callEntry_frame h.fit VG.Proof.CmacAes.X86.hrs
  rw [show 4 * ctrRegs.length + 4 = 28 from rfl] at fE
  have keep : ∀ {p : BitVec 32} {n k : Nat}, (below (s.gpr .esp) 28).Disjoint ⟨p.setWidth 64, n⟩ → k ≤ n →
      n ≤ 240 →
      Spec.Aes.bytesAt (pushed VG.Proof.CmacAes.X86.ctrRegs s).callEntry.mem (p.setWidth 64) k = Spec.Aes.bytesAt s.mem (p.setWidth 64) k :=
    fun hd hk hn => Proof.Cmac.bytesAt_frame fE (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hd.sub_right (Region.sub_prefix hk)).symm) (by omega)
  obtain ⟨hdata, -⟩ := post
  simp only [arg_withRegions, State.withRegions_mem, a0, a1, a2, a3, a4, hR,
    show (1 : BitVec 32).toNat = 1 from rfl, m₂] at hdata
  have one : ∀ m : Mem, Spec.Gcm.blocksAt m (D.setWidth 64) 1 = [Spec.Gcm.blockAt m (D.setWidth 64)] :=
    fun m => by simp [Spec.Gcm.blocksAt]
  have bD : Spec.Gcm.blockAt (pushed VG.Proof.CmacAes.X86.ctrRegs s).callEntry.mem (D.setWidth 64) = 0 := by
    rw [Spec.Gcm.blockAt, keep h.bd (Nat.le_refl _) (by decide), h.zero, VG.Proof.CmacAes.X86.ofBytes_zeros]
  rw [one, one, bD, Proof.Cmac.ctr32_one, List.cons.injEq] at hdata
  refine ⟨rd', wr', cs', ?_, ?_⟩
  · exact f'.mono fun r hr => by simp only [List.cons_append, List.nil_append] at hr; simpa using hr
  · rw [Proof.Cmac.bytesAt_blockAt, hdata.1, Spec.Gcm.blockAt, keep h.bw hR' (Nat.le_refl _), keep h.bc (Nat.le_refl _) (by decide),
      Proof.Cmac.aesWith_bytes _ _ (Proof.Cmac.bytesAt_length _ _ _)]

/-- Calls of `vg_aes_ctr32` on one block, with the same arguments and stack
pointer in both runs, are constant time. -/
theorem ctr_rel {W C D S E : BitVec 32} {R : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → VG.Proof.CmacAes.X86.CtrPre s₁ W C D S R ∧ VG.Proof.CmacAes.X86.CtrPre s₂ W C D S R ∧ s₁.gpr .esp = E ∧ s₂.gpr .esp = E) :
    RelCT isa P (ctrCall v.callee) fun _ _ => True := by
  refine RelCT.callWith v.ok v.ct (VG.Proof.CmacAes.X86.ctrRd E W) (VG.Proof.CmacAes.X86.ctrWr C D S)
    fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, e₁, e₂⟩ := h s₁ s₂ hp
  have p₁ := h₁.callPre
  have p₂ := h₂.callPre
  rw [e₁] at p₁
  rw [e₂] at p₂
  refine ⟨p₁, p₂, e₁.trans e₂.symm, ?_⟩
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := h₁.args
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := h₂.args
  refine ⟨by simp only [State.withRegions_gpr, callEntry_esp', e₁, e₂], fun i hi => ?_⟩
  simp only [arg_withRegions]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [a0, b0]
  · rw [a1, b1]
  · rw [a2, b2]
  · rw [a3, b3]
  · rw [a4, b4]
  · rw [a5, b5]

end VG.Proof.CmacAes.X86

end

/-!
# AES-CMAC on x86: saving registers and reading the stack arguments

The registers saved in the scratch buffer (`Spill`, with their slots), and
weakest preconditions of instructions with a stack argument as their source
(`wp_arg`, `wp_addArg`).
-/

namespace VG.Proof.CmacAes.X86

open VG VG.X86 VG.Impl.CmacAes.X86
open VG.Proof.MdStream.X86 (Upd Mupd WP.cons wp_movm wp_store)

theorem saved_fits : Spill.Fits 2080 saved := by decide

theorem saved_bound : ∀ p ∈ saved, 2064 ≤ p.2 ∧ p.2 + 4 ≤ 2080 := by decide

theorem saved_ne_eax : ∀ p ∈ saved, p.1 ≠ .eax := by decide

theorem save_eq : save = Spill.saveCode .eax saved := rfl

theorem restore_eq (i : Nat) : restore i = .mov .eax (argOp i) :: (Spill.restoreCode .eax saved ++ []) := rfl

/-- Each slot of `saved` holds the register saved there. -/
theorem saveMem_slot (m : Mem) (B : Addr) (g : Reg → BitVec 32) {r : Reg} {d : Nat} (h : (r, d) ∈ saved) :
    (Spill.saveMem m (B + BitVec.ofNat 64 ·) g saved).readW (B + BitVec.ofNat 64 d) 32 = g r :=
  Spill.saveMem_saved_ofNat m B g VG.Proof.CmacAes.X86.saved_fits (by decide) (r, d) h

/-! ## The stack arguments -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `mov d, [esp + 4 + 4 i]`, the stack argument `i` of the entry state `s₀`. -/
theorem wp_arg {d : Reg} {i : Nat} {s₀ : State} (hesp : s.gpr .esp = s₀.gpr .esp)
    (hin : InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4) (hv : s.mem.readW (argAddr s₀ i) 32 = VG.X86.arg s₀ i)
    (k : ∀ s', Upd s s' d (VG.X86.arg s₀ i) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (argOp i) :: is)) s Q :=
  wp_movm (by rw [VG.Proof.CmacAes.X86.ea_at', hesp]; rfl) hin fun s' u => k s' (hv ▸ u)

/-- `add d, [esp + 4 + 4 i]`. -/
theorem wp_addArg {d : Reg} {i : Nat} {s₀ : State} (hesp : s.gpr .esp = s₀.gpr .esp)
    (hin : InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4) (hv : s.mem.readW (argAddr s₀ i) 32 = VG.X86.arg s₀ i)
    (k : ∀ s', Upd s s' d (s.gpr d + VG.X86.arg s₀ i) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (argOp i) :: is)) s Q := by
  refine WP.cons (s' := (VG.X86.arithFlags s (s.gpr d + VG.X86.arg s₀ i)
    (2 ^ 32 ≤ (s.gpr d).toNat + (VG.X86.arg s₀ i).toNat) (addOverflow (s.gpr d) (VG.X86.arg s₀ i) (s.gpr d + VG.X86.arg s₀ i))).setReg d
      (s.gpr d + VG.X86.arg s₀ i)) ?_ (k _ (MdStream.X86.Upd.flags _ _ _ _ _ _))
  have ea : s.ea (at_ .esp (4 + 4 * i)) = argAddr s₀ i := by rw [VG.Proof.CmacAes.X86.ea_at', hesp]; rfl
  simp [exec, execAlu, readSrc, argOp, State.load32, ea, hin, hv]

end

end VG.Proof.CmacAes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.X86.UpdateLoop`. -/
section

section

/-!
# AES-CMAC on x86: `vg_cmac_aes_update`, the blocks before and in the loop

The invariant after `k` blocks (`LInv`): `esi` points at the next block, `esp`
is unchanged, only the state, the first 2064 bytes of the scratch buffer and
the 28 bytes below `esp` have changed since the registers were saved, and the
state is the chaining value after the first `k` blocks. Everything else is
reloaded from the stack arguments, which nothing writes.
-/

namespace VG.Proof.CmacAes.X86

open VG VG.X86 VG.Impl.CmacAes.X86
open VG.Proof.MdStream.X86 (Upd Mupd Fupd wp_mov wp_movi wp_addi wp_add wp_cmp wp_test)

section
variable (s₀ : State)

abbrev E : BitVec 32 := s₀.gpr .esp
abbrev W : BitVec 32 := VG.X86.arg s₀ 0
abbrev R : Nat := (VG.X86.arg s₀ 1).toNat
abbrev St : BitVec 32 := VG.X86.arg s₀ 2
abbrev Dp : BitVec 32 := VG.X86.arg s₀ 3
abbrev N : Nat := (VG.X86.arg s₀ 4).toNat
abbrev S : BitVec 32 := VG.X86.arg s₀ 5

abbrev schR : Region := ⟨(VG.Proof.CmacAes.X86.W s₀).setWidth 64, 240⟩
abbrev stR : Region := ⟨(VG.Proof.CmacAes.X86.St s₀).setWidth 64, 16⟩
abbrev dataR : Region := ⟨(VG.Proof.CmacAes.X86.Dp s₀).setWidth 64, 16 * VG.Proof.CmacAes.X86.N s₀⟩
abbrev scrR : Region := ⟨(VG.Proof.CmacAes.X86.S s₀).setWidth 64, 2176⟩
abbrev argsR : Region := ⟨argAddr s₀ 0, 24⟩
abbrev retR : Region := ⟨(VG.Proof.CmacAes.X86.E s₀).setWidth 64, 4⟩
abbrev stkR : Region := ⟨(VG.Proof.CmacAes.X86.E s₀).setWidth 64 - BitVec.ofNat 64 28, 28⟩

/-- The cipher. -/
abbrev ciph : Spec.Cmac.Cipher := VG.Proof.CmacAes.X86.ciphAt s₀.mem ((VG.Proof.CmacAes.X86.W s₀).setWidth 64) (VG.Proof.CmacAes.X86.R s₀)

/-- The message blocks. -/
abbrev blks : List (List Byte) := Spec.Cmac.blocksAt s₀.mem ((VG.Proof.CmacAes.X86.Dp s₀).setWidth 64) 16 (VG.Proof.CmacAes.X86.N s₀)

/-- The memory after saving the registers in the scratch buffer. -/
def savedMem : Mem := Spill.saveMem s₀.mem ((VG.Proof.CmacAes.X86.S s₀).setWidth 64 + BitVec.ofNat 64 ·) s₀.gpr saved

end

/-- The precondition, by name. -/
structure UPre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.CmacAes.X86.schR s₀, VG.Proof.CmacAes.X86.dataR s₀, VG.Proof.CmacAes.X86.argsR s₀]
  wr : s₀.wr = [VG.Proof.CmacAes.X86.stR s₀, VG.Proof.CmacAes.X86.scrR s₀]
  sch_st : (VG.Proof.CmacAes.X86.schR s₀).Disjoint (VG.Proof.CmacAes.X86.stR s₀)
  sch_scr : (VG.Proof.CmacAes.X86.schR s₀).Disjoint (VG.Proof.CmacAes.X86.scrR s₀)
  data_st : (VG.Proof.CmacAes.X86.dataR s₀).Disjoint (VG.Proof.CmacAes.X86.stR s₀)
  data_scr : (VG.Proof.CmacAes.X86.dataR s₀).Disjoint (VG.Proof.CmacAes.X86.scrR s₀)
  st_scr : (VG.Proof.CmacAes.X86.stR s₀).Disjoint (VG.Proof.CmacAes.X86.scrR s₀)
  args_st : (VG.Proof.CmacAes.X86.argsR s₀).Disjoint (VG.Proof.CmacAes.X86.stR s₀)
  args_scr : (VG.Proof.CmacAes.X86.argsR s₀).Disjoint (VG.Proof.CmacAes.X86.scrR s₀)
  ret_st : (VG.Proof.CmacAes.X86.retR s₀).Disjoint (VG.Proof.CmacAes.X86.stR s₀)
  ret_scr : (VG.Proof.CmacAes.X86.retR s₀).Disjoint (VG.Proof.CmacAes.X86.scrR s₀)
  b_sch : (VG.Proof.CmacAes.X86.stkR s₀).Disjoint (VG.Proof.CmacAes.X86.schR s₀)
  b_data : (VG.Proof.CmacAes.X86.stkR s₀).Disjoint (VG.Proof.CmacAes.X86.dataR s₀)
  b_st : (VG.Proof.CmacAes.X86.stkR s₀).Disjoint (VG.Proof.CmacAes.X86.stR s₀)
  b_scr : (VG.Proof.CmacAes.X86.stkR s₀).Disjoint (VG.Proof.CmacAes.X86.scrR s₀)
  sch_fit : (VG.Proof.CmacAes.X86.W s₀).toNat + 240 ≤ 2 ^ 32
  st_fit : (VG.Proof.CmacAes.X86.St s₀).toNat + 16 ≤ 2 ^ 32
  data_fit : (VG.Proof.CmacAes.X86.Dp s₀).toNat + 16 * VG.Proof.CmacAes.X86.N s₀ ≤ 2 ^ 32
  scr_fit : (VG.Proof.CmacAes.X86.S s₀).toNat + 2176 ≤ 2 ^ 32
  esp28 : 28 ≤ (VG.Proof.CmacAes.X86.E s₀).toNat
  esp_fit : (VG.Proof.CmacAes.X86.E s₀).toNat + 28 ≤ 2 ^ 32
  rounds : VG.Proof.CmacAes.X86.R s₀ = 10 ∨ VG.Proof.CmacAes.X86.R s₀ = 12 ∨ VG.Proof.CmacAes.X86.R s₀ = 14

theorem UPre.of {s₀ : State} (h : updateX86.pre s₀) : VG.Proof.CmacAes.X86.UPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t, u, v, w⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t, u, v, w⟩

/-- The loop invariant, after `k` blocks. -/
structure LInv (s₀ : State) (k : Nat) (s : State) : Prop where
  esi : s.gpr .esi = VG.Proof.CmacAes.X86.Dp s₀ + BitVec.ofNat 32 (16 * k)
  esp : s.gpr .esp = VG.Proof.CmacAes.X86.E s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [VG.Proof.CmacAes.X86.stR s₀, ⟨(VG.Proof.CmacAes.X86.S s₀).setWidth 64, 2064⟩, VG.Proof.CmacAes.X86.stkR s₀] (VG.Proof.CmacAes.X86.savedMem s₀) s.mem
  state : Spec.Aes.bytesAt s.mem ((VG.Proof.CmacAes.X86.St s₀).setWidth 64) 16 =
    Spec.Cmac.chain (VG.Proof.CmacAes.X86.ciph s₀) (Spec.Aes.bytesAt s₀.mem ((VG.Proof.CmacAes.X86.St s₀).setWidth 64) 16) ((VG.Proof.CmacAes.X86.blks s₀).take k)

/-! ## Addresses and regions -/

theorem add0 (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

theorem add0' (p : BitVec 32) : p + BitVec.ofNat 32 0 = p := BitVec.add_zero p

/-- The regions the function writes, with the stack below it. -/
abbrev Big (s₀ : State) : List Region := [VG.Proof.CmacAes.X86.stR s₀, VG.Proof.CmacAes.X86.scrR s₀, VG.Proof.CmacAes.X86.stkR s₀]

section
variable {s₀ : State} (hp : VG.Proof.CmacAes.X86.UPre s₀)
include hp

theorem UPre.below_eq : below (VG.Proof.CmacAes.X86.E s₀) 28 = VG.Proof.CmacAes.X86.stkR s₀ := by
  simp only [below]; rw [Taint.sub_setWidth hp.esp28]

theorem UPre.argA {i : Nat} (hi : i < 6) : argAddr s₀ i = argAddr s₀ 0 + BitVec.ofNat 64 (4 * i) := by
  have : (s₀.gpr .esp).toNat + 28 ≤ 2 ^ 32 := hp.esp_fit
  simp only [argAddr]
  rw [show (s₀.gpr .esp + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 = addr (s₀.gpr .esp) (4 + 4 * i) from rfl,
    show (s₀.gpr .esp + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 = addr (s₀.gpr .esp) (4 + 4 * 0) from rfl,
    addr_eq (by omega), addr_eq (by omega), Offset.add_add]

theorem UPre.arg_sub {i : Nat} (hi : i < 6) : Region.Sub ⟨argAddr s₀ i, 4⟩ (VG.Proof.CmacAes.X86.argsR s₀) := by
  rw [hp.argA hi]; exact Offset.sub_base _ (by omega)

theorem UPre.arg_in {i : Nat} (hi : i < 6) : InRegions (s₀.rd ++ s₀.wr) (argAddr s₀ i) 4 := by
  refine ⟨VG.Proof.CmacAes.X86.argsR s₀, by simp [hp.rd], ?_⟩
  rw [hp.argA hi]; exact Offset.contains_base _ (by omega) (by omega)

theorem UPre.args_stk : (VG.Proof.CmacAes.X86.argsR s₀).Disjoint (VG.Proof.CmacAes.X86.stkR s₀) := by
  have : (s₀.gpr .esp).toNat + 28 ≤ 2 ^ 32 := hp.esp_fit
  have e : argAddr s₀ 0 = (VG.Proof.CmacAes.X86.E s₀).setWidth 64 + BitVec.ofNat 64 4 := addr_eq (by omega)
  show Region.Disjoint ⟨argAddr s₀ 0, 24⟩ _
  rw [e]; exact (Offset.disjoint_below_above _ (by decide)).symm

/-- The stack arguments are unchanged where only `Big` changes. -/
theorem UPre.arg_keep {m : Mem} (hf : Frame (VG.Proof.CmacAes.X86.Big s₀) s₀.mem m) {i : Nat} (hi : i < 6) :
    m.readW (argAddr s₀ i) 32 = VG.X86.arg s₀ i :=
  hf.readW (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.args_st.sub_left (hp.arg_sub hi)
    · exact hp.args_scr.sub_left (hp.arg_sub hi)
    · exact hp.args_stk.sub_left (hp.arg_sub hi)) (by decide)

theorem UPre.dataA {k : Nat} (hk : k < VG.Proof.CmacAes.X86.N s₀) :
    addr (VG.Proof.CmacAes.X86.Dp s₀) (16 * k) = (VG.Proof.CmacAes.X86.Dp s₀).setWidth 64 + BitVec.ofNat 64 (16 * k) :=
  addr_eq (by have := hp.data_fit; omega)

theorem UPre.dataN {k : Nat} (hk : k < VG.Proof.CmacAes.X86.N s₀) :
    (VG.Proof.CmacAes.X86.Dp s₀ + BitVec.ofNat 32 (16 * k)).toNat = (VG.Proof.CmacAes.X86.Dp s₀).toNat + 16 * k := by
  have := hp.data_fit
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * k) (by omega),
    Nat.mod_eq_of_lt (by omega)]

theorem UPre.scrN {d : Nat} (hd : d < 2176) : (VG.Proof.CmacAes.X86.S s₀ + BitVec.ofNat 32 d).toNat = (VG.Proof.CmacAes.X86.S s₀).toNat + d := by
  have := hp.scr_fit
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem UPre.scrA {d : Nat} (hd : d < 2176) :
    (VG.Proof.CmacAes.X86.S s₀ + BitVec.ofNat 32 d).setWidth 64 = (VG.Proof.CmacAes.X86.S s₀).setWidth 64 + BitVec.ofNat 64 d :=
  addr_eq (by have := hp.scr_fit; omega)

end

theorem UPre.scr_sub {s₀ : State} {d n : Nat} (h : d + n ≤ 2176) :
    Region.Sub ⟨(VG.Proof.CmacAes.X86.S s₀).setWidth 64 + BitVec.ofNat 64 d, n⟩ (VG.Proof.CmacAes.X86.scrR s₀) :=
  Offset.sub_base _ h

theorem UPre.data_sub {s₀ : State} {k : Nat} (hk : k < VG.Proof.CmacAes.X86.N s₀) :
    Region.Sub ⟨(VG.Proof.CmacAes.X86.Dp s₀).setWidth 64 + BitVec.ofNat 64 (16 * k), 16⟩ (VG.Proof.CmacAes.X86.dataR s₀) :=
  Offset.sub_base _ (by omega)

theorem savedMem_frame (s₀ : State) : Frame [VG.Proof.CmacAes.X86.scrR s₀] s₀.mem (VG.Proof.CmacAes.X86.savedMem s₀) :=
  Spill.saveMem_frame List.mem_cons_self _ _ _ _ fun p hp =>
    have := VG.Proof.CmacAes.X86.saved_bound p hp; Offset.contains_base _ (by omega) (by omega)

theorem savedMem_slot (s₀ : State) {r : Reg} {d : Nat} (h : (r, d) ∈ saved) :
    (VG.Proof.CmacAes.X86.savedMem s₀).readW ((VG.Proof.CmacAes.X86.S s₀).setWidth 64 + BitVec.ofNat 64 d) 32 = s₀.gpr r :=
  VG.Proof.CmacAes.X86.saveMem_slot _ _ _ h

/-- `savedMem` changes only `Big`. -/
theorem savedMem_big (s₀ : State) : Frame (VG.Proof.CmacAes.X86.Big s₀) s₀.mem (VG.Proof.CmacAes.X86.savedMem s₀) :=
  (VG.Proof.CmacAes.X86.savedMem_frame s₀).mono (by simp)

/-! ## The prologue -/

theorem setup_eq : setup = .mov .eax (argOp 5) :: (saved.map (fun p => Instr.store (at_ .eax p.2) p.1) ++
    ([.mov .esi (argOp 3), .mov .eax (argOp 4), .alu .test .eax (.reg .eax)] : List Instr)) := rfl

theorem ofNat_and_self_beq {k : Nat} (h : k < 2 ^ 32) : (BitVec.ofNat 32 k &&& BitVec.ofNat 32 k == 0) = decide (k = 0) := by
  rw [BitVec.and_self]; exact MdStream.X86.ofNat_beq_zero h

theorem arg_ofNat (s₀ : State) (i : Nat) : VG.X86.arg s₀ i = BitVec.ofNat 32 (VG.X86.arg s₀ i).toNat := by simp

theorem prologue_wp {s₀ : State} (hp : VG.Proof.CmacAes.X86.UPre s₀) :
    WP isa (.block setup) s₀ fun s => VG.Proof.CmacAes.X86.LInv s₀ 0 s ∧ s.zf = some (decide (VG.Proof.CmacAes.X86.N s₀ = 0)) := by
  have hsc := hp.scr_fit
  rw [VG.Proof.CmacAes.X86.setup_eq]
  refine VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀) rfl (hp.arg_in (by decide)) rfl fun s₁ u₁ => ?_
  have h₁ : s₁.gpr .eax = VG.Proof.CmacAes.X86.S s₀ := u₁.gpr
  refine Spill.save_ofNat_ok saved VG.Proof.CmacAes.X86.saved_fits (by rw [h₁]; omega) (fun p hp' => ?_) fun s₂ u₂ => ?_
  · have hb := VG.Proof.CmacAes.X86.saved_bound p hp'
    rw [h₁, u₁.wr, hp.wr]
    exact ⟨VG.Proof.CmacAes.X86.scrR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hm₂ : s₂.mem = VG.Proof.CmacAes.X86.savedMem s₀ := by
    rw [u₂.mem, u₁.mem, h₁, VG.Proof.CmacAes.X86.savedMem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p hp' => u₁.other _ (VG.Proof.CmacAes.X86.saved_ne_eax p hp')
  have esp₂ : s₂.gpr .esp = s₀.gpr .esp := by rw [u₂.gpr, u₁.other _ (by decide)]
  have rw₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]
  refine VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀) esp₂ (by rw [rw₂]; exact hp.arg_in (by decide))
    (by rw [hm₂]; exact hp.arg_keep (VG.Proof.CmacAes.X86.savedMem_big s₀) (by decide)) fun s₃ u₃ => ?_
  refine VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀) (by rw [u₃.other _ (by decide), esp₂])
    (by rw [u₃.rd, u₃.wr, rw₂]; exact hp.arg_in (by decide))
    (by rw [u₃.mem, hm₂]; exact hp.arg_keep (VG.Proof.CmacAes.X86.savedMem_big s₀) (by decide)) fun s₄ u₄ => ?_
  refine wp_test fun s₅ f₅ z₅ => WP.block_nil ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [f₅.gpr, u₄.other _ (by decide), u₃.gpr, Nat.mul_zero, VG.Proof.CmacAes.X86.add0']
  · rw [f₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), esp₂]
  · rw [f₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [f₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [f₅.mem, u₄.mem, u₃.mem, hm₂]; exact Frame.refl _ _
  · rw [f₅.mem, u₄.mem, u₃.mem, hm₂, Proof.Cmac.bytesAt_frame16 (VG.Proof.CmacAes.X86.savedMem_frame s₀) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.st_scr)]
    rfl
  · rw [z₅, u₄.gpr, VG.Proof.CmacAes.X86.arg_ofNat s₀ 4, VG.Proof.CmacAes.X86.ofNat_and_self_beq (VG.X86.arg s₀ 4).isLt]

end VG.Proof.CmacAes.X86

end

/-!
# AES-CMAC on x86: the loop of `vg_cmac_aes_update`

One block keeps the loop invariant (`body_ok`): the counter block is `C ⊕ Mᵢ`
and the state is zeroed (`Cmac.chainMem4`), the call of `vg_aes_ctr32` leaves
`CIPH_K(C ⊕ Mᵢ)` in the state, and ZF is set once `esi` reaches `data + 16 n`
(`adv_zf`).
-/

namespace VG.Proof.CmacAes.X86

open VG VG.X86 VG.Impl.CmacAes.X86
open VG.Proof.Aes.X86 (Ctr32Impl)

variable (v : Ctr32Impl)
open VG.Proof.MdStream.X86 (Upd Mupd Fupd wp_mov wp_movi wp_addi wp_add wp_cmp eval_ne)

theorem take_succ_blks (s₀ : State) {k : Nat} (hk : k < VG.Proof.CmacAes.X86.N s₀) :
    (VG.Proof.CmacAes.X86.blks s₀).take (k + 1) =
      (VG.Proof.CmacAes.X86.blks s₀).take k ++ [Spec.Aes.bytesAt s₀.mem ((VG.Proof.CmacAes.X86.Dp s₀).setWidth 64 + BitVec.ofNat 64 (16 * k)) 16] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simp [Spec.Cmac.blocksAt]; omega)]
  simp [Spec.Cmac.blocksAt]

/-! ## Memory outside the writable regions -/

section
variable {s₀ : State} (hp : VG.Proof.CmacAes.X86.UPre s₀)
include hp

theorem UPre.sched_bytes {m : Mem} (hf : Frame (VG.Proof.CmacAes.X86.Big s₀) s₀.mem m) :
    Spec.Aes.bytesAt m ((VG.Proof.CmacAes.X86.W s₀).setWidth 64) (16 * (VG.Proof.CmacAes.X86.R s₀ + 1)) =
      Spec.Aes.bytesAt s₀.mem ((VG.Proof.CmacAes.X86.W s₀).setWidth 64) (16 * (VG.Proof.CmacAes.X86.R s₀ + 1)) := by
  have hR : 16 * (VG.Proof.CmacAes.X86.R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega
  refine Proof.Cmac.bytesAt_frame hf (fun r hr => ?_) (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.sch_st.sub_left (Region.sub_prefix hR)
  · exact hp.sch_scr.sub_left (Region.sub_prefix hR)
  · exact hp.b_sch.symm.sub_left (Region.sub_prefix hR)

theorem UPre.block_bytes {m : Mem} (hf : Frame (VG.Proof.CmacAes.X86.Big s₀) s₀.mem m) {k : Nat} (hk : k < VG.Proof.CmacAes.X86.N s₀) :
    Spec.Aes.bytesAt m ((VG.Proof.CmacAes.X86.Dp s₀).setWidth 64 + BitVec.ofNat 64 (16 * k)) 16 =
      Spec.Aes.bytesAt s₀.mem ((VG.Proof.CmacAes.X86.Dp s₀).setWidth 64 + BitVec.ofNat 64 (16 * k)) 16 := by
  refine Proof.Cmac.bytesAt_frame hf (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.data_st.sub_left (UPre.data_sub hk)
  · exact hp.data_scr.sub_left (UPre.data_sub hk)
  · exact hp.b_data.symm.sub_left (UPre.data_sub hk)

end

theorem UPre.big_of {s₀ : State} {m : Mem}
    (hf : Frame [VG.Proof.CmacAes.X86.stR s₀, ⟨(VG.Proof.CmacAes.X86.S s₀).setWidth 64, 2064⟩, VG.Proof.CmacAes.X86.stkR s₀] (VG.Proof.CmacAes.X86.savedMem s₀) m) : Frame (VG.Proof.CmacAes.X86.Big s₀) s₀.mem m :=
  (VG.Proof.CmacAes.X86.savedMem_big s₀).trans (hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨VG.Proof.CmacAes.X86.stR s₀, by simp, fun _ h => h⟩
    · exact ⟨VG.Proof.CmacAes.X86.scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨VG.Proof.CmacAes.X86.stkR s₀, by simp, fun _ h => h⟩)

/-! ## The end of a block -/

theorem dbl4 (n : BitVec 32) : n + n + (n + n) + (n + n + (n + n)) + (n + n + (n + n) + (n + n + (n + n))) =
    BitVec.ofNat 32 (16 * n.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem adv_zf {D n : BitVec 32} {k : Nat} (hk : k < n.toNat) (hfit : D.toNat + 16 * n.toNat ≤ 2 ^ 32) :
    (D + BitVec.ofNat 32 (16 * k) + 16 - ((n + n + (n + n) + (n + n + (n + n)) +
      (n + n + (n + n) + (n + n + (n + n)))) + D) == 0) = decide (k + 1 = n.toNat) := by
  rw [VG.Proof.CmacAes.X86.dbl4, Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj]
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow]
  have := D.isLt
  have h16 : (16 : BitVec 32).toNat = 16 := rfl
  have h0 : (0 : BitVec 32).toNat = 0 := rfl
  omega

theorem advance_eq : advance = .alu .add .esi (.imm 16) :: .mov .eax (argOp 4) :: .alu .add .eax (.reg .eax) ::
    .alu .add .eax (.reg .eax) :: .alu .add .eax (.reg .eax) :: .alu .add .eax (.reg .eax) ::
    .alu .add .eax (argOp 3) :: .alu .cmp .esi (.reg .eax) :: [] := rfl

theorem advance_wp {s₀ : State} (hp : VG.Proof.CmacAes.X86.UPre s₀) {k : Nat} (hk : k < VG.Proof.CmacAes.X86.N s₀) {s : State}
    (hesi : s.gpr .esi = VG.Proof.CmacAes.X86.Dp s₀ + BitVec.ofNat 32 (16 * k)) (hesp : s.gpr .esp = VG.Proof.CmacAes.X86.E s₀)
    (hargs : ∀ i < 6, s.mem.readW (argAddr s₀ i) 32 = VG.X86.arg s₀ i) (hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr) :
    WP isa (.block advance) s fun s' => s'.gpr .esi = VG.Proof.CmacAes.X86.Dp s₀ + BitVec.ofNat 32 (16 * (k + 1)) ∧
      s'.gpr .esp = VG.Proof.CmacAes.X86.E s₀ ∧ (∀ r, r ≠ .eax → r ≠ .esi → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.zf = some (decide (k + 1 = VG.Proof.CmacAes.X86.N s₀)) := by
  rw [VG.Proof.CmacAes.X86.advance_eq]
  refine wp_addi fun s₁ u₁ => ?_
  refine VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀) (by rw [u₁.other _ (by decide), hesp]) (by rw [u₁.rd, u₁.wr, hrw]; exact hp.arg_in (by decide))
    (by rw [u₁.mem]; exact hargs 4 (by decide)) fun s₂ u₂ => ?_
  refine wp_add fun s₃ u₃ => wp_add fun s₄ u₄ => wp_add fun s₅ u₅ => wp_add fun s₆ u₆ => ?_
  refine VG.Proof.CmacAes.X86.wp_addArg (s₀ := s₀)
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hesp])
    (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, hrw]
        exact hp.arg_in (by decide))
    (by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]; exact hargs 3 (by decide)) fun s₇ u₇ => ?_
  refine wp_cmp fun s₈ f₈ _ z₈ => WP.block_nil ⟨?_, ?_, fun r h₁ h₂ => ?_, ?_, ?_, ?_, ?_⟩
  · rw [f₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hesi, show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl,
      Offset.add_add_eq _ (c := 16 * (k + 1)) (by omega)]
  · rw [f₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hesp]
  · rw [f₈.gpr, u₇.other _ h₁, u₆.other _ h₁, u₅.other _ h₁, u₄.other _ h₁, u₃.other _ h₁, u₂.other _ h₁,
      u₁.other _ h₂]
  · rw [f₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [f₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [f₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [z₈, u₇.gpr, u₇.other _ (by decide), u₆.gpr, u₆.other _ (by decide), u₅.gpr, u₅.other _ (by decide),
      u₄.gpr, u₄.other _ (by decide), u₃.gpr, u₃.other _ (by decide), u₂.gpr, u₂.other _ (by decide), u₁.gpr, hesi]
    exact congrArg some (VG.Proof.CmacAes.X86.adv_zf hk hp.data_fit)

/-! ## One block -/

/-- The counter block's address. -/
abbrev Cb (s₀ : State) : BitVec 32 := VG.Proof.CmacAes.X86.S s₀ + BitVec.ofNat 32 2048

/-- What the code before the call leaves. -/
structure BodyA (s₀ : State) (k : Nat) (s s₁ : State) : Prop where
  pre : VG.Proof.CmacAes.X86.CtrPre s₁ (VG.Proof.CmacAes.X86.W s₀) (VG.Proof.CmacAes.X86.Cb s₀) (VG.Proof.CmacAes.X86.St s₀) (VG.Proof.CmacAes.X86.S s₀) (VG.Proof.CmacAes.X86.R s₀)
  esi : s₁.gpr .esi = s.gpr .esi
  esp : s₁.gpr .esp = s.gpr .esp
  mem : s₁.mem = Proof.Cmac.chainMem4 s.mem ((VG.Proof.CmacAes.X86.S s₀).setWidth 64 + BitVec.ofNat 64 2048) ((VG.Proof.CmacAes.X86.St s₀).setWidth 64)
    ((VG.Proof.CmacAes.X86.Dp s₀).setWidth 64 + BitVec.ofNat 64 (16 * k))
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

theorem ctrArgs_eq : ctrArgs = [.mov .eax (argOp 0), .mov .ecx (argOp 1), .mov .edx (.reg .ebp),
    .alu .add .edx (.imm (BitVec.ofNat 32 2048)), .mov .edi (.imm 1)] := rfl

theorem chainIn_eq : chainIn = .mov .ebx (argOp 2) :: .mov .ebp (argOp 5) ::
    (xor4 .ebx .esi .ebp 0 0 2048 ++ (zero4 .ebx 0 ++ ctrArgs)) := rfl

theorem bodyA_wp {s₀ : State} (hp : VG.Proof.CmacAes.X86.UPre s₀) {k : Nat} (hk : k < VG.Proof.CmacAes.X86.N s₀) {s : State} (h : VG.Proof.CmacAes.X86.LInv s₀ k s) :
    WP isa (.block chainIn) s (VG.Proof.CmacAes.X86.BodyA s₀ k s) := by
  have hRegs : s.rd ++ s.wr = [VG.Proof.CmacAes.X86.schR s₀, VG.Proof.CmacAes.X86.dataR s₀, VG.Proof.CmacAes.X86.argsR s₀, VG.Proof.CmacAes.X86.stR s₀, VG.Proof.CmacAes.X86.scrR s₀] := by
    rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  have hW : s.wr = [VG.Proof.CmacAes.X86.stR s₀, VG.Proof.CmacAes.X86.scrR s₀] := by rw [h.wr, hp.wr]
  have hsc := hp.scr_fit
  have hst := hp.st_fit
  have hdf := hp.data_fit
  have qN := hp.dataN hk
  have big := UPre.big_of h.frame
  have hargs : ∀ i < 6, s.mem.readW (argAddr s₀ i) 32 = VG.X86.arg s₀ i := fun i hi => hp.arg_keep big hi
  rw [VG.Proof.CmacAes.X86.chainIn_eq]
  refine VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀) h.esp (by rw [hrw]; exact hp.arg_in (by decide)) (hargs 2 (by decide))
    fun s₁ u₁ => ?_
  refine VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀) (by rw [u₁.other _ (by decide), h.esp]) (by rw [u₁.rd, u₁.wr, hrw]; exact hp.arg_in (by decide))
    (by rw [u₁.mem]; exact hargs 5 (by decide)) fun s₂ u₂ => ?_
  have b₂ : s₂.gpr .ebx = VG.Proof.CmacAes.X86.St s₀ := by rw [u₂.other _ (by decide), u₁.gpr]
  have p₂ : s₂.gpr .ebp = VG.Proof.CmacAes.X86.S s₀ := u₂.gpr
  have i₂ : s₂.gpr .esi = VG.Proof.CmacAes.X86.Dp s₀ + BitVec.ofNat 32 (16 * k) := by
    rw [u₂.other _ (by decide), u₁.other _ (by decide), h.esi]
  have rw₂ : s₂.rd ++ s₂.wr = [VG.Proof.CmacAes.X86.schR s₀, VG.Proof.CmacAes.X86.dataR s₀, VG.Proof.CmacAes.X86.argsR s₀, VG.Proof.CmacAes.X86.stR s₀, VG.Proof.CmacAes.X86.scrR s₀] := by
    rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, hRegs]
  have w₂ : s₂.wr = [VG.Proof.CmacAes.X86.stR s₀, VG.Proof.CmacAes.X86.scrR s₀] := by rw [u₂.wr, u₁.wr, hW]
  refine VG.Proof.CmacAes.X86.xor4_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [b₂]; omega) (by rw [i₂, qN]; omega) (by rw [p₂]; omega) ?_ ?_ ?_ fun s₃ g₃ => ?_
  · rw [b₂, VG.Proof.CmacAes.X86.add0, rw₂]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.CmacAes.X86.stR s₀, by simp, 0, by simp, by simp⟩
  · rw [i₂, VG.Proof.CmacAes.X86.add0, show (VG.Proof.CmacAes.X86.Dp s₀ + BitVec.ofNat 32 (16 * k)).setWidth 64 = addr (VG.Proof.CmacAes.X86.Dp s₀) (16 * k) from rfl,
      hp.dataA hk, rw₂]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.CmacAes.X86.dataR s₀, by simp, 16 * k, rfl, by simp; omega⟩
  · rw [p₂, w₂]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.CmacAes.X86.scrR s₀, by simp, 2048, rfl, by simp⟩
  have b₃ : s₃.gpr .ebx = VG.Proof.CmacAes.X86.St s₀ := by rw [g₃.gpr _ (by decide) (by decide), b₂]
  refine VG.Proof.CmacAes.X86.zero4_ok (by decide) (by rw [b₃]; omega) ?_ fun s₄ g₄ m₄ rd₄ wr₄ => ?_
  · rw [b₃, VG.Proof.CmacAes.X86.add0, g₃.wr, w₂]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.CmacAes.X86.stR s₀, by simp, 0, by simp, by simp⟩
  have esp₄ : s₄.gpr .esp = VG.Proof.CmacAes.X86.E s₀ := by
    rw [g₄ _ (by decide), g₃.gpr _ (by decide) (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.esp]
  have rd₄' : s₄.rd = s.rd := by rw [rd₄, g₃.rd, u₂.rd, u₁.rd]
  have wr₄' : s₄.wr = s.wr := by rw [wr₄, g₃.wr, u₂.wr, u₁.wr]
  have mem₄ : s₄.mem = Proof.Cmac.chainMem4 s.mem ((VG.Proof.CmacAes.X86.S s₀).setWidth 64 + BitVec.ofNat 64 2048)
      ((VG.Proof.CmacAes.X86.St s₀).setWidth 64) ((VG.Proof.CmacAes.X86.Dp s₀).setWidth 64 + BitVec.ofNat 64 (16 * k)) := by
    rw [m₄, b₃, VG.Proof.CmacAes.X86.add0, g₃.mem, p₂, b₂, i₂, VG.Proof.CmacAes.X86.add0, VG.Proof.CmacAes.X86.add0,
      show (VG.Proof.CmacAes.X86.Dp s₀ + BitVec.ofNat 32 (16 * k)).setWidth 64 = addr (VG.Proof.CmacAes.X86.Dp s₀) (16 * k) from rfl, hp.dataA hk,
      u₂.mem, u₁.mem]
    rfl
  have hargs₄ : ∀ i < 6, s₄.mem.readW (argAddr s₀ i) 32 = VG.X86.arg s₀ i := by
    intro i hi
    rw [mem₄]
    refine (Proof.Cmac.chainMem4_frame _ _ _ _).readW (Region.contains_self _ _) (fun r hr => ?_) (by decide) |>.trans
      (hargs i hi)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hp.args_scr.sub_left (hp.arg_sub hi)).sub_right (UPre.scr_sub (by decide))
    · exact hp.args_st.sub_left (hp.arg_sub hi)
  rw [VG.Proof.CmacAes.X86.ctrArgs_eq]
  refine VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀) esp₄ (by rw [rd₄', wr₄', hrw]; exact hp.arg_in (by decide)) (hargs₄ 0 (by decide))
    fun s₅ u₅ => ?_
  refine VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀) (by rw [u₅.other _ (by decide), esp₄])
    (by rw [u₅.rd, u₅.wr, rd₄', wr₄', hrw]; exact hp.arg_in (by decide))
    (by rw [u₅.mem]; exact hargs₄ 1 (by decide)) fun s₆ u₆ => ?_
  refine wp_mov fun s₇ u₇ => wp_addi fun s₈ u₈ => wp_movi fun s₉ u₉ => WP.block_nil ?_
  have keep : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → s₉.gpr r = s₄.gpr r := fun r ha hc hd hi => by
    rw [u₉.other _ hi, u₈.other _ hd, u₇.other _ hd, u₆.other _ hc, u₅.other _ ha]
  have p₄ : s₄.gpr .ebp = VG.Proof.CmacAes.X86.S s₀ := by rw [g₄ _ (by decide), g₃.gpr _ (by decide) (by decide), p₂]
  have b₄ : s₄.gpr .ebx = VG.Proof.CmacAes.X86.St s₀ := by rw [g₄ _ (by decide), b₃]
  have sp₉ : s₉.gpr .esp = VG.Proof.CmacAes.X86.E s₀ := by rw [keep _ (by decide) (by decide) (by decide) (by decide), esp₄]
  have rd₉ : s₉.rd = s.rd := by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, rd₄']
  have wr₉ : s₉.wr = s.wr := by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, wr₄']
  have mem₉ : s₉.mem = s₄.mem := by rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem]
  have hb : below (s₉.gpr .esp) 28 = VG.Proof.CmacAes.X86.stkR s₀ := by rw [sp₉]; exact hp.below_eq
  have cA : (VG.Proof.CmacAes.X86.Cb s₀).setWidth 64 = (VG.Proof.CmacAes.X86.S s₀).setWidth 64 + BitVec.ofNat 64 2048 := hp.scrA (by decide)
  have cSt : (⟨(VG.Proof.CmacAes.X86.Cb s₀).setWidth 64, 16⟩ : Region).Disjoint (VG.Proof.CmacAes.X86.stR s₀) := by
    rw [cA]; exact hp.st_scr.symm.sub_left (UPre.scr_sub (by decide))
  refine ⟨⟨?_, ?_, ?_, ?_, u₉.gpr, ?_, hp.rounds, by rw [sp₉]; exact hp.esp28, ?_, hp.sch_st, ?_, cSt,
    ?_, ?_, by rw [hb]; exact hp.b_sch, ?_, by rw [hb]; exact hp.b_st, ?_, hp.sch_fit, ?_, hp.st_fit, ?_, ?_, ?_,
    ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr]
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr]; exact VG.Proof.CmacAes.X86.arg_ofNat s₀ 1
  · rw [u₉.other _ (by decide), u₈.gpr, u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), p₄]
  · rw [keep _ (by decide) (by decide) (by decide) (by decide), b₄]
  · rw [keep _ (by decide) (by decide) (by decide) (by decide), p₄]
  · rw [cA]; exact hp.sch_scr.sub_right (UPre.scr_sub (by decide))
  · exact hp.sch_scr.sub_right (Region.sub_prefix (by decide))
  · rw [cA]; exact Offset.disjoint_base _ (by decide) (by omega)
  · exact hp.st_scr.sub_right (Region.sub_prefix (by decide))
  · rw [hb, cA]; exact hp.b_scr.sub_right (UPre.scr_sub (by decide))
  · rw [hb]; exact hp.b_scr.sub_right (Region.sub_prefix (by decide))
  · rw [hp.scrN (by decide)]; omega
  · omega
  · rw [rd₉, wr₉, hRegs]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.CmacAes.X86.schR s₀, by simp, 0, by simp, by simp⟩
  · rw [wr₉, hW, cA]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨VG.Proof.CmacAes.X86.scrR s₀, by simp, 2048, rfl, by simp⟩
    · exact ⟨VG.Proof.CmacAes.X86.stR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨VG.Proof.CmacAes.X86.scrR s₀, by simp, 0, by simp, by simp⟩
  · rw [mem₉, mem₄]; exact Proof.Cmac.chainMem4_state _ _ _ _
  · rw [keep _ (by decide) (by decide) (by decide) (by decide), g₄ _ (by decide), g₃.gpr _ (by decide) (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [sp₉, h.esp]
  · rw [mem₉, mem₄]
  · exact rd₉
  · exact wr₉

theorem body_ok {s₀ : State} (hp : VG.Proof.CmacAes.X86.UPre s₀) {k : Nat} (hk : k < VG.Proof.CmacAes.X86.N s₀) {s : State} (h : VG.Proof.CmacAes.X86.LInv s₀ k s) :
    WP isa (body v.callee) s fun s' => VG.Proof.CmacAes.X86.LInv s₀ (k + 1) s' ∧ s'.zf = some (decide (k + 1 = VG.Proof.CmacAes.X86.N s₀)) := by
  have hdf := hp.data_fit
  refine WP.seq (WP.mono (VG.Proof.CmacAes.X86.bodyA_wp hp hk h) fun s₁ a => ?_)
  refine WP.seq (WP.mono (VG.Proof.CmacAes.X86.ctr_call v a.pre) fun s₂ h₂ => ?_)
  have esp₁ : s₁.gpr .esp = VG.Proof.CmacAes.X86.E s₀ := by rw [a.esp, h.esp]
  have hb : below (s₁.gpr .esp) 28 = VG.Proof.CmacAes.X86.stkR s₀ := by rw [esp₁]; exact hp.below_eq
  have cA : (VG.Proof.CmacAes.X86.Cb s₀).setWidth 64 = (VG.Proof.CmacAes.X86.S s₀).setWidth 64 + BitVec.ofNat 64 2048 := hp.scrA (by decide)
  have f₁ : Frame [⟨(VG.Proof.CmacAes.X86.S s₀).setWidth 64 + BitVec.ofNat 64 2048, 16⟩, VG.Proof.CmacAes.X86.stR s₀] s.mem s₁.mem := by
    rw [a.mem]; exact Proof.Cmac.chainMem4_frame _ _ _ _
  have f₂ : Frame [VG.Proof.CmacAes.X86.stR s₀, ⟨(VG.Proof.CmacAes.X86.S s₀).setWidth 64, 2064⟩, VG.Proof.CmacAes.X86.stkR s₀] s₁.mem s₂.mem := by
    have fr := h₂.frame
    rw [hb, cA] at fr
    exact fr.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨(VG.Proof.CmacAes.X86.S s₀).setWidth 64, 2064⟩, by simp, Offset.sub_base _ (by decide)⟩
      · exact ⟨VG.Proof.CmacAes.X86.stR s₀, by simp, fun _ h => h⟩
      · exact ⟨⟨(VG.Proof.CmacAes.X86.S s₀).setWidth 64, 2064⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨VG.Proof.CmacAes.X86.stkR s₀, by simp, fun _ h => h⟩
  have f₁' : Frame [VG.Proof.CmacAes.X86.stR s₀, ⟨(VG.Proof.CmacAes.X86.S s₀).setWidth 64, 2064⟩, VG.Proof.CmacAes.X86.stkR s₀] s.mem s₁.mem := f₁.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨(VG.Proof.CmacAes.X86.S s₀).setWidth 64, 2064⟩, by simp, Offset.sub_base _ (by decide)⟩
    · exact ⟨VG.Proof.CmacAes.X86.stR s₀, by simp, fun _ h => h⟩
  have fr₂ : Frame [VG.Proof.CmacAes.X86.stR s₀, ⟨(VG.Proof.CmacAes.X86.S s₀).setWidth 64, 2064⟩, VG.Proof.CmacAes.X86.stkR s₀] (VG.Proof.CmacAes.X86.savedMem s₀) s₂.mem :=
    (h.frame.trans f₁').trans f₂
  have big₂ := UPre.big_of fr₂
  have big₁ := UPre.big_of (h.frame.trans f₁')
  have esi₂ : s₂.gpr .esi = VG.Proof.CmacAes.X86.Dp s₀ + BitVec.ofNat 32 (16 * k) := by
    rw [h₂.saved .esi (by simp [calleeSaved]), a.esi, h.esi]
  have esp₂ : s₂.gpr .esp = VG.Proof.CmacAes.X86.E s₀ := by rw [h₂.saved .esp (by simp [calleeSaved]), esp₁]
  have rw₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [h₂.rd, h₂.wr, a.rd, a.wr, h.rd, h.wr]
  refine WP.mono (VG.Proof.CmacAes.X86.advance_wp hp hk esi₂ esp₂ (fun i hi => hp.arg_keep big₂ hi) rw₂) fun s₃ ⟨esi₃, esp₃, _, mem₃,
    rd₃, wr₃, zf₃⟩ => ⟨⟨esi₃, esp₃, by rw [rd₃, h₂.rd, a.rd, h.rd], by rw [wr₃, h₂.wr, a.wr, h.wr],
      by rw [mem₃]; exact fr₂, ?_⟩, zf₃⟩
  have cst : (⟨(VG.Proof.CmacAes.X86.S s₀).setWidth 64 + BitVec.ofNat 64 2048, 16⟩ : Region).Disjoint (VG.Proof.CmacAes.X86.stR s₀) :=
    hp.st_scr.symm.sub_left (UPre.scr_sub (by decide))
  have cq : (⟨(VG.Proof.CmacAes.X86.S s₀).setWidth 64 + BitVec.ofNat 64 2048, 16⟩ : Region).Disjoint
      ⟨(VG.Proof.CmacAes.X86.Dp s₀).setWidth 64 + BitVec.ofNat 64 (16 * k), 16⟩ :=
    (hp.data_scr.symm.sub_left (UPre.scr_sub (by decide))).sub_right (UPre.data_sub hk)
  have out := h₂.out
  rw [UPre.sched_bytes hp big₁, cA, a.mem, Proof.Cmac.chainMem4_counter _ cst cq, h.state,
    UPre.block_bytes hp (UPre.big_of h.frame) hk] at out
  rw [mem₃, out, VG.Proof.CmacAes.X86.take_succ_blks s₀ hk, Proof.Cmac.chain_append, Proof.Cmac.chain_single]

theorem loop_ok {s₀ : State} (hp : VG.Proof.CmacAes.X86.UPre s₀) {k : Nat} (hk : k < VG.Proof.CmacAes.X86.N s₀) {s : State} (h : VG.Proof.CmacAes.X86.LInv s₀ k s) :
    WP isa (.loop (body v.callee) .ne) s (VG.Proof.CmacAes.X86.LInv s₀ (VG.Proof.CmacAes.X86.N s₀)) := by
  refine WP.loop (M := isa) (body := (body v.callee)) (c := .ne) (Q := VG.Proof.CmacAes.X86.LInv s₀ (VG.Proof.CmacAes.X86.N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = VG.Proof.CmacAes.X86.N s₀ - j ∧ j < VG.Proof.CmacAes.X86.N s₀ ∧ VG.Proof.CmacAes.X86.LInv s₀ j t) ?_ (VG.Proof.CmacAes.X86.N s₀ - k) s
    ⟨k, rfl, hk, h⟩
  rintro n s ⟨k, rfl, hk, h⟩
  refine WP.mono (VG.Proof.CmacAes.X86.body_ok v hp hk h) fun s' ⟨h', hz⟩ => ?_
  have ev : isa.eval .ne s' = some !decide (k + 1 = VG.Proof.CmacAes.X86.N s₀) := by
    show VG.X86.eval .ne s' = _; rw [eval_ne, hz]; rfl
  by_cases hz' : k + 1 = VG.Proof.CmacAes.X86.N s₀
  · left
    refine ⟨by rw [ev]; simp [hz'], ?_⟩
    rwa [← hz']
  · right
    refine ⟨by rw [ev]; simp [hz'], VG.Proof.CmacAes.X86.N s₀ - (k + 1), by omega, k + 1, rfl, by omega, h'⟩

end VG.Proof.CmacAes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.X86.UpdateCorrect`. -/
section

/-!
# AES-CMAC on x86: `vg_cmac_aes_update` is correct
-/

namespace VG.Proof.CmacAes.X86

open VG VG.X86 VG.Impl.CmacAes.X86
open VG.Proof.Aes.X86 (Ctr32Impl)

variable (v : Ctr32Impl)
open VG.Proof.MdStream.X86 (eval_e)

theorem slot_read {s₀ : State} (hp : VG.Proof.CmacAes.X86.UPre s₀) {m : Mem}
    (hf : Frame [VG.Proof.CmacAes.X86.stR s₀, ⟨(VG.Proof.CmacAes.X86.S s₀).setWidth 64, 2064⟩, VG.Proof.CmacAes.X86.stkR s₀] (VG.Proof.CmacAes.X86.savedMem s₀) m) {d : Nat} (h₁ : 2064 ≤ d)
    (h₂ : d + 4 ≤ 2080) :
    m.readW ((VG.Proof.CmacAes.X86.S s₀).setWidth 64 + BitVec.ofNat 64 d) 32 =
      (VG.Proof.CmacAes.X86.savedMem s₀).readW ((VG.Proof.CmacAes.X86.S s₀).setWidth 64 + BitVec.ofNat 64 d) 32 :=
  hf.readW (r := ⟨(VG.Proof.CmacAes.X86.S s₀).setWidth 64 + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.st_scr.symm.sub_left (UPre.scr_sub (by omega))
    · exact Offset.disjoint_base _ h₁ (by omega)
    · exact hp.b_scr.symm.sub_left (UPre.scr_sub (by omega))) (by decide)

theorem UPre.ret_stk {s₀ : State} (_hp : VG.Proof.CmacAes.X86.UPre s₀) : (VG.Proof.CmacAes.X86.retR s₀).Disjoint (VG.Proof.CmacAes.X86.stkR s₀) := by
  have := Offset.disjoint_below_above ((VG.Proof.CmacAes.X86.E s₀).setWidth 64) (m := 28) (a := 0) (l := 4) (by decide)
  rw [VG.Proof.CmacAes.X86.add0] at this
  exact this.symm

/-- The return address, which nothing writes. -/
theorem ret_read {s₀ : State} (hp : VG.Proof.CmacAes.X86.UPre s₀) {m : Mem}
    (hf : Frame [VG.Proof.CmacAes.X86.stR s₀, ⟨(VG.Proof.CmacAes.X86.S s₀).setWidth 64, 2064⟩, VG.Proof.CmacAes.X86.stkR s₀] (VG.Proof.CmacAes.X86.savedMem s₀) m) :
    m.readW ((VG.Proof.CmacAes.X86.E s₀).setWidth 64) 32 = s₀.mem.readW ((VG.Proof.CmacAes.X86.E s₀).setWidth 64) 32 :=
  (UPre.big_of hf).readW (r := VG.Proof.CmacAes.X86.retR s₀) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.ret_st
    · exact hp.ret_scr
    · exact hp.ret_stk) (by decide)

theorem epilogue_wp {s₀ : State} (hp : VG.Proof.CmacAes.X86.UPre s₀) {s : State} (h : VG.Proof.CmacAes.X86.LInv s₀ (VG.Proof.CmacAes.X86.N s₀) s) :
    WP isa (.block (restore 5)) s fun s' => abiPreserved s₀ s' ∧ updateX86.post s₀ s' := by
  have hsc : (VG.X86.arg s₀ 5).toNat + 2176 ≤ 2 ^ 32 := hp.scr_fit
  have rdwr : s.rd ++ s.wr = [VG.Proof.CmacAes.X86.schR s₀, VG.Proof.CmacAes.X86.dataR s₀, VG.Proof.CmacAes.X86.argsR s₀, VG.Proof.CmacAes.X86.stR s₀, VG.Proof.CmacAes.X86.scrR s₀] := by
    rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  have sl : ∀ r d, (r, d) ∈ saved → s.mem.readW ((VG.Proof.CmacAes.X86.S s₀).setWidth 64 + BitVec.ofNat 64 d) 32 = s₀.gpr r :=
    fun r d hrd => by
      have hb := VG.Proof.CmacAes.X86.saved_bound _ hrd
      rw [VG.Proof.CmacAes.X86.slot_read hp h.frame hb.1 hb.2, VG.Proof.CmacAes.X86.savedMem_slot s₀ hrd]
  rw [VG.Proof.CmacAes.X86.restore_eq]
  refine VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀) h.esp (by rw [hrw]; exact hp.arg_in (by decide))
    (hp.arg_keep (UPre.big_of h.frame) (by decide)) fun s₁ u₁ => ?_
  refine Spill.restore_ofNat_ok saved VG.Proof.CmacAes.X86.saved_fits (by rw [u₁.gpr]; omega) VG.Proof.CmacAes.X86.saved_ne_eax (fun p hp' => ?_)
    (fun p hp' => by rw [u₁.gpr, u₁.mem]; exact sl p.1 p.2 hp') fun s₂ r₂ => WP.block_nil ?_
  · have hb := VG.Proof.CmacAes.X86.saved_bound p hp'
    rw [u₁.gpr, u₁.rd, u₁.wr, rdwr]
    exact ⟨VG.Proof.CmacAes.X86.scrR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  refine ⟨⟨r₂.abi (by decide) (by decide) (by rw [u₁.other _ (by decide), h.esp]), ?_⟩, ?_⟩
  · rw [r₂.mem, u₁.mem]; exact VG.Proof.CmacAes.X86.ret_read hp h.frame
  · show Spec.Aes.bytesAt s₂.mem ((VG.Proof.CmacAes.X86.St s₀).setWidth 64) 16 = Spec.Cmac.chain (VG.Proof.CmacAes.X86.ciph s₀) _ (VG.Proof.CmacAes.X86.blks s₀)
    rw [r₂.mem, u₁.mem, h.state, List.take_of_length_le (by simp [Spec.Cmac.blocksAt])]

theorem mid_wp {s₀ : State} (hp : VG.Proof.CmacAes.X86.UPre s₀) {s₁ : State} (h : VG.Proof.CmacAes.X86.LInv s₀ 0 s₁)
    (hz : s₁.zf = some (decide (VG.Proof.CmacAes.X86.N s₀ = 0))) :
    WP isa (.ite .e (.block []) (.loop (body v.callee) .ne)) s₁ (VG.Proof.CmacAes.X86.LInv s₀ (VG.Proof.CmacAes.X86.N s₀)) := by
  have ev : isa.eval .e s₁ = some (decide (VG.Proof.CmacAes.X86.N s₀ = 0)) := by
    show VG.X86.eval .e s₁ = _; rw [eval_e, hz]
  by_cases hn : VG.Proof.CmacAes.X86.N s₀ = 0
  · refine WP.ite true (by rw [ev]; simp [hn]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    rw [hn]; exact h
  · refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
    exact VG.Proof.CmacAes.X86.loop_ok v hp (by omega) h

theorem update_wp {s₀ : State} (h0 : updateX86.pre s₀) :
    WP isa (update v.callee) s₀ fun s' => abiPreserved s₀ s' ∧ updateX86.post s₀ s' := by
  have hp := UPre.of h0
  exact WP.seq (WP.mono (VG.Proof.CmacAes.X86.prologue_wp hp) fun s₁ ⟨h₁, hz⟩ =>
    WP.seq (WP.mono (VG.Proof.CmacAes.X86.mid_wp v hp h₁ hz) fun _ h₂ => VG.Proof.CmacAes.X86.epilogue_wp hp h₂))

end VG.Proof.CmacAes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.X86.Finalize`. -/
section

/-!
# AES-CMAC on x86: `vg_cmac_aes_finalize`, the last block

The steps that form the last block `Mₙ` (§6.2 step 4) in the counter block,
before the chaining value is XORed in: `Mₙ* ⊕ K1` for a complete block
(`full_wp`), else `Mₙ*` copied a byte at a time onto zeros (`copy_wp`), `0x80`
after it, and the block XORed with `K2` (`partial_wp`). The arguments are
those of `vg_cmac_aes_update` but `last` (`Dp`) and `last_len` (`N`), so its
abbreviations serve.
-/

namespace VG.Proof.CmacAes.X86

open VG VG.X86 VG.Impl.CmacAes.X86
open VG.Proof.Aes.X86 (Ctr32Impl)

variable (v : Ctr32Impl)
open VG.Proof.MdStream.X86 (Upd Mupd Fupd wp_mov wp_movi wp_addi wp_subi wp_cmpi wp_test wp_movzx8 wp_store8
  eval_e eval_ne ofNat_beq_zero sub_ofNat)
open VG.WriteBytes (writeBytes writeBytes_nil writeBytes_snoc writeBytes_frame)

section
variable (s₀ : State)

/-- The key: the schedule and the subkeys `K1` and `K2` after it. -/
abbrev keyR : Region := ⟨(VG.Proof.CmacAes.X86.W s₀).setWidth 64, 272⟩
/-- The last bytes `Mₙ*`. -/
abbrev lastR : Region := ⟨(VG.Proof.CmacAes.X86.Dp s₀).setWidth 64, VG.Proof.CmacAes.X86.N s₀⟩

/-- The last block `Mₙ` (§6.2 step 4), from the key and the last bytes. -/
abbrev mn : List Byte :=
  Spec.Cmac.lastBlock 16 (Spec.Aes.bytesAt s₀.mem ((VG.Proof.CmacAes.X86.W s₀).setWidth 64 + BitVec.ofNat 64 240) 16)
    (Spec.Aes.bytesAt s₀.mem ((VG.Proof.CmacAes.X86.W s₀).setWidth 64 + BitVec.ofNat 64 256) 16)
    (Spec.Aes.bytesAt s₀.mem ((VG.Proof.CmacAes.X86.Dp s₀).setWidth 64) (VG.Proof.CmacAes.X86.N s₀))

/-- The counter block. -/
abbrev Ca : Addr := (VG.Proof.CmacAes.X86.S s₀).setWidth 64 + BitVec.ofNat 64 2048

end

/-- The precondition, by name. -/
structure FPre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.CmacAes.X86.keyR s₀, VG.Proof.CmacAes.X86.lastR s₀, VG.Proof.CmacAes.X86.argsR s₀]
  wr : s₀.wr = [VG.Proof.CmacAes.X86.stR s₀, VG.Proof.CmacAes.X86.scrR s₀]
  key_st : (VG.Proof.CmacAes.X86.keyR s₀).Disjoint (VG.Proof.CmacAes.X86.stR s₀)
  key_scr : (VG.Proof.CmacAes.X86.keyR s₀).Disjoint (VG.Proof.CmacAes.X86.scrR s₀)
  last_st : (VG.Proof.CmacAes.X86.lastR s₀).Disjoint (VG.Proof.CmacAes.X86.stR s₀)
  last_scr : (VG.Proof.CmacAes.X86.lastR s₀).Disjoint (VG.Proof.CmacAes.X86.scrR s₀)
  st_scr : (VG.Proof.CmacAes.X86.stR s₀).Disjoint (VG.Proof.CmacAes.X86.scrR s₀)
  args_st : (VG.Proof.CmacAes.X86.argsR s₀).Disjoint (VG.Proof.CmacAes.X86.stR s₀)
  args_scr : (VG.Proof.CmacAes.X86.argsR s₀).Disjoint (VG.Proof.CmacAes.X86.scrR s₀)
  ret_st : (VG.Proof.CmacAes.X86.retR s₀).Disjoint (VG.Proof.CmacAes.X86.stR s₀)
  ret_scr : (VG.Proof.CmacAes.X86.retR s₀).Disjoint (VG.Proof.CmacAes.X86.scrR s₀)
  b_key : (VG.Proof.CmacAes.X86.stkR s₀).Disjoint (VG.Proof.CmacAes.X86.keyR s₀)
  b_last : (VG.Proof.CmacAes.X86.stkR s₀).Disjoint (VG.Proof.CmacAes.X86.lastR s₀)
  b_st : (VG.Proof.CmacAes.X86.stkR s₀).Disjoint (VG.Proof.CmacAes.X86.stR s₀)
  b_scr : (VG.Proof.CmacAes.X86.stkR s₀).Disjoint (VG.Proof.CmacAes.X86.scrR s₀)
  key_fit : (VG.Proof.CmacAes.X86.W s₀).toNat + 272 ≤ 2 ^ 32
  st_fit : (VG.Proof.CmacAes.X86.St s₀).toNat + 16 ≤ 2 ^ 32
  last_fit : (VG.Proof.CmacAes.X86.Dp s₀).toNat + VG.Proof.CmacAes.X86.N s₀ ≤ 2 ^ 32
  scr_fit : (VG.Proof.CmacAes.X86.S s₀).toNat + 2176 ≤ 2 ^ 32
  esp28 : 28 ≤ (VG.Proof.CmacAes.X86.E s₀).toNat
  esp_fit : (VG.Proof.CmacAes.X86.E s₀).toNat + 28 ≤ 2 ^ 32
  rounds : VG.Proof.CmacAes.X86.R s₀ = 10 ∨ VG.Proof.CmacAes.X86.R s₀ = 12 ∨ VG.Proof.CmacAes.X86.R s₀ = 14
  len : VG.Proof.CmacAes.X86.N s₀ ≤ 16

theorem FPre.of {s₀ : State} (h : finalizeX86.pre s₀) : VG.Proof.CmacAes.X86.FPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t, u, v, w, x⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t, u, v, w, x⟩

theorem in_cov {rs : List Region} {a : Addr} {n : Nat} (h : Covers [⟨a, n⟩] rs) : InRegions rs a n :=
  h _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

section
variable {s₀ : State} (hp : VG.Proof.CmacAes.X86.FPre s₀)
include hp

theorem FPre.below_eq : below (VG.Proof.CmacAes.X86.E s₀) 28 = VG.Proof.CmacAes.X86.stkR s₀ := by
  simp only [below]; rw [Taint.sub_setWidth hp.esp28]

theorem FPre.argA {i : Nat} (hi : i < 6) : argAddr s₀ i = argAddr s₀ 0 + BitVec.ofNat 64 (4 * i) := by
  have : (s₀.gpr .esp).toNat + 28 ≤ 2 ^ 32 := hp.esp_fit
  simp only [argAddr]
  rw [show (s₀.gpr .esp + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 = addr (s₀.gpr .esp) (4 + 4 * i) from rfl,
    show (s₀.gpr .esp + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 = addr (s₀.gpr .esp) (4 + 4 * 0) from rfl,
    addr_eq (by omega), addr_eq (by omega), Offset.add_add]

theorem FPre.arg_sub {i : Nat} (hi : i < 6) : Region.Sub ⟨argAddr s₀ i, 4⟩ (VG.Proof.CmacAes.X86.argsR s₀) := by
  rw [hp.argA hi]; exact Offset.sub_base _ (by omega)

theorem FPre.arg_in {i : Nat} (hi : i < 6) : InRegions (s₀.rd ++ s₀.wr) (argAddr s₀ i) 4 := by
  refine ⟨VG.Proof.CmacAes.X86.argsR s₀, by simp [hp.rd], ?_⟩
  rw [hp.argA hi]; exact Offset.contains_base _ (by omega) (by omega)

theorem FPre.args_stk : (VG.Proof.CmacAes.X86.argsR s₀).Disjoint (VG.Proof.CmacAes.X86.stkR s₀) := by
  have : (s₀.gpr .esp).toNat + 28 ≤ 2 ^ 32 := hp.esp_fit
  have e : argAddr s₀ 0 = (VG.Proof.CmacAes.X86.E s₀).setWidth 64 + BitVec.ofNat 64 4 := addr_eq (by omega)
  show Region.Disjoint ⟨argAddr s₀ 0, 24⟩ _
  rw [e]; exact (Offset.disjoint_below_above _ (by decide)).symm

/-- The stack arguments are unchanged where only `Big` changes. -/
theorem FPre.arg_keep {m : Mem} (hf : Frame (VG.Proof.CmacAes.X86.Big s₀) s₀.mem m) {i : Nat} (hi : i < 6) :
    m.readW (argAddr s₀ i) 32 = VG.X86.arg s₀ i :=
  hf.readW (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.args_st.sub_left (hp.arg_sub hi)
    · exact hp.args_scr.sub_left (hp.arg_sub hi)
    · exact hp.args_stk.sub_left (hp.arg_sub hi)) (by decide)

theorem FPre.cS {d n : Nat} (h : d + n ≤ 2176) :
    Covers [⟨(VG.Proof.CmacAes.X86.S s₀).setWidth 64 + BitVec.ofNat 64 d, n⟩] s₀.wr := by
  rw [hp.wr]
  exact Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.CmacAes.X86.scrR s₀, by simp, d, rfl, h⟩

theorem FPre.cKey {d n : Nat} (h : d + n ≤ 272) :
    Covers [⟨(VG.Proof.CmacAes.X86.W s₀).setWidth 64 + BitVec.ofNat 64 d, n⟩] (s₀.rd ++ s₀.wr) := by
  rw [hp.rd]
  exact Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.CmacAes.X86.keyR s₀, by simp, d, rfl, h⟩

theorem FPre.cLast {d n : Nat} (h : d + n ≤ VG.Proof.CmacAes.X86.N s₀) :
    Covers [⟨(VG.Proof.CmacAes.X86.Dp s₀).setWidth 64 + BitVec.ofNat 64 d, n⟩] (s₀.rd ++ s₀.wr) := by
  rw [hp.rd]
  exact Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.CmacAes.X86.lastR s₀, by simp, d, rfl, h⟩

theorem FPre.ca_key {d n : Nat} (h : d + n ≤ 272) :
    (⟨VG.Proof.CmacAes.X86.Ca s₀, 16⟩ : Region).Disjoint ⟨(VG.Proof.CmacAes.X86.W s₀).setWidth 64 + BitVec.ofNat 64 d, n⟩ :=
  (hp.key_scr.symm.sub_left (Offset.sub_base _ (by decide))).sub_right (Offset.sub_base _ h)

theorem FPre.ca_last : (⟨VG.Proof.CmacAes.X86.Ca s₀, 16⟩ : Region).Disjoint (VG.Proof.CmacAes.X86.lastR s₀) :=
  hp.last_scr.symm.sub_left (Offset.sub_base _ (by decide))

theorem FPre.cA : (VG.Proof.CmacAes.X86.S s₀ + BitVec.ofNat 32 2048).setWidth 64 = VG.Proof.CmacAes.X86.Ca s₀ :=
  addr_eq (by have := hp.scr_fit; omega)

theorem FPre.key_bytes {d : Nat} (h : d + 16 ≤ 272) :
    Spec.Aes.bytesAt (VG.Proof.CmacAes.X86.savedMem s₀) ((VG.Proof.CmacAes.X86.W s₀).setWidth 64 + BitVec.ofNat 64 d) 16 =
      Spec.Aes.bytesAt s₀.mem ((VG.Proof.CmacAes.X86.W s₀).setWidth 64 + BitVec.ofNat 64 d) 16 :=
  Proof.Cmac.bytesAt_frame16 (VG.Proof.CmacAes.X86.savedMem_frame s₀) fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.key_scr.sub_left (Offset.sub_base _ h)

theorem FPre.last_bytes : Spec.Aes.bytesAt (VG.Proof.CmacAes.X86.savedMem s₀) ((VG.Proof.CmacAes.X86.Dp s₀).setWidth 64) (VG.Proof.CmacAes.X86.N s₀) =
    Spec.Aes.bytesAt s₀.mem ((VG.Proof.CmacAes.X86.Dp s₀).setWidth 64) (VG.Proof.CmacAes.X86.N s₀) :=
  Proof.Cmac.bytesAt_frame (VG.Proof.CmacAes.X86.savedMem_frame s₀) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hp.last_scr) (by have := hp.len; omega)

end

/-! ## Saving the registers -/

theorem finSave_eq : finSave = .mov .eax (argOp 5) :: (saved.map (fun p => Instr.store (at_ .eax p.2) p.1) ++
    ([.mov .ebp (.reg .eax), .mov .ecx (argOp 4), .alu .cmp .ecx (.imm 16)] : List Instr)) := rfl

/-- What `finSave` leaves. -/
structure FS (s₀ s : State) : Prop where
  keep : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .ebp → s.gpr r = s₀.gpr r
  ecx : s.gpr .ecx = BitVec.ofNat 32 (VG.Proof.CmacAes.X86.N s₀)
  ebp : s.gpr .ebp = VG.Proof.CmacAes.X86.S s₀
  zf : s.zf = some (decide (VG.Proof.CmacAes.X86.N s₀ = 16))
  mem : s.mem = VG.Proof.CmacAes.X86.savedMem s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem finSave_wp {s₀ : State} (hp : VG.Proof.CmacAes.X86.FPre s₀) : WP isa (.block finSave) s₀ (VG.Proof.CmacAes.X86.FS s₀) := by
  have hsc := hp.scr_fit
  rw [VG.Proof.CmacAes.X86.finSave_eq]
  refine VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀) rfl (hp.arg_in (by decide)) rfl fun s₁ u₁ => ?_
  have h₁ : s₁.gpr .eax = VG.Proof.CmacAes.X86.S s₀ := u₁.gpr
  refine Spill.save_ofNat_ok saved VG.Proof.CmacAes.X86.saved_fits (by rw [h₁]; omega) (fun p hp' => ?_) fun s₂ u₂ => ?_
  · have hb := VG.Proof.CmacAes.X86.saved_bound p hp'
    rw [h₁, u₁.wr, hp.wr]
    exact ⟨VG.Proof.CmacAes.X86.scrR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hm₂ : s₂.mem = VG.Proof.CmacAes.X86.savedMem s₀ := by
    rw [u₂.mem, u₁.mem, h₁, VG.Proof.CmacAes.X86.savedMem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p hp' => u₁.other _ (VG.Proof.CmacAes.X86.saved_ne_eax p hp')
  have esp₂ : s₂.gpr .esp = s₀.gpr .esp := by rw [u₂.gpr, u₁.other _ (by decide)]
  have rw₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]
  refine wp_mov fun s₃ u₃ => ?_
  refine VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀) (by rw [u₃.other _ (by decide), esp₂])
    (by rw [u₃.rd, u₃.wr, rw₂]; exact hp.arg_in (by decide))
    (by rw [u₃.mem, hm₂]; exact hp.arg_keep (VG.Proof.CmacAes.X86.savedMem_big s₀) (by decide)) fun s₄ u₄ => ?_
  refine wp_cmpi fun s₅ f₅ _ z₅ => WP.block_nil ⟨fun r ha hc hb => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [f₅.gpr, u₄.other _ hc, u₃.other _ hb, u₂.gpr, u₁.other _ ha]
  · rw [f₅.gpr, u₄.gpr]; exact VG.Proof.CmacAes.X86.arg_ofNat s₀ 4
  · rw [f₅.gpr, u₄.other _ (by decide), u₃.gpr, u₂.gpr, h₁]
  · rw [z₅, u₄.gpr, VG.Proof.CmacAes.X86.arg_ofNat s₀ 4, show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl,
      MdStream.X86.sub_beq (VG.X86.arg s₀ 4).isLt (by decide)]
  · rw [f₅.mem, u₄.mem, u₃.mem, hm₂]
  · rw [f₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [f₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]

/-! ## The last block -/

/-- What the branch on the length leaves: `Mₙ` in the counter block. -/
structure BPost (s₀ s : State) : Prop where
  ebp : s.gpr .ebp = VG.Proof.CmacAes.X86.S s₀
  esp : s.gpr .esp = VG.Proof.CmacAes.X86.E s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨VG.Proof.CmacAes.X86.Ca s₀, 16⟩] (VG.Proof.CmacAes.X86.savedMem s₀) s.mem
  blk : Spec.Aes.bytesAt s.mem (VG.Proof.CmacAes.X86.Ca s₀) 16 = VG.Proof.CmacAes.X86.mn s₀

theorem full_eq : full = .mov .ebx (argOp 3) :: .mov .edx (argOp 0) :: (xor4 .ebx .edx .ebp 0 240 2048 ++ []) := rfl

theorem full_wp {s₀ : State} (hp : VG.Proof.CmacAes.X86.FPre s₀) (hL : VG.Proof.CmacAes.X86.N s₀ = 16) {s : State} (h : VG.Proof.CmacAes.X86.FS s₀ s) :
    WP isa (.block full) s (VG.Proof.CmacAes.X86.BPost s₀) := by
  have sf := hp.scr_fit
  have kf := hp.key_fit
  have lf := hp.last_fit
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  have esp : s.gpr .esp = VG.Proof.CmacAes.X86.E s₀ := h.keep _ (by decide) (by decide) (by decide)
  rw [VG.Proof.CmacAes.X86.full_eq]
  refine VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀) esp (by rw [hrw]; exact hp.arg_in (by decide))
    (by rw [h.mem]; exact hp.arg_keep (VG.Proof.CmacAes.X86.savedMem_big s₀) (by decide)) fun s₁ u₁ => ?_
  refine VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀) (by rw [u₁.other _ (by decide), esp])
    (by rw [u₁.rd, u₁.wr, hrw]; exact hp.arg_in (by decide))
    (by rw [u₁.mem, h.mem]; exact hp.arg_keep (VG.Proof.CmacAes.X86.savedMem_big s₀) (by decide)) fun s₂ u₂ => ?_
  have b₂ : s₂.gpr .ebx = VG.Proof.CmacAes.X86.Dp s₀ := by rw [u₂.other _ (by decide), u₁.gpr]
  have d₂ : s₂.gpr .edx = VG.Proof.CmacAes.X86.W s₀ := u₂.gpr
  have p₂ : s₂.gpr .ebp = VG.Proof.CmacAes.X86.S s₀ := by rw [u₂.other _ (by decide), u₁.other _ (by decide), h.ebp]
  have rw₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, hrw]
  have w₂ : s₂.wr = s₀.wr := by rw [u₂.wr, u₁.wr, h.wr]
  have lf' : (VG.Proof.CmacAes.X86.Dp s₀).toNat + 16 ≤ 2 ^ 32 := by rw [← hL]; exact lf
  refine VG.Proof.CmacAes.X86.xor4_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [b₂]; omega) (by rw [d₂]; omega) (by rw [p₂]; omega)
    (by rw [b₂, rw₂]; exact hp.cLast (by omega)) (by rw [d₂, rw₂]; exact hp.cKey (by decide))
    (by rw [p₂, w₂]; exact hp.cS (by decide)) fun s₃ g₃ => WP.block_nil ?_
  refine ⟨by rw [g₃.gpr _ (by decide) (by decide), p₂],
    by rw [g₃.gpr _ (by decide) (by decide), u₂.other _ (by decide), u₁.other _ (by decide), esp],
    by rw [g₃.rd, u₂.rd, u₁.rd, h.rd], by rw [g₃.wr, w₂], ?_, ?_⟩
  · rw [g₃.mem, p₂, u₂.mem, u₁.mem, h.mem]; exact Proof.Cmac.xor4Mem_frame _ _ _ _
  · rw [g₃.mem, p₂, b₂, d₂, u₂.mem, u₁.mem, h.mem, VG.Proof.CmacAes.X86.add0, Proof.Cmac.xor4Mem_bytes _
      (Proof.Cmac.Sep4.of_disjoint (hp.ca_last.sub_right (Region.sub_prefix (by omega))))
      (Proof.Cmac.Sep4.of_disjoint (hp.ca_key (by decide))), hp.key_bytes (by decide)]
    have lb := hp.last_bytes
    rw [hL] at lb
    rw [lb]
    simp only [VG.Proof.CmacAes.X86.mn, Spec.Cmac.lastBlock, Proof.Cmac.bytesAt_length, hL, ite_true]
    exact Proof.Cmac.xor_comm _ _

/-! ## Copying the last bytes -/

theorem byte_rt32 (b : BitVec 8) : (b.setWidth 32).setWidth 8 = b := by
  apply BitVec.eq_of_toNat_eq
  have := b.isLt
  simp only [BitVec.toNat_setWidth]
  omega

theorem addr_at {p : BitVec 32} {i : Nat} (h : p.toNat + i < 2 ^ 32) :
    addr (p + BitVec.ofNat 32 i) 0 = p.setWidth 64 + BitVec.ofNat 64 i := by
  simp only [addr, VG.Proof.CmacAes.X86.add0']; exact addr_eq h

theorem copy_wp {s : State} {p c : BitVec 32} {L : Nat} (hL₀ : 0 < L) (hL : L ≤ 16)
    (hsi : s.gpr .esi = p) (hdi : s.gpr .edi = c) (hcx : s.gpr .ecx = BitVec.ofNat 32 L)
    (fp : p.toNat + L ≤ 2 ^ 32) (fc : c.toNat + 16 ≤ 2 ^ 32)
    (hr : Covers [⟨p.setWidth 64, L⟩] (s.rd ++ s.wr)) (hw : Covers [⟨c.setWidth 64, 16⟩] s.wr)
    (hd : (⟨p.setWidth 64, L⟩ : Region).Disjoint ⟨c.setWidth 64, 16⟩) :
    WP isa copy s fun s' =>
      s'.mem = VG.WriteBytes.writeBytes s.mem (c.setWidth 64) (Spec.Aes.bytesAt s.mem (p.setWidth 64) L) ∧
      s'.gpr .edi = c + BitVec.ofNat 32 L ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .esi → r ≠ .edi → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.loop (M := isa) (body := .block [.movzx8 .eax (at_ .esi 0), .store8 (at_ .edi 0) .al,
      .alu .add .esi (.imm 1), .alu .add .edi (.imm 1), .alu .sub .ecx (.imm 1)]) (c := .ne)
    (fun (n : Nat) (t : State) => ∃ i, n = L - i ∧ i < L ∧ t.gpr .esi = p + BitVec.ofNat 32 i ∧
      t.gpr .edi = c + BitVec.ofNat 32 i ∧ t.gpr .ecx = BitVec.ofNat 32 (L - i) ∧
      t.mem = VG.WriteBytes.writeBytes s.mem (c.setWidth 64) (Spec.Aes.bytesAt s.mem (p.setWidth 64) i) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .esi → r ≠ .edi → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr) ?_ (L - 0) _
    ⟨0, rfl, hL₀, by rw [hsi, VG.Proof.CmacAes.X86.add0'], by rw [hdi, VG.Proof.CmacAes.X86.add0'], by rw [hcx, Nat.sub_zero],
      by simp [Spec.Aes.bytesAt, VG.WriteBytes.writeBytes_nil], fun _ _ _ _ _ => rfl, rfl, rfl⟩
  rintro n t ⟨i, rfl, hi, xsi, xdi, xcx, mem, g, rd, wr⟩
  refine wp_movzx8 (a := p.setWidth 64 + BitVec.ofNat 64 i) (by rw [VG.Proof.CmacAes.X86.ea_at', xsi]; exact VG.Proof.CmacAes.X86.addr_at (by omega))
    (by rw [rd, wr]; exact hr _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩)
    fun t₁ u₁ => ?_
  refine wp_store8 (a := c.setWidth 64 + BitVec.ofNat 64 i)
    (by rw [VG.Proof.CmacAes.X86.ea_at', u₁.other _ (by decide), xdi]; exact VG.Proof.CmacAes.X86.addr_at (by omega))
    (by rw [u₁.wr, wr]; exact hw _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩)
    fun t₂ v₂ => ?_
  refine wp_addi fun t₃ u₃ => wp_addi fun t₄ u₄ => wp_subi fun t₅ u₅ z₅ => WP.block_nil ?_
  have hlen : (Spec.Aes.bytesAt s.mem (p.setWidth 64) i).length = i := Proof.Cmac.bytesAt_length _ _ _
  have hx : VG.WriteBytes.writeBytes s.mem (c.setWidth 64) (Spec.Aes.bytesAt s.mem (p.setWidth 64) i)
      (p.setWidth 64 + BitVec.ofNat 64 i) = s.mem (p.setWidth 64 + BitVec.ofNat 64 i) :=
    (VG.WriteBytes.writeBytes_frame s.mem (c.setWidth 64) _ (R := ⟨c.setWidth 64, i⟩) (by rw [hlen]; exact Region.contains_self _ _)) _
      fun r hr hcon => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hd _ (Offset.contains_base _ (by omega) (by omega)) (Region.sub_prefix (by omega) _ hcon)
  have al : t₁.gpr Reg8.al.reg = (t.mem (p.setWidth 64 + BitVec.ofNat 64 i)).setWidth 32 := u₁.gpr
  have hmem : t₅.mem = VG.WriteBytes.writeBytes s.mem (c.setWidth 64) (Spec.Aes.bytesAt s.mem (p.setWidth 64) (i + 1)) := by
    rw [u₅.mem, u₄.mem, u₃.mem, v₂.mem, al, u₁.mem, mem, VG.Proof.CmacAes.X86.byte_rt32, hx, Proof.Cmac.bytesAt_succ,
      VG.WriteBytes.writeBytes_snoc s.mem _ _ _ (by rw [hlen]; omega), hlen]
  have cx₄ : t₄.gpr .ecx = BitVec.ofNat 32 (L - i) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), xcx]
  have xcx' : t₅.gpr .ecx = BitVec.ofNat 32 (L - (i + 1)) := by
    rw [u₅.gpr, cx₄, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega), Nat.sub_sub]
  have ev : isa.eval .ne t₅ = some !decide (L - (i + 1) = 0) := by
    show VG.X86.eval .ne t₅ = _
    rw [eval_ne, z₅, cx₄, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega), Nat.sub_sub,
      ofNat_beq_zero (by omega)]
    rfl
  have gg : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .esi → r ≠ .edi → t₅.gpr r = s.gpr r := fun r ha hc hs hd' => by
    rw [u₅.other _ hc, u₄.other _ hd', u₃.other _ hs, v₂.gpr, u₁.other _ ha, g r ha hc hs hd']
  have xdi' : t₅.gpr .edi = c + BitVec.ofNat 32 (i + 1) := by
    rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), xdi,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Offset.add_add]
  have xsi' : t₅.gpr .esi = p + BitVec.ofNat 32 (i + 1) := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, v₂.gpr, u₁.other _ (by decide), xsi,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Offset.add_add]
  have rd' : t₅.rd = s.rd := by rw [u₅.rd, u₄.rd, u₃.rd, v₂.rd, u₁.rd, rd]
  have wr' : t₅.wr = s.wr := by rw [u₅.wr, u₄.wr, u₃.wr, v₂.wr, u₁.wr, wr]
  by_cases he : i + 1 = L
  · left
    exact ⟨by rw [ev]; simp [he], by rw [hmem, he], by rw [xdi', he], gg, rd', wr'⟩
  · right
    exact ⟨by rw [ev]; simp; omega, L - (i + 1), by omega, i + 1, rfl, by omega, xsi', xdi', xcx', hmem, gg,
      rd', wr'⟩

/-! ## A partial last block -/

theorem zero_eq : zero = zero4 .ebp 2048 ++ ([.mov .edi (.reg .ebp), .alu .add .edi (.imm (BitVec.ofNat 32 2048)),
    .mov .esi (argOp 3), .mov .ecx (argOp 4), .alu .test .ecx (.reg .ecx)] : List Instr) := rfl

theorem padK2_eq : padK2 = .mov .eax (.imm 0x80) :: .store8 (at_ .edi 0) .al :: .mov .edx (argOp 0) ::
    (xor4 .ebp .edx .ebp 2048 256 2048 ++ []) := rfl

theorem b80 : ((0x80 : BitVec 32).setWidth 8 : Byte) = 0x80 := by decide

theorem partial_wp {s₀ : State} (hp : VG.Proof.CmacAes.X86.FPre s₀) (hL : VG.Proof.CmacAes.X86.N s₀ < 16) {s : State} (h : VG.Proof.CmacAes.X86.FS s₀ s) :
    WP isa partialBlock s (VG.Proof.CmacAes.X86.BPost s₀) := by
  have sf := hp.scr_fit
  have sf' : (VG.X86.arg s₀ 5).toNat + 2176 ≤ 2 ^ 32 := sf
  have kf := hp.key_fit
  have lf := hp.last_fit
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  have cA := hp.cA
  -- Zero the counter block.
  refine WP.seq ?_
  rw [VG.Proof.CmacAes.X86.zero_eq]
  refine VG.Proof.CmacAes.X86.zero4_ok (b := .ebp) (d := 2048) (by decide) (by rw [h.ebp]; omega)
    (by rw [h.ebp, h.wr]; exact hp.cS (by decide)) fun s₁ g₁ m₁ rd₁ wr₁ => ?_
  have p₁ : s₁.gpr .ebp = VG.Proof.CmacAes.X86.S s₀ := by rw [g₁ _ (by decide), h.ebp]
  have esp₁ : s₁.gpr .esp = VG.Proof.CmacAes.X86.E s₀ := by rw [g₁ _ (by decide), h.keep _ (by decide) (by decide) (by decide)]
  have fz : Frame [⟨VG.Proof.CmacAes.X86.Ca s₀, 16⟩] (VG.Proof.CmacAes.X86.savedMem s₀) (Proof.Cmac.zero4 (VG.Proof.CmacAes.X86.savedMem s₀) (VG.Proof.CmacAes.X86.Ca s₀)) :=
    Proof.Cmac.frame_store4 _ _ _ _ _
  have mem₁ : s₁.mem = Proof.Cmac.zero4 (VG.Proof.CmacAes.X86.savedMem s₀) (VG.Proof.CmacAes.X86.Ca s₀) := by rw [m₁, h.ebp, h.mem]
  have big₁ : Frame (VG.Proof.CmacAes.X86.Big s₀) s₀.mem s₁.mem := by
    rw [mem₁]
    exact (VG.Proof.CmacAes.X86.savedMem_big s₀).trans (fz.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.CmacAes.X86.scrR s₀, by simp, Offset.sub_base _ (by decide)⟩)
  have rw₁ : s₁.rd ++ s₁.wr = s₀.rd ++ s₀.wr := by rw [rd₁, wr₁, hrw]
  refine wp_mov fun s₂ u₂ => wp_addi fun s₃ u₃ => ?_
  refine VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀) (by rw [u₃.other _ (by decide), u₂.other _ (by decide), esp₁])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, rw₁]; exact hp.arg_in (by decide))
    (by rw [u₃.mem, u₂.mem]; exact hp.arg_keep big₁ (by decide)) fun s₄ u₄ => ?_
  refine VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀) (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), esp₁])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, rw₁]; exact hp.arg_in (by decide))
    (by rw [u₄.mem, u₃.mem, u₂.mem]; exact hp.arg_keep big₁ (by decide)) fun s₅ u₅ => ?_
  refine wp_test fun s₆ f₆ z₆ => WP.block_nil ?_
  have k₆ : ∀ r, r ≠ .ecx → r ≠ .esi → r ≠ .edi → s₆.gpr r = s₁.gpr r := fun r hc hs hd => by
    rw [f₆.gpr, u₅.other _ hc, u₄.other _ hs, u₃.other _ hd, u₂.other _ hd]
  have edi₆ : s₆.gpr .edi = VG.Proof.CmacAes.X86.S s₀ + BitVec.ofNat 32 2048 := by
    rw [f₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr, p₁]
  have esi₆ : s₆.gpr .esi = VG.Proof.CmacAes.X86.Dp s₀ := by rw [f₆.gpr, u₅.other _ (by decide), u₄.gpr]
  have ecx₆ : s₆.gpr .ecx = BitVec.ofNat 32 (VG.Proof.CmacAes.X86.N s₀) := by rw [f₆.gpr, u₅.gpr]; exact VG.Proof.CmacAes.X86.arg_ofNat s₀ 4
  have mem₆ : s₆.mem = Proof.Cmac.zero4 (VG.Proof.CmacAes.X86.savedMem s₀) (VG.Proof.CmacAes.X86.Ca s₀) := by
    rw [f₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, mem₁]
  have rd₆ : s₆.rd = s₀.rd := by rw [f₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁, h.rd]
  have wr₆ : s₆.wr = s₀.wr := by rw [f₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁, h.wr]
  have ev : isa.eval .e s₆ = some (decide (VG.Proof.CmacAes.X86.N s₀ = 0)) := by
    show VG.X86.eval .e s₆ = _
    rw [eval_e, z₆, u₅.gpr, VG.Proof.CmacAes.X86.arg_ofNat s₀ 4, VG.Proof.CmacAes.X86.ofNat_and_self_beq (VG.X86.arg s₀ 4).isLt]
  have lastZ : Spec.Aes.bytesAt (Proof.Cmac.zero4 (VG.Proof.CmacAes.X86.savedMem s₀) (VG.Proof.CmacAes.X86.Ca s₀)) ((VG.Proof.CmacAes.X86.Dp s₀).setWidth 64) (VG.Proof.CmacAes.X86.N s₀) =
      Spec.Aes.bytesAt s₀.mem ((VG.Proof.CmacAes.X86.Dp s₀).setWidth 64) (VG.Proof.CmacAes.X86.N s₀) := by
    rw [Proof.Cmac.bytesAt_frame fz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.ca_last.symm) (by omega), hp.last_bytes]
  -- Copy the last bytes.
  refine WP.seq (WP.mono (Q := fun (s₇ : State) =>
      s₇.mem = VG.WriteBytes.writeBytes (Proof.Cmac.zero4 (VG.Proof.CmacAes.X86.savedMem s₀) (VG.Proof.CmacAes.X86.Ca s₀)) (VG.Proof.CmacAes.X86.Ca s₀)
        (Spec.Aes.bytesAt s₀.mem ((VG.Proof.CmacAes.X86.Dp s₀).setWidth 64) (VG.Proof.CmacAes.X86.N s₀)) ∧
      s₇.gpr .edi = VG.Proof.CmacAes.X86.S s₀ + BitVec.ofNat 32 (2048 + VG.Proof.CmacAes.X86.N s₀) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .esi → r ≠ .edi → s₇.gpr r = s₆.gpr r) ∧
      s₇.rd = s₀.rd ∧ s₇.wr = s₀.wr) ?_ fun s₇ h₇ => ?_)
  · by_cases hL0 : VG.Proof.CmacAes.X86.N s₀ = 0
    · refine WP.ite true (by rw [ev]; simp [hL0]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      refine ⟨by rw [mem₆, hL0]; simp [Spec.Aes.bytesAt, VG.WriteBytes.writeBytes_nil], by rw [edi₆, hL0],
        fun _ _ _ _ _ => rfl, rd₆, wr₆⟩
    · refine WP.ite false (by rw [ev]; simp [hL0]) (fun h => by cases h) fun _ => ?_
      have hr := hp.cLast (d := 0) (n := VG.Proof.CmacAes.X86.N s₀) (by omega)
      rw [VG.Proof.CmacAes.X86.add0] at hr
      refine WP.mono (VG.Proof.CmacAes.X86.copy_wp (p := VG.Proof.CmacAes.X86.Dp s₀) (c := VG.Proof.CmacAes.X86.S s₀ + BitVec.ofNat 32 2048) (L := VG.Proof.CmacAes.X86.N s₀) (by omega) (by omega)
        esi₆ edi₆ ecx₆ lf
        (by rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 2048) (by decide),
          Nat.mod_eq_of_lt (by omega)]; omega)
        (by rw [rd₆, wr₆]; exact hr) (by rw [cA, wr₆]; exact hp.cS (by decide))
        (by rw [cA]; exact hp.ca_last.symm)) ?_
      rintro s₇ ⟨m₇, di₇, g₇, rd₇, wr₇⟩
      exact ⟨by rw [m₇, mem₆, cA, lastZ], by rw [di₇, Offset.add_add], g₇, by rw [rd₇, rd₆], by rw [wr₇, wr₆]⟩
  · obtain ⟨m₇, di₇, g₇, rd₇, wr₇⟩ := h₇
    rw [VG.Proof.CmacAes.X86.padK2_eq]
    refine wp_movi fun s₈ u₈ => ?_
    refine wp_store8 (a := VG.Proof.CmacAes.X86.Ca s₀ + BitVec.ofNat 64 (VG.Proof.CmacAes.X86.N s₀))
      (by
        rw [VG.Proof.CmacAes.X86.ea_at', u₈.other _ (by decide), di₇, VG.Proof.CmacAes.X86.addr_at (by omega)]
        show _ = (VG.Proof.CmacAes.X86.S s₀).setWidth 64 + BitVec.ofNat 64 2048 + BitVec.ofNat 64 (VG.Proof.CmacAes.X86.N s₀)
        rw [Offset.add_add])
      (by
        rw [u₈.wr, wr₇]
        show InRegions s₀.wr ((VG.Proof.CmacAes.X86.S s₀).setWidth 64 + BitVec.ofNat 64 2048 + BitVec.ofNat 64 (VG.Proof.CmacAes.X86.N s₀)) 1
        rw [Offset.add_add]
        exact VG.Proof.CmacAes.X86.in_cov (hp.cS (d := 2048 + VG.Proof.CmacAes.X86.N s₀) (n := 1) (by omega))) fun s₉ v₉ => ?_
    have g₉ : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .esi → r ≠ .edi → s₉.gpr r = s₁.gpr r := fun r ha hc hs hd => by
      rw [v₉.gpr, u₈.other _ ha, g₇ r ha hc hs hd, k₆ r hc hs hd]
    have esp₉ : s₉.gpr .esp = VG.Proof.CmacAes.X86.E s₀ := by
      rw [g₉ _ (by decide) (by decide) (by decide) (by decide), esp₁]
    have rw₉ : s₉.rd ++ s₉.wr = s₀.rd ++ s₀.wr := by rw [v₉.rd, v₉.wr, u₈.rd, u₈.wr, rd₇, wr₇]
    have hlen : (Spec.Aes.bytesAt s₀.mem ((VG.Proof.CmacAes.X86.Dp s₀).setWidth 64) (VG.Proof.CmacAes.X86.N s₀)).length = VG.Proof.CmacAes.X86.N s₀ :=
      Proof.Cmac.bytesAt_length _ _ _
    have m₉ : s₉.mem = (VG.WriteBytes.writeBytes (Proof.Cmac.zero4 (VG.Proof.CmacAes.X86.savedMem s₀) (VG.Proof.CmacAes.X86.Ca s₀)) (VG.Proof.CmacAes.X86.Ca s₀)
        (Spec.Aes.bytesAt s₀.mem ((VG.Proof.CmacAes.X86.Dp s₀).setWidth 64) (VG.Proof.CmacAes.X86.N s₀))).writeW (VG.Proof.CmacAes.X86.Ca s₀ + BitVec.ofNat 64 (VG.Proof.CmacAes.X86.N s₀))
        (0x80 : Byte) := by
      have : s₈.gpr Reg8.al.reg = 0x80 := u₈.gpr
      rw [v₉.mem, this, u₈.mem, m₇, VG.Proof.CmacAes.X86.b80]
    have fW : Frame [⟨VG.Proof.CmacAes.X86.Ca s₀, 16⟩] (VG.Proof.CmacAes.X86.savedMem s₀) s₉.mem := by
      rw [m₉]
      refine (fz.trans (VG.WriteBytes.writeBytes_frame _ _ _ ?_)).trans
        ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega)))
      rw [hlen]; simpa using Offset.contains_base (VG.Proof.CmacAes.X86.Ca s₀) (d := 0) (n := VG.Proof.CmacAes.X86.N s₀) (k := 16) (by omega) (by decide)
    have big₉ : Frame (VG.Proof.CmacAes.X86.Big s₀) s₀.mem s₉.mem :=
      (VG.Proof.CmacAes.X86.savedMem_big s₀).trans (fW.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨VG.Proof.CmacAes.X86.scrR s₀, by simp, Offset.sub_base _ (by decide)⟩)
    refine VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀) esp₉ (by rw [rw₉]; exact hp.arg_in (by decide)) (hp.arg_keep big₉ (by decide))
      fun s₁₀ u₁₀ => ?_
    have p₁₀ : s₁₀.gpr .ebp = VG.Proof.CmacAes.X86.S s₀ := by
      rw [u₁₀.other _ (by decide), g₉ _ (by decide) (by decide) (by decide) (by decide), p₁]
    have d₁₀ : s₁₀.gpr .edx = VG.Proof.CmacAes.X86.W s₀ := u₁₀.gpr
    have rw₁₀ : s₁₀.rd ++ s₁₀.wr = s₀.rd ++ s₀.wr := by rw [u₁₀.rd, u₁₀.wr, rw₉]
    have w₁₀ : s₁₀.wr = s₀.wr := by rw [u₁₀.wr, v₉.wr, u₈.wr, wr₇]
    refine VG.Proof.CmacAes.X86.xor4_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rw [p₁₀]; omega) (by rw [d₁₀]; omega) (by rw [p₁₀]; omega)
      (by
        rw [p₁₀, rw₁₀]
        exact fun a n hi => (hp.cS (d := 2048) (n := 16) (by decide)) a n hi |>
          fun ⟨r, hr, hc⟩ => ⟨r, List.mem_append_right _ hr, hc⟩)
      (by rw [d₁₀, rw₁₀]; exact hp.cKey (by decide)) (by rw [p₁₀, w₁₀]; exact hp.cS (by decide))
      fun s₁₁ g₁₁ => WP.block_nil ?_
    have pad : Spec.Aes.bytesAt s₉.mem (VG.Proof.CmacAes.X86.Ca s₀) 16 =
        Spec.Aes.bytesAt s₀.mem ((VG.Proof.CmacAes.X86.Dp s₀).setWidth 64) (VG.Proof.CmacAes.X86.N s₀) ++ [0x80] ++ Spec.Cmac.zeros (16 - VG.Proof.CmacAes.X86.N s₀ - 1) := by
      have := Proof.Cmac.padded_bytes (Proof.Cmac.zero4 (VG.Proof.CmacAes.X86.savedMem s₀) (VG.Proof.CmacAes.X86.Ca s₀)) (VG.Proof.CmacAes.X86.Ca s₀)
        (Spec.Aes.bytesAt s₀.mem ((VG.Proof.CmacAes.X86.Dp s₀).setWidth 64) (VG.Proof.CmacAes.X86.N s₀)) (by rw [hlen]; exact hL)
        (Proof.Cmac.zero4_bytes _ _)
      rw [hlen] at this
      rw [m₉]; exact this
    have k2 : Spec.Aes.bytesAt s₉.mem ((VG.Proof.CmacAes.X86.W s₀).setWidth 64 + BitVec.ofNat 64 256) 16 =
        Spec.Aes.bytesAt s₀.mem ((VG.Proof.CmacAes.X86.W s₀).setWidth 64 + BitVec.ofNat 64 256) 16 := by
      rw [Proof.Cmac.bytesAt_frame16 fW (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (hp.ca_key (by decide)).symm), hp.key_bytes (by decide)]
    refine ⟨by rw [g₁₁.gpr _ (by decide) (by decide), p₁₀],
      by rw [g₁₁.gpr _ (by decide) (by decide), u₁₀.other _ (by decide), esp₉],
      by rw [g₁₁.rd, u₁₀.rd, v₉.rd, u₈.rd, rd₇], by rw [g₁₁.wr, w₁₀], ?_, ?_⟩
    · rw [g₁₁.mem, p₁₀, u₁₀.mem]; exact fW.trans (Proof.Cmac.xor4Mem_frame _ _ _ _)
    · rw [g₁₁.mem, p₁₀, d₁₀, u₁₀.mem, Proof.Cmac.xor4Mem_bytes _ (Proof.Cmac.Sep4.self _)
        (Proof.Cmac.Sep4.of_disjoint (hp.ca_key (by decide))), pad, k2]
      simp only [VG.Proof.CmacAes.X86.mn, Spec.Cmac.lastBlock, hlen, show VG.Proof.CmacAes.X86.N s₀ ≠ 16 by omega, ite_false]
      exact Proof.Cmac.xor_comm _ _

end VG.Proof.CmacAes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.X86.UpdateCT`. -/
section

/-!
# AES-CMAC on x86: `vg_cmac_aes_update` is constant time

The taint analysis does not analyse frames, so two runs from states that agree
on the public arguments are related piece by piece (`RelCT`): the taint
analysis covers the code between the calls, from `esp`, the stack arguments
(which nothing writes, `argTaint`) and `esi` (the next block, which the
correctness proof pins to the public arguments), and each call of
`vg_aes_ctr32`, in its frame, is constant time by its own proof (`ctr_rel`).
-/

namespace VG.Proof.CmacAes.X86

open VG VG.X86 VG.Impl.CmacAes.X86
open VG.Proof.Aes.X86 (Ctr32Impl)

variable (v : Ctr32Impl)
open VG.Proof.MdStream.X86 (eval_e eval_ne)

/-- The stack arguments of a state with the entry stack pointer, from
those of the entry state. -/
theorem arg_cur {s₀ s : State} (hesp : s.gpr .esp = s₀.gpr .esp) {i : Nat}
    (hm : s.mem.readW (argAddr s₀ i) 32 = VG.X86.arg s₀ i) : VG.X86.arg s i = VG.X86.arg s₀ i := by
  show s.mem.readW (argAddr s i) 32 = _
  rw [show argAddr s i = argAddr s₀ i by simp only [argAddr, hesp]]; exact hm

theorem UPre.argsOut {s₀ : State} (hp : VG.Proof.CmacAes.X86.UPre s₀) {s : State} (hesp : s.gpr .esp = VG.Proof.CmacAes.X86.E s₀) (hwr : s.wr = s₀.wr) :
    ArgsOut 6 s := by
  have hs : (s₀.gpr .esp).toNat + 28 ≤ 2 ^ 32 := hp.esp_fit
  refine ⟨by rw [hesp]; omega, ?_⟩
  rw [hwr, hp.wr, hesp]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega) hp.ret_st hp.args_st
  · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega) hp.ret_scr hp.args_scr

/-- What two runs agree on at a point between the calls. -/
structure Pt (s₀ : State) (s : State) : Prop where
  esp : s.gpr .esp = VG.Proof.CmacAes.X86.E s₀
  wr : s.wr = s₀.wr
  args : ∀ i < 6, s.mem.readW (argAddr s₀ i) 32 = VG.X86.arg s₀ i

section
variable {s₀ s₀' : State} (hq : updateX86.pub s₀ s₀')
include hq

theorem pub_E : VG.Proof.CmacAes.X86.E s₀ = VG.Proof.CmacAes.X86.E s₀' := hq.1
theorem pub_arg {i : Nat} (hi : i < 6) : VG.X86.arg s₀ i = VG.X86.arg s₀' i := hq.2 i hi
theorem pub_N : VG.Proof.CmacAes.X86.N s₀ = VG.Proof.CmacAes.X86.N s₀' := by rw [VG.Proof.CmacAes.X86.N, VG.Proof.CmacAes.X86.N, VG.Proof.CmacAes.X86.pub_arg hq (by decide)]
theorem pub_W : VG.Proof.CmacAes.X86.W s₀ = VG.Proof.CmacAes.X86.W s₀' := VG.Proof.CmacAes.X86.pub_arg hq (by decide)
theorem pub_R : VG.Proof.CmacAes.X86.R s₀ = VG.Proof.CmacAes.X86.R s₀' := by rw [VG.Proof.CmacAes.X86.R, VG.Proof.CmacAes.X86.R, VG.Proof.CmacAes.X86.pub_arg hq (by decide)]
theorem pub_St : VG.Proof.CmacAes.X86.St s₀ = VG.Proof.CmacAes.X86.St s₀' := VG.Proof.CmacAes.X86.pub_arg hq (by decide)
theorem pub_Dp : VG.Proof.CmacAes.X86.Dp s₀ = VG.Proof.CmacAes.X86.Dp s₀' := VG.Proof.CmacAes.X86.pub_arg hq (by decide)
theorem pub_S : VG.Proof.CmacAes.X86.S s₀ = VG.Proof.CmacAes.X86.S s₀' := VG.Proof.CmacAes.X86.pub_arg hq (by decide)
theorem pub_Cb : VG.Proof.CmacAes.X86.Cb s₀ = VG.Proof.CmacAes.X86.Cb s₀' := by rw [VG.Proof.CmacAes.X86.Cb, VG.Proof.CmacAes.X86.Cb, VG.Proof.CmacAes.X86.pub_S hq]

/-- Two runs agree on `esp`, the stack arguments and the registers `rs`. -/
theorem Pt.agree (hp : VG.Proof.CmacAes.X86.UPre s₀) (hp' : VG.Proof.CmacAes.X86.UPre s₀') {rs : List Reg} {s₁ s₂ : State} (h₁ : VG.Proof.CmacAes.X86.Pt s₀ s₁)
    (h₂ : VG.Proof.CmacAes.X86.Pt s₀' s₂) (hr : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) :
    VG.X86.Taint.Agree (argTaint rs (4 + 4 * 6)) s₁ s₂ :=
  agree_argTaint hr (by rw [h₁.esp, h₂.esp, VG.Proof.CmacAes.X86.pub_E hq]) (hp.argsOut h₁.esp h₁.wr) (hp'.argsOut h₂.esp h₂.wr)
    fun i hi => by rw [VG.Proof.CmacAes.X86.arg_cur (h₁.esp) (h₁.args i hi), VG.Proof.CmacAes.X86.arg_cur (h₂.esp) (h₂.args i hi), VG.Proof.CmacAes.X86.pub_arg hq hi]

end

theorem LInv.pt {s₀ : State} (hp : VG.Proof.CmacAes.X86.UPre s₀) {k : Nat} {s : State} (h : VG.Proof.CmacAes.X86.LInv s₀ k s) : VG.Proof.CmacAes.X86.Pt s₀ s :=
  ⟨h.esp, h.wr, fun _ hi => hp.arg_keep (UPre.big_of h.frame) hi⟩

/-! ## One block -/

/-- What is known between the code before the call and the call. -/
structure Mid (s₀ : State) (k : Nat) (s : State) : Prop where
  pre : VG.Proof.CmacAes.X86.CtrPre s (VG.Proof.CmacAes.X86.W s₀) (VG.Proof.CmacAes.X86.Cb s₀) (VG.Proof.CmacAes.X86.St s₀) (VG.Proof.CmacAes.X86.S s₀) (VG.Proof.CmacAes.X86.R s₀)
  esi : s.gpr .esi = VG.Proof.CmacAes.X86.Dp s₀ + BitVec.ofNat 32 (16 * k)
  pt : VG.Proof.CmacAes.X86.Pt s₀ s
  big : Frame (VG.Proof.CmacAes.X86.Big s₀) s₀.mem s.mem

theorem bodyMid_wp {s₀ : State} (hp : VG.Proof.CmacAes.X86.UPre s₀) {k : Nat} (hk : k < VG.Proof.CmacAes.X86.N s₀) {s : State} (h : VG.Proof.CmacAes.X86.LInv s₀ k s) :
    WP isa (.block chainIn) s (VG.Proof.CmacAes.X86.Mid s₀ k) :=
  WP.mono (VG.Proof.CmacAes.X86.bodyA_wp hp hk h) fun s₁ a => by
    have big : Frame (VG.Proof.CmacAes.X86.Big s₀) s₀.mem s₁.mem := (UPre.big_of h.frame).trans (by
      rw [a.mem]
      exact (Proof.Cmac.chainMem4_frame _ _ _ _).sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨VG.Proof.CmacAes.X86.scrR s₀, by simp, UPre.scr_sub (by decide)⟩
        · exact ⟨VG.Proof.CmacAes.X86.stR s₀, by simp, fun _ h => h⟩)
    exact ⟨a.pre, by rw [a.esi, h.esi], ⟨by rw [a.esp, h.esp], by rw [a.wr, h.wr],
      fun _ hi => hp.arg_keep big hi⟩, big⟩

/-- What is known after the call. -/
structure After (s₀ : State) (k : Nat) (s : State) : Prop where
  esi : s.gpr .esi = VG.Proof.CmacAes.X86.Dp s₀ + BitVec.ofNat 32 (16 * k)
  pt : VG.Proof.CmacAes.X86.Pt s₀ s

theorem call_after {s₀ : State} (hp : VG.Proof.CmacAes.X86.UPre s₀) {k : Nat} {s : State} (h : VG.Proof.CmacAes.X86.Mid s₀ k s) :
    WP isa (ctrCall v.callee) s (VG.Proof.CmacAes.X86.After s₀ k) :=
  WP.mono (VG.Proof.CmacAes.X86.ctr_call v h.pre) fun s' hc => by
    have hb : below (s.gpr .esp) 28 = VG.Proof.CmacAes.X86.stkR s₀ := by rw [h.pt.esp]; exact hp.below_eq
    have cA : (VG.Proof.CmacAes.X86.Cb s₀).setWidth 64 = (VG.Proof.CmacAes.X86.S s₀).setWidth 64 + BitVec.ofNat 64 2048 := hp.scrA (by decide)
    have fr := hc.frame
    rw [hb, cA] at fr
    have big : Frame (VG.Proof.CmacAes.X86.Big s₀) s₀.mem s'.mem := h.big.trans (fr.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨VG.Proof.CmacAes.X86.scrR s₀, by simp, UPre.scr_sub (by decide)⟩
      · exact ⟨VG.Proof.CmacAes.X86.stR s₀, by simp, fun _ h => h⟩
      · exact ⟨VG.Proof.CmacAes.X86.scrR s₀, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨VG.Proof.CmacAes.X86.stkR s₀, by simp, fun _ h => h⟩)
    exact ⟨by rw [hc.saved .esi (by simp [calleeSaved]), h.esi],
      ⟨by rw [hc.saved .esp (by simp [calleeSaved]), h.pt.esp], by rw [hc.wr, h.pt.wr],
        fun _ hi => hp.arg_keep big hi⟩⟩

/-- The relation before a block, in two runs. -/
def BRel (s₀ s₀' : State) (k : Nat) (s₁ s₂ : State) : Prop :=
  (k < VG.Proof.CmacAes.X86.N s₀ ∧ VG.Proof.CmacAes.X86.LInv s₀ k s₁) ∧ (k < VG.Proof.CmacAes.X86.N s₀' ∧ VG.Proof.CmacAes.X86.LInv s₀' k s₂)

theorem body_ct {s₀ s₀' : State} (hp : VG.Proof.CmacAes.X86.UPre s₀) (hp' : VG.Proof.CmacAes.X86.UPre s₀') (hq : updateX86.pub s₀ s₀') (k : Nat) :
    RelCT isa (VG.Proof.CmacAes.X86.BRel s₀ s₀' k) (body v.callee) fun _ _ => True := by
  have a := ((RelCT.taint (A := taint) (P := VG.Proof.CmacAes.X86.BRel s₀ s₀' k) (argTaint [.esi] (4 + 4 * 6))
    (fun _ _ h => Pt.agree hq hp hp' (h.1.2.pt hp) (h.2.2.pt hp') fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.2.esi, h.2.2.esi, VG.Proof.CmacAes.X86.pub_Dp hq])
    (c := .block chainIn) (by taint_decide)).wp (F₁ := VG.Proof.CmacAes.X86.Mid s₀ k) (F₂ := VG.Proof.CmacAes.X86.Mid s₀' k)
      fun _ _ h => ⟨VG.Proof.CmacAes.X86.bodyMid_wp hp h.1.1 h.1.2, VG.Proof.CmacAes.X86.bodyMid_wp hp' h.2.1 h.2.2⟩).mono (fun _ _ h => h)
      fun _ _ h => h.2
  have c := ((VG.Proof.CmacAes.X86.ctr_rel v (E := VG.Proof.CmacAes.X86.E s₀) (P := fun s₁ s₂ => VG.Proof.CmacAes.X86.Mid s₀ k s₁ ∧ VG.Proof.CmacAes.X86.Mid s₀' k s₂) fun s₁ s₂ h =>
      ⟨h.1.pre, by rw [VG.Proof.CmacAes.X86.pub_W hq, VG.Proof.CmacAes.X86.pub_Cb hq, VG.Proof.CmacAes.X86.pub_St hq, VG.Proof.CmacAes.X86.pub_S hq, VG.Proof.CmacAes.X86.pub_R hq]; exact h.2.pre, h.1.pt.esp,
        h.2.pt.esp.trans (VG.Proof.CmacAes.X86.pub_E hq).symm⟩).wp (F₁ := VG.Proof.CmacAes.X86.After s₀ k) (F₂ := VG.Proof.CmacAes.X86.After s₀' k)
      fun _ _ h => ⟨VG.Proof.CmacAes.X86.call_after v hp h.1, VG.Proof.CmacAes.X86.call_after v hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have b := RelCT.taint (A := taint) (P := fun s₁ s₂ => VG.Proof.CmacAes.X86.After s₀ k s₁ ∧ VG.Proof.CmacAes.X86.After s₀' k s₂)
    (argTaint [.esi] (4 + 4 * 6))
    (fun _ _ h => Pt.agree hq hp hp' h.1.pt h.2.pt fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.esi, h.2.esi, VG.Proof.CmacAes.X86.pub_Dp hq])
    (c := .block advance) (by taint_decide)
  exact a.seq (c.seq b)

/-! ## The loop -/

/-- The loop's relation, with the number of iterations left. -/
def LRel (s₀ s₀' : State) (n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ k, n = VG.Proof.CmacAes.X86.N s₀ - k ∧ VG.Proof.CmacAes.X86.BRel s₀ s₀' k s₁ s₂

theorem loop_ct {s₀ s₀' : State} (hp : VG.Proof.CmacAes.X86.UPre s₀) (hp' : VG.Proof.CmacAes.X86.UPre s₀') (hq : updateX86.pub s₀ s₀') (n : Nat) :
    RelCT isa (VG.Proof.CmacAes.X86.LRel s₀ s₀' n) (.loop (body v.callee) .ne) fun s₁ s₂ => VG.Proof.CmacAes.X86.LInv s₀ (VG.Proof.CmacAes.X86.N s₀) s₁ ∧ VG.Proof.CmacAes.X86.LInv s₀' (VG.Proof.CmacAes.X86.N s₀') s₂ := by
  refine RelCT.loop (M := isa) (VG.Proof.CmacAes.X86.LRel s₀ s₀') (fun n => ?_) n
  have hN := VG.Proof.CmacAes.X86.pub_N hq
  refine (RelCT.exists_ fun k => ?_).mono (fun s₁ s₂ (h : VG.Proof.CmacAes.X86.LRel s₀ s₀' n s₁ s₂) => h) fun _ _ h => h
  by_cases hn : n = VG.Proof.CmacAes.X86.N s₀ - k
  swap
  · exact RelCT.of_false fun _ _ h => hn h.1
  subst hn
  have ct := (VG.Proof.CmacAes.X86.body_ct v hp hp' hq k).wp
    (F₁ := fun (s : State) => (VG.Proof.CmacAes.X86.LInv s₀ (k + 1) s ∧ s.zf = some (decide (k + 1 = VG.Proof.CmacAes.X86.N s₀))) ∧ k < VG.Proof.CmacAes.X86.N s₀)
    (F₂ := fun (s : State) => VG.Proof.CmacAes.X86.LInv s₀' (k + 1) s ∧ s.zf = some (decide (k + 1 = VG.Proof.CmacAes.X86.N s₀')))
    fun _ _ h => ⟨WP.mono (VG.Proof.CmacAes.X86.body_ok v hp h.1.1 h.1.2) fun _ r => ⟨r, h.1.1⟩, VG.Proof.CmacAes.X86.body_ok v hp' h.2.1 h.2.2⟩
  refine ct.mono (fun _ _ h => h.2) fun s₁ s₂ ⟨_, ⟨⟨l₁, z₁⟩, hk⟩, ⟨l₂, z₂⟩⟩ => ?_
  have e₁ : isa.eval .ne s₁ = some !decide (k + 1 = VG.Proof.CmacAes.X86.N s₀) := by
    show VG.X86.eval .ne s₁ = _; rw [eval_ne, z₁]; rfl
  have e₂ : isa.eval .ne s₂ = some !decide (k + 1 = VG.Proof.CmacAes.X86.N s₀) := by
    show VG.X86.eval .ne s₂ = _; rw [eval_ne, z₂, ← hN]; rfl
  refine ⟨by rw [e₁, e₂], fun hf => ?_, fun ht => ?_⟩
  · rw [e₁] at hf
    have h0 : k + 1 = VG.Proof.CmacAes.X86.N s₀ := by simpa using hf
    exact ⟨h0 ▸ l₁, by rw [← hN, ← h0]; exact l₂⟩
  · rw [e₁] at ht
    have h0 : k + 1 ≠ VG.Proof.CmacAes.X86.N s₀ := by simpa using ht
    exact ⟨VG.Proof.CmacAes.X86.N s₀ - (k + 1), by omega, k + 1, rfl, ⟨by omega, l₁⟩, ⟨by omega, l₂⟩⟩

/-! ## The whole function -/

theorem update_rel {s₀ s₀' : State} (h0 : updateX86.pre s₀) (h0' : updateX86.pre s₀')
    (hq : updateX86.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (update v.callee) fun _ _ => True := by
  have hp := UPre.of h0
  have hp' := UPre.of h0'
  have hN := VG.Proof.CmacAes.X86.pub_N hq
  have pt₀ : ∀ {t : State}, VG.Proof.CmacAes.X86.UPre t → VG.Proof.CmacAes.X86.Pt t t := fun h => ⟨rfl, rfl, fun _ _ => rfl⟩
  have pro := ((RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') (argTaint [] (4 + 4 * 6))
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      exact Pt.agree hq hp hp' (pt₀ hp) (pt₀ hp') fun r hr => by simp at hr)
    (c := .block setup) (by taint_decide)).wp
    (F₁ := fun (s : State) => VG.Proof.CmacAes.X86.LInv s₀ 0 s ∧ s.zf = some (decide (VG.Proof.CmacAes.X86.N s₀ = 0)))
    (F₂ := fun (s : State) => VG.Proof.CmacAes.X86.LInv s₀' 0 s ∧ s.zf = some (decide (VG.Proof.CmacAes.X86.N s₀' = 0)))
    fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨VG.Proof.CmacAes.X86.prologue_wp hp, VG.Proof.CmacAes.X86.prologue_wp hp'⟩).mono (fun _ _ h => h)
    fun _ _ h => h.2
  have ev {s : State} (h : s.zf = some (decide (VG.Proof.CmacAes.X86.N s₀ = 0))) : isa.eval .e s = some (decide (VG.Proof.CmacAes.X86.N s₀ = 0)) := by
    show VG.X86.eval .e s = _; rw [eval_e, h]
  have ev' {s : State} (h : s.zf = some (decide (VG.Proof.CmacAes.X86.N s₀' = 0))) : isa.eval .e s = some (decide (VG.Proof.CmacAes.X86.N s₀ = 0)) := by
    show VG.X86.eval .e s = _; rw [eval_e, h, hN]
  have nil := RelCT.taint (A := taint)
    (P := fun a b => ((VG.Proof.CmacAes.X86.LInv s₀ 0 a ∧ a.zf = some (decide (VG.Proof.CmacAes.X86.N s₀ = 0))) ∧
      (VG.Proof.CmacAes.X86.LInv s₀' 0 b ∧ b.zf = some (decide (VG.Proof.CmacAes.X86.N s₀' = 0)))) ∧ isa.eval .e a = some true) (argTaint [] (4 + 4 * 6))
    (fun _ _ h => Pt.agree hq hp hp' (h.1.1.1.pt hp) (h.1.2.1.pt hp') fun r hr => by simp at hr)
    (c := .block []) (by taint_decide)
  have mid : RelCT isa (fun a b => (VG.Proof.CmacAes.X86.LInv s₀ 0 a ∧ a.zf = some (decide (VG.Proof.CmacAes.X86.N s₀ = 0))) ∧
      (VG.Proof.CmacAes.X86.LInv s₀' 0 b ∧ b.zf = some (decide (VG.Proof.CmacAes.X86.N s₀' = 0))))
      (.ite .e (.block []) (.loop (body v.callee) .ne)) (fun a b => VG.Proof.CmacAes.X86.LInv s₀ (VG.Proof.CmacAes.X86.N s₀) a ∧ VG.Proof.CmacAes.X86.LInv s₀' (VG.Proof.CmacAes.X86.N s₀') b) := by
    refine RelCT.ite (fun a b h => by rw [ev h.1.2, ev' h.2.2]) ?_ ?_
    · refine (nil.wp (F₁ := VG.Proof.CmacAes.X86.LInv s₀ (VG.Proof.CmacAes.X86.N s₀)) (F₂ := VG.Proof.CmacAes.X86.LInv s₀' (VG.Proof.CmacAes.X86.N s₀')) fun a b h => ?_).mono
        (fun _ _ h => h) fun _ _ h => h.2
      have h0 : VG.Proof.CmacAes.X86.N s₀ = 0 := by
        have := h.2; rw [ev h.1.1.2] at this; simpa using this
      exact ⟨WP.block_nil (h0 ▸ h.1.1.1), WP.block_nil (by rw [← hN, h0]; exact h.1.2.1)⟩
    · refine (VG.Proof.CmacAes.X86.loop_ct v hp hp' hq (VG.Proof.CmacAes.X86.N s₀ - 0)).mono (fun a b h => ⟨0, rfl, ⟨?_, h.1.1.1⟩, ⟨?_, h.1.2.1⟩⟩)
        fun _ _ h => h
      all_goals
        have := h.2; rw [ev h.1.1.2] at this
        have : VG.Proof.CmacAes.X86.N s₀ ≠ 0 := by simpa using this
        omega
  have epi := RelCT.taint (A := taint) (P := fun a b => VG.Proof.CmacAes.X86.LInv s₀ (VG.Proof.CmacAes.X86.N s₀) a ∧ VG.Proof.CmacAes.X86.LInv s₀' (VG.Proof.CmacAes.X86.N s₀') b)
    (argTaint [] (4 + 4 * 6)) (fun _ _ h => Pt.agree hq hp hp' (h.1.pt hp) (h.2.pt hp') fun r hr => by simp at hr)
    (c := .block (restore 5)) (by taint_decide)
  exact pro.seq (mid.seq epi)

theorem update_ct : ConstantTime isa updateX86.pre updateX86.pub (update v.callee) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (VG.Proof.CmacAes.X86.update_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.X86.FinalizeCT`. -/
section

section

/-!
# AES-CMAC on x86: `vg_cmac_aes_finalize` is correct

Before the call, the counter block holds `Mₙ ⊕ C`, for the last block `Mₙ` of
§6.2 step 4 and the chaining value `C` at `state`, and the state is zeroed;
the call leaves `CIPH_K(C ⊕ Mₙ)` there, the MAC (`Cmac.macFull_split`).
-/

namespace VG.Proof.CmacAes.X86

open VG VG.X86 VG.Impl.CmacAes.X86
open VG.Proof.Aes.X86 (Ctr32Impl)

variable (v : Ctr32Impl)
open VG.Proof.MdStream.X86 (Upd wp_mov wp_movi wp_addi eval_e)

/-! ## Up to the call -/

/-- What the code before the call leaves. -/
structure FMid (s₀ s : State) : Prop where
  pre : VG.Proof.CmacAes.X86.CtrPre s (VG.Proof.CmacAes.X86.W s₀) (VG.Proof.CmacAes.X86.S s₀ + BitVec.ofNat 32 2048) (VG.Proof.CmacAes.X86.St s₀) (VG.Proof.CmacAes.X86.S s₀) (VG.Proof.CmacAes.X86.R s₀)
  blk : Spec.Aes.bytesAt s.mem (VG.Proof.CmacAes.X86.Ca s₀) 16 =
    Spec.Cmac.xor (VG.Proof.CmacAes.X86.mn s₀) (Spec.Aes.bytesAt s₀.mem ((VG.Proof.CmacAes.X86.St s₀).setWidth 64) 16)
  frame : Frame [⟨VG.Proof.CmacAes.X86.Ca s₀, 16⟩, VG.Proof.CmacAes.X86.stR s₀] (VG.Proof.CmacAes.X86.savedMem s₀) s.mem
  esp : s.gpr .esp = VG.Proof.CmacAes.X86.E s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem finArgs_eq : finArgs = .mov .ebx (argOp 2) :: (xor4 .ebp .ebx .ebp 2048 0 2048 ++ (zero4 .ebx 0 ++ ctrArgs)) :=
  rfl

theorem finArgs_wp {s₀ : State} (hp : VG.Proof.CmacAes.X86.FPre s₀) {s : State} (h : VG.Proof.CmacAes.X86.BPost s₀ s) :
    WP isa (.block finArgs) s (VG.Proof.CmacAes.X86.FMid s₀) := by
  have sf := hp.scr_fit
  have tf := hp.st_fit
  have hR := hp.rounds
  have cA := hp.cA
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  have cSt : (⟨VG.Proof.CmacAes.X86.Ca s₀, 16⟩ : Region).Disjoint (VG.Proof.CmacAes.X86.stR s₀) := hp.st_scr.symm.sub_left (Offset.sub_base _ (by decide))
  have wSt : Covers [VG.Proof.CmacAes.X86.stR s₀] s₀.wr := by
    rw [hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.CmacAes.X86.stR s₀, by simp, 0, by simp, by simp⟩
  have big : Frame (VG.Proof.CmacAes.X86.Big s₀) s₀.mem s.mem :=
    (VG.Proof.CmacAes.X86.savedMem_big s₀).trans (h.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.CmacAes.X86.scrR s₀, by simp, Offset.sub_base _ (by decide)⟩)
  rw [VG.Proof.CmacAes.X86.finArgs_eq]
  refine VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀) h.esp (by rw [hrw]; exact hp.arg_in (by decide)) (hp.arg_keep big (by decide))
    fun s₁ u₁ => ?_
  have b₁ : s₁.gpr .ebx = VG.Proof.CmacAes.X86.St s₀ := u₁.gpr
  have p₁ : s₁.gpr .ebp = VG.Proof.CmacAes.X86.S s₀ := by rw [u₁.other _ (by decide), h.ebp]
  have rw₁ : s₁.rd ++ s₁.wr = s₀.rd ++ s₀.wr := by rw [u₁.rd, u₁.wr, hrw]
  refine VG.Proof.CmacAes.X86.xor4_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [p₁]; omega) (by rw [b₁]; omega) (by rw [p₁]; omega)
    (by
      rw [p₁, rw₁]
      exact fun a n hi => (hp.cS (d := 2048) (n := 16) (by decide)) a n hi |>
        fun ⟨r, hr, hc⟩ => ⟨r, List.mem_append_right _ hr, hc⟩)
    (by
      rw [b₁, VG.Proof.CmacAes.X86.add0, rw₁]
      exact fun a n hi => wSt a n hi |> fun ⟨r, hr, hc⟩ => ⟨r, List.mem_append_right _ hr, hc⟩)
    (by rw [p₁, u₁.wr, h.wr]; exact hp.cS (by decide)) fun s₂ g₂ => ?_
  have b₂ : s₂.gpr .ebx = VG.Proof.CmacAes.X86.St s₀ := by rw [g₂.gpr _ (by decide) (by decide), b₁]
  refine VG.Proof.CmacAes.X86.zero4_ok (by decide) (by rw [b₂]; omega) (by rw [b₂, VG.Proof.CmacAes.X86.add0, g₂.wr, u₁.wr, h.wr]; exact wSt)
    fun s₃ g₃ m₃ rd₃ wr₃ => ?_
  have esp₃ : s₃.gpr .esp = VG.Proof.CmacAes.X86.E s₀ := by
    rw [g₃ _ (by decide), g₂.gpr _ (by decide) (by decide), u₁.other _ (by decide), h.esp]
  have rd₃' : s₃.rd = s₀.rd := by rw [rd₃, g₂.rd, u₁.rd, h.rd]
  have wr₃' : s₃.wr = s₀.wr := by rw [wr₃, g₂.wr, u₁.wr, h.wr]
  have mem₃ : s₃.mem = Proof.Cmac.zero4 (Proof.Cmac.xor4Mem s.mem (VG.Proof.CmacAes.X86.Ca s₀) (VG.Proof.CmacAes.X86.Ca s₀) ((VG.Proof.CmacAes.X86.St s₀).setWidth 64))
      ((VG.Proof.CmacAes.X86.St s₀).setWidth 64) := by
    rw [m₃, b₂, VG.Proof.CmacAes.X86.add0, g₂.mem, p₁, b₁, VG.Proof.CmacAes.X86.add0, u₁.mem]
  have fr₃ : Frame [⟨VG.Proof.CmacAes.X86.Ca s₀, 16⟩, VG.Proof.CmacAes.X86.stR s₀] (VG.Proof.CmacAes.X86.savedMem s₀) s₃.mem := by
    rw [mem₃]
    exact ((h.frame.trans (Proof.Cmac.xor4Mem_frame _ _ _ _)).mono (by simp)).trans
      ((Proof.Cmac.frame_store4 _ _ _ _ _).mono (by simp))
  have big₃ : Frame (VG.Proof.CmacAes.X86.Big s₀) s₀.mem s₃.mem :=
    (VG.Proof.CmacAes.X86.savedMem_big s₀).trans (fr₃.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨VG.Proof.CmacAes.X86.scrR s₀, by simp, Offset.sub_base _ (by decide)⟩
      · exact ⟨VG.Proof.CmacAes.X86.stR s₀, by simp, fun _ h => h⟩)
  rw [VG.Proof.CmacAes.X86.ctrArgs_eq]
  refine VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀) esp₃ (by rw [rd₃', wr₃']; exact hp.arg_in (by decide)) (hp.arg_keep big₃ (by decide))
    fun s₄ u₄ => ?_
  refine VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀) (by rw [u₄.other _ (by decide), esp₃])
    (by rw [u₄.rd, u₄.wr, rd₃', wr₃']; exact hp.arg_in (by decide))
    (by rw [u₄.mem]; exact hp.arg_keep big₃ (by decide)) fun s₅ u₅ => ?_
  refine wp_mov fun s₆ u₆ => wp_addi fun s₇ u₇ => wp_movi fun s₈ u₈ => WP.block_nil ?_
  have keep : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → s₈.gpr r = s₃.gpr r := fun r ha hc hd hi => by
    rw [u₈.other _ hi, u₇.other _ hd, u₆.other _ hd, u₅.other _ hc, u₄.other _ ha]
  have p₃ : s₃.gpr .ebp = VG.Proof.CmacAes.X86.S s₀ := by rw [g₃ _ (by decide), g₂.gpr _ (by decide) (by decide), p₁]
  have b₃ : s₃.gpr .ebx = VG.Proof.CmacAes.X86.St s₀ := by rw [g₃ _ (by decide), b₂]
  have sp₈ : s₈.gpr .esp = VG.Proof.CmacAes.X86.E s₀ := by rw [keep _ (by decide) (by decide) (by decide) (by decide), esp₃]
  have rd₈ : s₈.rd = s₀.rd := by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, rd₃']
  have wr₈ : s₈.wr = s₀.wr := by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, wr₃']
  have mem₈ : s₈.mem = s₃.mem := by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem]
  have hb : below (s₈.gpr .esp) 28 = VG.Proof.CmacAes.X86.stkR s₀ := by rw [sp₈]; exact hp.below_eq
  have stS : Spec.Aes.bytesAt s.mem ((VG.Proof.CmacAes.X86.St s₀).setWidth 64) 16 =
      Spec.Aes.bytesAt s₀.mem ((VG.Proof.CmacAes.X86.St s₀).setWidth 64) 16 :=
    Proof.Cmac.bytesAt_frame16 ((VG.Proof.CmacAes.X86.savedMem_frame s₀).trans (h.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.CmacAes.X86.scrR s₀, List.mem_singleton_self _, Offset.sub_base _ (by decide)⟩)) fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.st_scr
  refine ⟨⟨?_, ?_, ?_, ?_, u₈.gpr, ?_, hR, by rw [sp₈]; exact hp.esp28, ?_,
    hp.key_st.sub_left (Region.sub_prefix (by decide)),
    (hp.key_scr.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide)),
    by rw [cA]; exact cSt, by rw [cA]; exact Offset.disjoint_base _ (by decide) (by omega),
    hp.st_scr.sub_right (Region.sub_prefix (by decide)),
    by rw [hb]; exact hp.b_key.sub_right (Region.sub_prefix (by decide)),
    by rw [hb, cA]; exact hp.b_scr.sub_right (Offset.sub_base _ (by decide)), by rw [hb]; exact hp.b_st,
    by rw [hb]; exact hp.b_scr.sub_right (Region.sub_prefix (by decide)), by have := hp.key_fit; omega, ?_, tf,
    by omega, ?_, ?_, ?_⟩, ?_, ?_, sp₈, rd₈, wr₈⟩
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr]; exact VG.Proof.CmacAes.X86.arg_ofNat s₀ 1
  · rw [u₈.other _ (by decide), u₇.gpr, u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), p₃]
  · rw [keep _ (by decide) (by decide) (by decide) (by decide), b₃]
  · rw [keep _ (by decide) (by decide) (by decide) (by decide), p₃]
  · rw [cA]; exact (hp.ca_key (d := 0) (n := 240) (by decide)).symm |> fun d => by simpa using d
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 2048) (by decide),
      Nat.mod_eq_of_lt (by omega)]; omega
  · rw [rd₈, wr₈, hp.rd]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.CmacAes.X86.keyR s₀, by simp, 0, by simp, by simp⟩
  · rw [wr₈, hp.wr, cA]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨VG.Proof.CmacAes.X86.scrR s₀, by simp, 2048, rfl, by simp⟩
    · exact ⟨VG.Proof.CmacAes.X86.stR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨VG.Proof.CmacAes.X86.scrR s₀, by simp, 0, by simp, by simp⟩
  · rw [mem₈, mem₃]; exact Proof.Cmac.zero4_bytes _ _
  · rw [mem₈, mem₃, Proof.Cmac.zero4, Proof.Cmac.bytesAt_frame16 (Proof.Cmac.frame_store4 _ _ _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact cSt),
      Proof.Cmac.xor4Mem_bytes _ (Proof.Cmac.Sep4.self _) (Proof.Cmac.Sep4.of_disjoint cSt), h.blk, stS]
  · rw [mem₈]; exact fr₃

theorem finPre_wp {s₀ : State} (hp : VG.Proof.CmacAes.X86.FPre s₀) : WP isa finPre s₀ (VG.Proof.CmacAes.X86.FMid s₀) := by
  refine WP.seq (WP.mono (VG.Proof.CmacAes.X86.finSave_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (Q := VG.Proof.CmacAes.X86.BPost s₀) ?_ fun _ h => VG.Proof.CmacAes.X86.finArgs_wp hp h)
  have ev : isa.eval .e s₁ = some (decide (VG.Proof.CmacAes.X86.N s₀ = 16)) := by
    show VG.X86.eval .e s₁ = _; rw [eval_e, h₁.zf]
  by_cases hL : VG.Proof.CmacAes.X86.N s₀ = 16
  · exact WP.ite true (by rw [ev]; simp [hL]) (fun _ => VG.Proof.CmacAes.X86.full_wp hp hL h₁) (fun h => by cases h)
  · exact WP.ite false (by rw [ev]; simp [hL]) (fun h => by cases h)
      (fun _ => VG.Proof.CmacAes.X86.partial_wp hp (by have := hp.len; omega) h₁)

/-! ## The whole function -/

theorem finalize_wp {s₀ : State} (h0 : finalizeX86.pre s₀) :
    WP isa (finalize v.callee) s₀ fun s' => abiPreserved s₀ s' ∧ finalizeX86.post s₀ s' := by
  have hp := FPre.of h0
  have hR := hp.rounds
  have hRb : 16 * (VG.Proof.CmacAes.X86.R s₀ + 1) ≤ 240 := by rcases hR with h | h | h <;> omega
  have hsc : (VG.X86.arg s₀ 5).toNat + 2176 ≤ 2 ^ 32 := hp.scr_fit
  have cA := hp.cA
  unfold finalize
  refine WP.seq (WP.mono (VG.Proof.CmacAes.X86.finPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (VG.Proof.CmacAes.X86.ctr_call v h₁.pre) fun s₂ h₂ => ?_)
  have hb : below (s₁.gpr .esp) 28 = VG.Proof.CmacAes.X86.stkR s₀ := by rw [h₁.esp]; exact hp.below_eq
  have f₁ : Frame [VG.Proof.CmacAes.X86.stR s₀, ⟨(VG.Proof.CmacAes.X86.S s₀).setWidth 64, 2064⟩, VG.Proof.CmacAes.X86.stkR s₀] (VG.Proof.CmacAes.X86.savedMem s₀) s₁.mem :=
    h₁.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨(VG.Proof.CmacAes.X86.S s₀).setWidth 64, 2064⟩, by simp, Offset.sub_base _ (by decide)⟩
      · exact ⟨VG.Proof.CmacAes.X86.stR s₀, by simp, fun _ h => h⟩
  have f₂ : Frame [VG.Proof.CmacAes.X86.stR s₀, ⟨(VG.Proof.CmacAes.X86.S s₀).setWidth 64, 2064⟩, VG.Proof.CmacAes.X86.stkR s₀] (VG.Proof.CmacAes.X86.savedMem s₀) s₂.mem := by
    have fr := h₂.frame
    rw [hb, cA] at fr
    refine f₁.trans (fr.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨⟨(VG.Proof.CmacAes.X86.S s₀).setWidth 64, 2064⟩, by simp, Offset.sub_base _ (by decide)⟩
    · exact ⟨VG.Proof.CmacAes.X86.stR s₀, by simp, fun _ h => h⟩
    · exact ⟨⟨(VG.Proof.CmacAes.X86.S s₀).setWidth 64, 2064⟩, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨VG.Proof.CmacAes.X86.stkR s₀, by simp, fun _ h => h⟩
  have big₁ := UPre.big_of f₁
  have big₂ := UPre.big_of f₂
  have esp₂ : s₂.gpr .esp = VG.Proof.CmacAes.X86.E s₀ := by rw [h₂.saved .esp (by simp [calleeSaved]), h₁.esp]
  have rdwr₂ : s₂.rd ++ s₂.wr = [VG.Proof.CmacAes.X86.keyR s₀, VG.Proof.CmacAes.X86.lastR s₀, VG.Proof.CmacAes.X86.argsR s₀, VG.Proof.CmacAes.X86.stR s₀, VG.Proof.CmacAes.X86.scrR s₀] := by
    rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr, hp.rd, hp.wr]; rfl
  have hrw₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr]
  have sl : ∀ r d, (r, d) ∈ saved → s₂.mem.readW ((VG.Proof.CmacAes.X86.S s₀).setWidth 64 + BitVec.ofNat 64 d) 32 = s₀.gpr r := by
    intro r d hrd
    have hb := VG.Proof.CmacAes.X86.saved_bound _ hrd
    rw [f₂.readW (r := ⟨(VG.Proof.CmacAes.X86.S s₀).setWidth 64 + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.st_scr.symm.sub_left (UPre.scr_sub (by omega))
      · exact Offset.disjoint_base _ hb.1 (by omega)
      · exact hp.b_scr.symm.sub_left (UPre.scr_sub (by omega))) (by decide), VG.Proof.CmacAes.X86.savedMem_slot s₀ hrd]
  have sch : Spec.Aes.bytesAt s₁.mem ((VG.Proof.CmacAes.X86.W s₀).setWidth 64) (16 * (VG.Proof.CmacAes.X86.R s₀ + 1)) =
      Spec.Aes.bytesAt s₀.mem ((VG.Proof.CmacAes.X86.W s₀).setWidth 64) (16 * (VG.Proof.CmacAes.X86.R s₀ + 1)) :=
    Proof.Cmac.bytesAt_frame big₁ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.key_st.sub_left (Region.sub_prefix (by omega))
      · exact hp.key_scr.sub_left (Region.sub_prefix (by omega))
      · exact hp.b_key.symm.sub_left (Region.sub_prefix (by omega))) (by omega)
  rw [VG.Proof.CmacAes.X86.restore_eq]
  refine VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀) esp₂ (by rw [hrw₂]; exact hp.arg_in (by decide)) (hp.arg_keep big₂ (by decide))
    fun s₃ u₃ => ?_
  refine Spill.restore_ofNat_ok saved VG.Proof.CmacAes.X86.saved_fits (by rw [u₃.gpr]; omega) VG.Proof.CmacAes.X86.saved_ne_eax (fun p hp' => ?_)
    (fun p hp' => by rw [u₃.gpr, u₃.mem]; exact sl p.1 p.2 hp') fun s₄ r₄ => WP.block_nil ?_
  · have hb := VG.Proof.CmacAes.X86.saved_bound p hp'
    rw [u₃.gpr, u₃.rd, u₃.wr, rdwr₂]
    exact ⟨VG.Proof.CmacAes.X86.scrR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  refine ⟨⟨r₄.abi (by decide) (by decide) (by rw [u₃.other _ (by decide), esp₂]), ?_⟩, ?_⟩
  · rw [r₄.mem, u₃.mem]
    have rs : (VG.Proof.CmacAes.X86.retR s₀).Disjoint (VG.Proof.CmacAes.X86.stkR s₀) := by
      have := Offset.disjoint_below_above ((VG.Proof.CmacAes.X86.E s₀).setWidth 64) (m := 28) (a := 0) (l := 4) (by decide)
      rw [VG.Proof.CmacAes.X86.add0] at this
      exact this.symm
    exact big₂.readW (r := VG.Proof.CmacAes.X86.retR s₀) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.ret_st
      · exact hp.ret_scr
      · exact rs) (by decide)
  · intro hk msg hm hne hst
    have hk' : Spec.Aes.bytesAt s₀.mem ((VG.Proof.CmacAes.X86.W s₀).setWidth 64 + BitVec.ofNat 64 240) 32 =
        (Spec.Cmac.subkeys (VG.Proof.CmacAes.X86.ciph s₀) 16).1 ++ (Spec.Cmac.subkeys (VG.Proof.CmacAes.X86.ciph s₀) 16).2 := hk
    obtain ⟨e1, e2⟩ := Proof.Cmac.k1k2 (Proof.Cmac.subkeys_aes_length _ _) hk'
    show Spec.Aes.bytesAt s₄.mem ((VG.Proof.CmacAes.X86.St s₀).setWidth 64) 16 = _
    rw [r₄.mem, u₃.mem, h₂.out, sch, cA, h₁.blk, VG.Proof.CmacAes.X86.mn, e1, e2, hst,
      Proof.Cmac.macFull_split _ hm (by rw [Proof.Cmac.bytesAt_length]; exact hp.len)
        (by rw [Proof.Cmac.bytesAt_length]; exact hne), Proof.Cmac.xor_comm]

end VG.Proof.CmacAes.X86

end

/-!
# AES-CMAC on x86: `vg_cmac_aes_finalize` is constant time

The code before the call is checked by the taint analysis, from `esp` and the
stack arguments (its branches and the copy loop depend only on `last_len`),
the call of `vg_aes_ctr32`, in its frame, is constant time by its own proof
(`ctr_rel`), its arguments pinned by the correctness proof (`FMid`), and the
restore after it by the taint analysis again.
-/

namespace VG.Proof.CmacAes.X86

open VG VG.X86 VG.Impl.CmacAes.X86
open VG.Proof.Aes.X86 (Ctr32Impl)

variable (v : Ctr32Impl)

theorem FPre.argsOut {s₀ : State} (hp : VG.Proof.CmacAes.X86.FPre s₀) {s : State} (hesp : s.gpr .esp = VG.Proof.CmacAes.X86.E s₀) (hwr : s.wr = s₀.wr) :
    ArgsOut 6 s := by
  have hs : (s₀.gpr .esp).toNat + 28 ≤ 2 ^ 32 := hp.esp_fit
  refine ⟨by rw [hesp]; omega, ?_⟩
  rw [hwr, hp.wr, hesp]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega) hp.ret_st hp.args_st
  · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega) hp.ret_scr hp.args_scr

/-- Two runs agree on `esp`, the stack arguments and the registers `rs`. -/
theorem fagree {s₀ s₀' : State} (hq : finalizeX86.pub s₀ s₀') (hp : VG.Proof.CmacAes.X86.FPre s₀) (hp' : VG.Proof.CmacAes.X86.FPre s₀') {rs : List Reg}
    {s₁ s₂ : State} (h₁ : VG.Proof.CmacAes.X86.Pt s₀ s₁) (h₂ : VG.Proof.CmacAes.X86.Pt s₀' s₂) (hr : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) :
    VG.X86.Taint.Agree (argTaint rs (4 + 4 * 6)) s₁ s₂ :=
  agree_argTaint hr (by rw [h₁.esp, h₂.esp]; exact hq.1) (hp.argsOut h₁.esp h₁.wr) (hp'.argsOut h₂.esp h₂.wr)
    fun i hi => by rw [VG.Proof.CmacAes.X86.arg_cur (h₁.esp) (h₁.args i hi), VG.Proof.CmacAes.X86.arg_cur (h₂.esp) (h₂.args i hi), hq.2 i hi]

theorem FMid.f {s₀ s : State} (h : VG.Proof.CmacAes.X86.FMid s₀ s) :
    Frame [VG.Proof.CmacAes.X86.stR s₀, ⟨(VG.Proof.CmacAes.X86.S s₀).setWidth 64, 2064⟩, VG.Proof.CmacAes.X86.stkR s₀] (VG.Proof.CmacAes.X86.savedMem s₀) s.mem :=
  h.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨(VG.Proof.CmacAes.X86.S s₀).setWidth 64, 2064⟩, by simp, Offset.sub_base _ (by decide)⟩
    · exact ⟨VG.Proof.CmacAes.X86.stR s₀, by simp, fun _ h => h⟩

theorem FMid.pt {s₀ : State} (hp : VG.Proof.CmacAes.X86.FPre s₀) {s : State} (h : VG.Proof.CmacAes.X86.FMid s₀ s) : VG.Proof.CmacAes.X86.Pt s₀ s :=
  ⟨h.esp, h.wr, fun _ hi => hp.arg_keep (UPre.big_of h.f) hi⟩

theorem fcall_after {s₀ : State} (hp : VG.Proof.CmacAes.X86.FPre s₀) {s : State} (h : VG.Proof.CmacAes.X86.FMid s₀ s) : WP isa (ctrCall v.callee) s (VG.Proof.CmacAes.X86.Pt s₀) :=
  WP.mono (VG.Proof.CmacAes.X86.ctr_call v h.pre) fun s' hc => by
    have hb : below (s.gpr .esp) 28 = VG.Proof.CmacAes.X86.stkR s₀ := by rw [h.esp]; exact hp.below_eq
    have fr := hc.frame
    rw [hb, hp.cA] at fr
    have big := UPre.big_of (h.f.trans (fr.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨(VG.Proof.CmacAes.X86.S s₀).setWidth 64, 2064⟩, by simp, Offset.sub_base _ (by decide)⟩
      · exact ⟨VG.Proof.CmacAes.X86.stR s₀, by simp, fun _ h => h⟩
      · exact ⟨⟨(VG.Proof.CmacAes.X86.S s₀).setWidth 64, 2064⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨VG.Proof.CmacAes.X86.stkR s₀, by simp, fun _ h => h⟩))
    exact ⟨by rw [hc.saved .esp (by simp [calleeSaved]), h.esp], by rw [hc.wr, h.wr],
      fun _ hi => hp.arg_keep big hi⟩

theorem finalize_rel {s₀ s₀' : State} (h0 : finalizeX86.pre s₀) (h0' : finalizeX86.pre s₀')
    (hq : finalizeX86.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (finalize v.callee) fun _ _ => True := by
  have hp := FPre.of h0
  have hp' := FPre.of h0'
  have eW : VG.Proof.CmacAes.X86.W s₀ = VG.Proof.CmacAes.X86.W s₀' := hq.2 0 (by decide)
  have eR : VG.Proof.CmacAes.X86.R s₀ = VG.Proof.CmacAes.X86.R s₀' := by rw [VG.Proof.CmacAes.X86.R, VG.Proof.CmacAes.X86.R, hq.2 1 (by decide)]
  have eSt : VG.Proof.CmacAes.X86.St s₀ = VG.Proof.CmacAes.X86.St s₀' := hq.2 2 (by decide)
  have eS : VG.Proof.CmacAes.X86.S s₀ = VG.Proof.CmacAes.X86.S s₀' := hq.2 5 (by decide)
  have pt₀ : ∀ {t : State}, VG.Proof.CmacAes.X86.Pt t t := ⟨rfl, rfl, fun _ _ => rfl⟩
  have a := ((RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') (argTaint [] (4 + 4 * 6))
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      exact VG.Proof.CmacAes.X86.fagree hq hp hp' pt₀ pt₀ fun r hr => by simp at hr)
    (c := finPre) (by taint_decide)).wp (F₁ := VG.Proof.CmacAes.X86.FMid s₀) (F₂ := VG.Proof.CmacAes.X86.FMid s₀')
    fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨VG.Proof.CmacAes.X86.finPre_wp hp, VG.Proof.CmacAes.X86.finPre_wp hp'⟩).mono (fun _ _ h => h)
    fun _ _ h => h.2
  have c := ((VG.Proof.CmacAes.X86.ctr_rel v (E := VG.Proof.CmacAes.X86.E s₀) (P := fun s₁ s₂ => VG.Proof.CmacAes.X86.FMid s₀ s₁ ∧ VG.Proof.CmacAes.X86.FMid s₀' s₂) fun s₁ s₂ h =>
      ⟨h.1.pre, by rw [eW, eS, eSt, eR]; exact h.2.pre, h.1.esp, h.2.esp.trans hq.1.symm⟩).wp
      (F₁ := VG.Proof.CmacAes.X86.Pt s₀) (F₂ := VG.Proof.CmacAes.X86.Pt s₀') fun _ _ h => ⟨VG.Proof.CmacAes.X86.fcall_after v hp h.1, VG.Proof.CmacAes.X86.fcall_after v hp' h.2⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  have b := RelCT.taint (A := taint) (P := fun s₁ s₂ => VG.Proof.CmacAes.X86.Pt s₀ s₁ ∧ VG.Proof.CmacAes.X86.Pt s₀' s₂) (argTaint [] (4 + 4 * 6))
    (fun _ _ h => VG.Proof.CmacAes.X86.fagree hq hp hp' h.1 h.2 fun r hr => by simp at hr)
    (c := .block (restore 5)) (by taint_decide)
  exact a.seq (c.seq b)

theorem finalize_ct : ConstantTime isa finalizeX86.pre finalizeX86.pub (finalize v.callee) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (VG.Proof.CmacAes.X86.finalize_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.X86.Subkeys`. -/
section

section

/-!
# AES-CMAC on x86: doubling a block in four 32-bit words

`dbl src dst` loads a block as four byte-reversed words (`bswap`), the block
as a big-endian integer (`Cmac.ofBytes_rev4`), doubles the integer a word at a
time (`Cmac.dbl_words4`, shifting by `add r, r`), and stores the words
byte-reversed again (`Cmac.le4_rev4`).
-/

namespace VG.Proof.CmacAes.X86

open VG VG.X86 VG.Impl.CmacAes.X86
open VG.Proof.MdStream.X86 (Upd Mupd wp_mov wp_movi wp_movm wp_store wp_add wp_sub wp_andi wp_or wp_shr wp_bswap)

theorem bswap_eq (a : BitVec 32) : bswap a = byteRev32 a := rfl

theorem add_self_shl (x : BitVec 32) : x + x = x <<< 1 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

/-- The memory after `dbl src dst`, with `ebx` pointing at `A`. -/
def dblMem (m : Mem) (A : Addr) (src dst : Nat) : Mem :=
  let P := A + BitVec.ofNat 64 src
  let b₀ := byteRev32 (m.readW P 32)
  let b₁ := byteRev32 (m.readW (P + BitVec.ofNat 64 4) 32)
  let b₂ := byteRev32 (m.readW (P + BitVec.ofNat 64 8) 32)
  let b₃ := byteRev32 (m.readW (P + BitVec.ofNat 64 12) 32)
  Proof.Cmac.store4 m (A + BitVec.ofNat 64 dst) (byteRev32 (Proof.Cmac.dblW0 b₀ b₁))
    (byteRev32 (Proof.Cmac.dblW0 b₁ b₂)) (byteRev32 (Proof.Cmac.dblW0 b₂ b₃)) (byteRev32 (Proof.Cmac.dblW3 b₀ b₃))

theorem dblMem_frame (m : Mem) (A : Addr) (src dst : Nat) :
    Frame [⟨A + BitVec.ofNat 64 dst, 16⟩] m (VG.Proof.CmacAes.X86.dblMem m A src dst) :=
  Proof.Cmac.frame_store4 _ _ _ _ _

theorem dblMem_bytes (m : Mem) (A : Addr) (src dst : Nat) :
    Spec.Aes.bytesAt (VG.Proof.CmacAes.X86.dblMem m A src dst) (A + BitVec.ofNat 64 dst) 16 =
      Spec.Cmac.dbl 16 (Spec.Aes.bytesAt m (A + BitVec.ofNat 64 src) 16) := by
  simp only [VG.Proof.CmacAes.X86.dblMem]
  rw [Proof.Cmac.bytesAt_store4, Proof.Cmac.le4_rev4, Proof.Cmac.dbl_words4,
    Proof.Cmac.dbl_eq (Proof.Cmac.bytesAt_length _ _ _), Proof.Cmac.ofBytes_rev4]

/-- `dbl src dst`, with `ebx` pointing at `K`. -/
theorem dbl_wp {is : List Instr} {s : State} {Q : State → Prop} {K : BitVec 32} {src dst : Nat}
    (hb : s.gpr .ebx = K) (fs : K.toNat + src + 16 ≤ 2 ^ 32) (fd : K.toNat + dst + 16 ≤ 2 ^ 32)
    (rS : Covers [⟨K.setWidth 64 + BitVec.ofNat 64 src, 16⟩] (s.rd ++ s.wr))
    (wD : Covers [⟨K.setWidth 64 + BitVec.ofNat 64 dst, 16⟩] s.wr)
    (k : ∀ s', (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .esi → r ≠ .edi → r ≠ .ebp → s'.gpr r = s.gpr r) →
      s'.mem = VG.Proof.CmacAes.X86.dblMem s.mem (K.setWidth 64) src dst → s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (dbl src dst ++ is)) s Q := by
  simp only [dbl, List.cons_append, List.nil_append]
  refine wp_movm (a := K.setWidth 64 + BitVec.ofNat 64 src) (by rw [VG.Proof.CmacAes.X86.ea_at', hb]; exact addr_eq (by omega))
    (VG.Proof.CmacAes.X86.in_word0 rS) fun s₁ u₁ => ?_
  refine wp_movm (a := K.setWidth 64 + BitVec.ofNat 64 src + BitVec.ofNat 64 4)
    (by rw [VG.Proof.CmacAes.X86.ea_at', u₁.other _ (by decide), hb]; exact VG.Proof.CmacAes.X86.addr_word 4 fs (by decide))
    (by rw [u₁.rd, u₁.wr]; exact VG.Proof.CmacAes.X86.in_word rS (by decide)) fun s₂ u₂ => ?_
  refine wp_movm (a := K.setWidth 64 + BitVec.ofNat 64 src + BitVec.ofNat 64 8)
    (by rw [VG.Proof.CmacAes.X86.ea_at', u₂.other _ (by decide), u₁.other _ (by decide), hb]; exact VG.Proof.CmacAes.X86.addr_word 8 fs (by decide))
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact VG.Proof.CmacAes.X86.in_word rS (by decide)) fun s₃ u₃ => ?_
  refine wp_movm (a := K.setWidth 64 + BitVec.ofNat 64 src + BitVec.ofNat 64 12)
    (by rw [VG.Proof.CmacAes.X86.ea_at', u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hb]
        exact VG.Proof.CmacAes.X86.addr_word 12 fs (by decide))
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact VG.Proof.CmacAes.X86.in_word rS (by decide)) fun s₄ u₄ => ?_
  refine wp_bswap fun s₅ u₅ => wp_bswap fun s₆ u₆ => wp_bswap fun s₇ u₇ => wp_bswap fun s₈ u₈ => ?_
  refine wp_mov fun s₉ u₉ => wp_shr (by decide) fun s₁₀ u₁₀ => wp_movi fun s₁₁ u₁₁ =>
    wp_sub fun s₁₂ u₁₂ _ => wp_andi fun s₁₃ u₁₃ => ?_
  refine wp_add fun s₁₄ u₁₄ => wp_mov fun s₁₅ u₁₅ => wp_shr (by decide) fun s₁₆ u₁₆ => wp_or fun s₁₇ u₁₇ => ?_
  refine wp_add fun s₁₈ u₁₈ => wp_mov fun s₁₉ u₁₉ => wp_shr (by decide) fun s₂₀ u₂₀ => wp_or fun s₂₁ u₂₁ => ?_
  refine wp_add fun s₂₂ u₂₂ => wp_mov fun s₂₃ u₂₃ => wp_shr (by decide) fun s₂₄ u₂₄ => wp_or fun s₂₅ u₂₅ => ?_
  refine wp_add fun s₂₆ u₂₆ => VG.Proof.CmacAes.X86.wp_xor fun s₂₇ u₂₇ => ?_
  refine wp_bswap fun s₂₈ u₂₈ => wp_bswap fun s₂₉ u₂₉ => wp_bswap fun s₃₀ u₃₀ => wp_bswap fun s₃₁ u₃₁ => ?_
  have g : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .esi → r ≠ .edi → r ≠ .ebp → s₃₁.gpr r = s.gpr r :=
    fun r ha hc hd hs hi hp => by
      rw [u₃₁.other _ hs, u₃₀.other _ hd, u₂₉.other _ hc, u₂₈.other _ ha, u₂₇.other _ hs, u₂₆.other _ hs,
        u₂₅.other _ hd, u₂₄.other _ hi, u₂₃.other _ hi, u₂₂.other _ hd, u₂₁.other _ hc, u₂₀.other _ hi,
        u₁₉.other _ hi, u₁₈.other _ hc, u₁₇.other _ ha, u₁₆.other _ hi, u₁₅.other _ hi, u₁₄.other _ ha,
        u₁₃.other _ hp, u₁₂.other _ hp, u₁₁.other _ hp, u₁₀.other _ hi, u₉.other _ hi, u₈.other _ hs,
        u₇.other _ hd, u₆.other _ hc, u₅.other _ ha, u₄.other _ hs, u₃.other _ hd, u₂.other _ hc, u₁.other _ ha]
  have gb : s₃₁.gpr .ebx = K := by
    rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hb]
  have m31 : s₃₁.mem = s.mem := by
    rw [u₃₁.mem, u₃₀.mem, u₂₉.mem, u₂₈.mem, u₂₇.mem, u₂₆.mem, u₂₅.mem, u₂₄.mem, u₂₃.mem, u₂₂.mem, u₂₁.mem,
      u₂₀.mem, u₁₉.mem, u₁₈.mem, u₁₇.mem, u₁₆.mem, u₁₅.mem, u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem,
      u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have rd31 : s₃₁.rd = s.rd := by
    rw [u₃₁.rd, u₃₀.rd, u₂₉.rd, u₂₈.rd, u₂₇.rd, u₂₆.rd, u₂₅.rd, u₂₄.rd, u₂₃.rd, u₂₂.rd, u₂₁.rd,
      u₂₀.rd, u₁₉.rd, u₁₈.rd, u₁₇.rd, u₁₆.rd, u₁₅.rd, u₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd,
      u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr31 : s₃₁.wr = s.wr := by
    rw [u₃₁.wr, u₃₀.wr, u₂₉.wr, u₂₈.wr, u₂₇.wr, u₂₆.wr, u₂₅.wr, u₂₄.wr, u₂₃.wr, u₂₂.wr, u₂₁.wr,
      u₂₀.wr, u₁₉.wr, u₁₈.wr, u₁₇.wr, u₁₆.wr, u₁₅.wr, u₁₄.wr, u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr,
      u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  -- The four words, byte-reversed.
  have b₀ : s₈.gpr .eax = byteRev32 (s.mem.readW (K.setWidth 64 + BitVec.ofNat 64 src) 32) := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, VG.Proof.CmacAes.X86.bswap_eq]
  have b₁ : s₈.gpr .ecx = byteRev32 (s.mem.readW (K.setWidth 64 + BitVec.ofNat 64 src + BitVec.ofNat 64 4) 32) := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, u₁.mem, VG.Proof.CmacAes.X86.bswap_eq]
  have b₂ : s₈.gpr .edx = byteRev32 (s.mem.readW (K.setWidth 64 + BitVec.ofNat 64 src + BitVec.ofNat 64 8) 32) := by
    rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.gpr, u₂.mem, u₁.mem, VG.Proof.CmacAes.X86.bswap_eq]
  have b₃ : s₈.gpr .esi = byteRev32 (s.mem.readW (K.setWidth 64 + BitVec.ofNat 64 src + BitVec.ofNat 64 12) 32) := by
    rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.mem, u₂.mem,
      u₁.mem, VG.Proof.CmacAes.X86.bswap_eq]
  have v : s₃₁.gpr .eax = byteRev32 (Proof.Cmac.dblW0 (s₈.gpr .eax) (s₈.gpr .ecx)) ∧
      s₃₁.gpr .ecx = byteRev32 (Proof.Cmac.dblW0 (s₈.gpr .ecx) (s₈.gpr .edx)) ∧
      s₃₁.gpr .edx = byteRev32 (Proof.Cmac.dblW0 (s₈.gpr .edx) (s₈.gpr .esi)) ∧
      s₃₁.gpr .esi = byteRev32 (Proof.Cmac.dblW3 (s₈.gpr .eax) (s₈.gpr .esi)) := by
    simp (disch := decide) only [u₃₁.gpr, u₃₁.other, u₃₀.gpr, u₃₀.other, u₂₉.gpr, u₂₉.other, u₂₈.gpr, u₂₈.other, u₂₇.gpr, u₂₇.other, u₂₆.gpr, u₂₆.other, u₂₅.gpr, u₂₅.other, u₂₄.gpr, u₂₄.other, u₂₃.gpr, u₂₃.other, u₂₂.gpr, u₂₂.other, u₂₁.gpr, u₂₁.other, u₂₀.gpr, u₂₀.other, u₁₉.gpr, u₁₉.other, u₁₈.gpr, u₁₈.other, u₁₇.gpr, u₁₇.other, u₁₆.gpr, u₁₆.other, u₁₅.gpr, u₁₅.other, u₁₄.gpr, u₁₄.other, u₁₃.gpr, u₁₃.other, u₁₂.gpr, u₁₂.other, u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other,
      VG.Proof.CmacAes.X86.bswap_eq, VG.Proof.CmacAes.X86.add_self_shl, Proof.Cmac.dblW0, Proof.Cmac.dblW3, and_self]
  obtain ⟨v₀, v₁, v₂, v₃⟩ := v
  refine wp_store (a := K.setWidth 64 + BitVec.ofNat 64 dst) (by rw [VG.Proof.CmacAes.X86.ea_at', gb]; exact addr_eq (by omega))
    (by rw [wr31]; exact VG.Proof.CmacAes.X86.in_word0 wD) fun s₃₂ v₃₂ => ?_
  refine wp_store (a := K.setWidth 64 + BitVec.ofNat 64 dst + BitVec.ofNat 64 4)
    (by rw [VG.Proof.CmacAes.X86.ea_at', v₃₂.gpr, gb]; exact VG.Proof.CmacAes.X86.addr_word 4 fd (by decide))
    (by rw [v₃₂.wr, wr31]; exact VG.Proof.CmacAes.X86.in_word wD (by decide)) fun s₃₃ v₃₃ => ?_
  refine wp_store (a := K.setWidth 64 + BitVec.ofNat 64 dst + BitVec.ofNat 64 8)
    (by rw [VG.Proof.CmacAes.X86.ea_at', v₃₃.gpr, v₃₂.gpr, gb]; exact VG.Proof.CmacAes.X86.addr_word 8 fd (by decide))
    (by rw [v₃₃.wr, v₃₂.wr, wr31]; exact VG.Proof.CmacAes.X86.in_word wD (by decide)) fun s₃₄ v₃₄ => ?_
  refine wp_store (a := K.setWidth 64 + BitVec.ofNat 64 dst + BitVec.ofNat 64 12)
    (by rw [VG.Proof.CmacAes.X86.ea_at', v₃₄.gpr, v₃₃.gpr, v₃₂.gpr, gb]; exact VG.Proof.CmacAes.X86.addr_word 12 fd (by decide))
    (by rw [v₃₄.wr, v₃₃.wr, v₃₂.wr, wr31]; exact VG.Proof.CmacAes.X86.in_word wD (by decide)) fun s₃₅ v₃₅ => k s₃₅ ?_ ?_ ?_ ?_
  · intro r ha hc hd hs hi hp
    rw [v₃₅.gpr, v₃₄.gpr, v₃₃.gpr, v₃₂.gpr, g r ha hc hd hs hi hp]
  · rw [v₃₅.mem, v₃₄.mem, v₃₃.mem, v₃₂.mem, v₃₄.gpr, v₃₃.gpr, v₃₂.gpr, m31, v₀, v₁, v₂, v₃, b₀, b₁, b₂, b₃]
    rfl
  · rw [v₃₅.rd, v₃₄.rd, v₃₃.rd, v₃₂.rd, rd31]
  · rw [v₃₅.wr, v₃₄.wr, v₃₃.wr, v₃₂.wr, wr31]

end VG.Proof.CmacAes.X86

end

/-!
# AES-CMAC on x86: `vg_cmac_aes_subkeys`

`L = CIPH_K(0)` is computed into the first block of the subkeys (a zero
counter block and a zero data block), then doubled there (`K1`) and into the
second block (`K2`). Only the subkeys, the scratch buffer and the 28 bytes
below `esp` change, so the stack arguments, which are reloaded from the stack,
and the return address are intact.
-/

namespace VG.Proof.CmacAes.X86

open VG VG.X86 VG.Impl.CmacAes.X86
open VG.Proof.Aes.X86 (Ctr32Impl)

variable (v : Ctr32Impl)
open VG.Proof.MdStream.X86 (Upd wp_mov wp_movi wp_addi)

section
variable (s₀ : State)

/-- The subkeys. -/
abbrev Kb : BitVec 32 := VG.X86.arg s₀ 2
/-- The scratch buffer. -/
abbrev Sc : BitVec 32 := VG.X86.arg s₀ 3

abbrev kR : Region := ⟨(VG.Proof.CmacAes.X86.Kb s₀).setWidth 64, 32⟩
abbrev scR : Region := ⟨(VG.Proof.CmacAes.X86.Sc s₀).setWidth 64, 2176⟩
abbrev kArgsR : Region := ⟨argAddr s₀ 0, 16⟩

/-- The regions the function writes, with the stack below it. -/
abbrev SBig : List Region := [VG.Proof.CmacAes.X86.kR s₀, VG.Proof.CmacAes.X86.scR s₀, VG.Proof.CmacAes.X86.stkR s₀]

/-- The memory after saving the registers in the scratch buffer. -/
def sSaved : Mem := Spill.saveMem s₀.mem ((VG.Proof.CmacAes.X86.Sc s₀).setWidth 64 + BitVec.ofNat 64 ·) s₀.gpr saved

/-- The memory before the call. -/
def sPreMem : Mem :=
  Proof.Cmac.zero4 (Proof.Cmac.zero4 (VG.Proof.CmacAes.X86.sSaved s₀) ((VG.Proof.CmacAes.X86.Sc s₀).setWidth 64 + BitVec.ofNat 64 2048)) ((VG.Proof.CmacAes.X86.Kb s₀).setWidth 64)

end

/-- The precondition, by name. -/
structure SPre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.CmacAes.X86.schR s₀, VG.Proof.CmacAes.X86.kArgsR s₀]
  wr : s₀.wr = [VG.Proof.CmacAes.X86.kR s₀, VG.Proof.CmacAes.X86.scR s₀]
  sch_k : (VG.Proof.CmacAes.X86.schR s₀).Disjoint (VG.Proof.CmacAes.X86.kR s₀)
  sch_scr : (VG.Proof.CmacAes.X86.schR s₀).Disjoint (VG.Proof.CmacAes.X86.scR s₀)
  k_scr : (VG.Proof.CmacAes.X86.kR s₀).Disjoint (VG.Proof.CmacAes.X86.scR s₀)
  args_k : (VG.Proof.CmacAes.X86.kArgsR s₀).Disjoint (VG.Proof.CmacAes.X86.kR s₀)
  args_scr : (VG.Proof.CmacAes.X86.kArgsR s₀).Disjoint (VG.Proof.CmacAes.X86.scR s₀)
  ret_k : (VG.Proof.CmacAes.X86.retR s₀).Disjoint (VG.Proof.CmacAes.X86.kR s₀)
  ret_scr : (VG.Proof.CmacAes.X86.retR s₀).Disjoint (VG.Proof.CmacAes.X86.scR s₀)
  b_sch : (VG.Proof.CmacAes.X86.stkR s₀).Disjoint (VG.Proof.CmacAes.X86.schR s₀)
  b_k : (VG.Proof.CmacAes.X86.stkR s₀).Disjoint (VG.Proof.CmacAes.X86.kR s₀)
  b_scr : (VG.Proof.CmacAes.X86.stkR s₀).Disjoint (VG.Proof.CmacAes.X86.scR s₀)
  sch_fit : (VG.Proof.CmacAes.X86.W s₀).toNat + 240 ≤ 2 ^ 32
  k_fit : (VG.Proof.CmacAes.X86.Kb s₀).toNat + 32 ≤ 2 ^ 32
  scr_fit : (VG.Proof.CmacAes.X86.Sc s₀).toNat + 2176 ≤ 2 ^ 32
  esp28 : 28 ≤ (VG.Proof.CmacAes.X86.E s₀).toNat
  esp_fit : (VG.Proof.CmacAes.X86.E s₀).toNat + 20 ≤ 2 ^ 32
  rounds : VG.Proof.CmacAes.X86.R s₀ = 10 ∨ VG.Proof.CmacAes.X86.R s₀ = 12 ∨ VG.Proof.CmacAes.X86.R s₀ = 14

theorem SPre.of {s₀ : State} (h : subkeysX86.pre s₀) : VG.Proof.CmacAes.X86.SPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r⟩

/-! ## Addresses and regions -/

theorem ret_stk (s₀ : State) : (VG.Proof.CmacAes.X86.retR s₀).Disjoint (VG.Proof.CmacAes.X86.stkR s₀) := by
  have := Offset.disjoint_below_above ((VG.Proof.CmacAes.X86.E s₀).setWidth 64) (m := 28) (a := 0) (l := 4) (by decide)
  rw [VG.Proof.CmacAes.X86.add0] at this
  exact this.symm

theorem sSaved_frame (s₀ : State) : Frame [VG.Proof.CmacAes.X86.scR s₀] s₀.mem (VG.Proof.CmacAes.X86.sSaved s₀) :=
  Spill.saveMem_frame List.mem_cons_self _ _ _ _ fun p hp =>
    have := VG.Proof.CmacAes.X86.saved_bound p hp; Offset.contains_base _ (by omega) (by omega)

section
variable {s₀ : State} (hp : VG.Proof.CmacAes.X86.SPre s₀)
include hp

theorem SPre.below_eq : below (VG.Proof.CmacAes.X86.E s₀) 28 = VG.Proof.CmacAes.X86.stkR s₀ := by
  simp only [below]; rw [Taint.sub_setWidth hp.esp28]

theorem SPre.argA {i : Nat} (hi : i < 4) : argAddr s₀ i = argAddr s₀ 0 + BitVec.ofNat 64 (4 * i) := by
  have : (s₀.gpr .esp).toNat + 20 ≤ 2 ^ 32 := hp.esp_fit
  simp only [argAddr]
  rw [show (s₀.gpr .esp + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 = addr (s₀.gpr .esp) (4 + 4 * i) from rfl,
    show (s₀.gpr .esp + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 = addr (s₀.gpr .esp) (4 + 4 * 0) from rfl,
    addr_eq (by omega), addr_eq (by omega), Offset.add_add]

theorem SPre.arg_sub {i : Nat} (hi : i < 4) : Region.Sub ⟨argAddr s₀ i, 4⟩ (VG.Proof.CmacAes.X86.kArgsR s₀) := by
  rw [hp.argA hi]; exact Offset.sub_base _ (by omega)

theorem SPre.arg_in {i : Nat} (hi : i < 4) : InRegions (s₀.rd ++ s₀.wr) (argAddr s₀ i) 4 := by
  refine ⟨VG.Proof.CmacAes.X86.kArgsR s₀, by simp [hp.rd], ?_⟩
  rw [hp.argA hi]; exact Offset.contains_base _ (by omega) (by omega)

theorem SPre.args_stk : (VG.Proof.CmacAes.X86.kArgsR s₀).Disjoint (VG.Proof.CmacAes.X86.stkR s₀) := by
  have : (s₀.gpr .esp).toNat + 20 ≤ 2 ^ 32 := hp.esp_fit
  have e : argAddr s₀ 0 = (VG.Proof.CmacAes.X86.E s₀).setWidth 64 + BitVec.ofNat 64 4 := addr_eq (by omega)
  show Region.Disjoint ⟨argAddr s₀ 0, 16⟩ _
  rw [e]; exact (Offset.disjoint_below_above _ (by decide)).symm

/-- The stack arguments are unchanged where only `SBig` changes. -/
theorem SPre.arg_keep {m : Mem} (hf : Frame (VG.Proof.CmacAes.X86.SBig s₀) s₀.mem m) {i : Nat} (hi : i < 4) :
    m.readW (argAddr s₀ i) 32 = VG.X86.arg s₀ i :=
  hf.readW (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.args_k.sub_left (hp.arg_sub hi)
    · exact hp.args_scr.sub_left (hp.arg_sub hi)
    · exact hp.args_stk.sub_left (hp.arg_sub hi)) (by decide)

theorem SPre.sched_bytes {m : Mem} (hf : Frame (VG.Proof.CmacAes.X86.SBig s₀) s₀.mem m) :
    Spec.Aes.bytesAt m ((VG.Proof.CmacAes.X86.W s₀).setWidth 64) (16 * (VG.Proof.CmacAes.X86.R s₀ + 1)) =
      Spec.Aes.bytesAt s₀.mem ((VG.Proof.CmacAes.X86.W s₀).setWidth 64) (16 * (VG.Proof.CmacAes.X86.R s₀ + 1)) := by
  have hR : 16 * (VG.Proof.CmacAes.X86.R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega
  refine Proof.Cmac.bytesAt_frame hf (fun r hr => ?_) (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.sch_k.sub_left (Region.sub_prefix hR)
  · exact hp.sch_scr.sub_left (Region.sub_prefix hR)
  · exact hp.b_sch.symm.sub_left (Region.sub_prefix hR)

theorem SPre.ret_keep {m : Mem} (hf : Frame (VG.Proof.CmacAes.X86.SBig s₀) s₀.mem m) :
    m.readW ((VG.Proof.CmacAes.X86.E s₀).setWidth 64) 32 = s₀.mem.readW ((VG.Proof.CmacAes.X86.E s₀).setWidth 64) 32 :=
  hf.readW (r := VG.Proof.CmacAes.X86.retR s₀) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.ret_k
    · exact hp.ret_scr
    · exact VG.Proof.CmacAes.X86.ret_stk s₀) (by decide)

theorem SPre.cA : (VG.Proof.CmacAes.X86.Sc s₀ + BitVec.ofNat 32 2048).setWidth 64 = (VG.Proof.CmacAes.X86.Sc s₀).setWidth 64 + BitVec.ofNat 64 2048 :=
  addr_eq (by have := hp.scr_fit; omega)

end

/-- The frame of the code that changes only the subkeys, the scratch buffer
but the saved registers, and the stack below `esp`. -/
theorem sbig_of {s₀ : State} {m : Mem}
    (hf : Frame [VG.Proof.CmacAes.X86.kR s₀, ⟨(VG.Proof.CmacAes.X86.Sc s₀).setWidth 64, 2064⟩, VG.Proof.CmacAes.X86.stkR s₀] (VG.Proof.CmacAes.X86.sSaved s₀) m) : Frame (VG.Proof.CmacAes.X86.SBig s₀) s₀.mem m :=
  ((VG.Proof.CmacAes.X86.sSaved_frame s₀).mono (by simp)).trans (hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨VG.Proof.CmacAes.X86.kR s₀, by simp, fun _ h => h⟩
    · exact ⟨VG.Proof.CmacAes.X86.scR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨VG.Proof.CmacAes.X86.stkR s₀, by simp, fun _ h => h⟩)

/-! ## Before the call -/

/-- What the code before the call leaves. -/
structure SAfter (s₀ s : State) : Prop where
  pre : VG.Proof.CmacAes.X86.CtrPre s (VG.Proof.CmacAes.X86.W s₀) (VG.Proof.CmacAes.X86.Sc s₀ + BitVec.ofNat 32 2048) (VG.Proof.CmacAes.X86.Kb s₀) (VG.Proof.CmacAes.X86.Sc s₀) (VG.Proof.CmacAes.X86.R s₀)
  esp : s.gpr .esp = VG.Proof.CmacAes.X86.E s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = VG.Proof.CmacAes.X86.sPreMem s₀

theorem subkeysPre_eq : subkeysPre = .mov .eax (argOp 3) :: (saved.map (fun p => Instr.store (at_ .eax p.2) p.1) ++
    (.mov .ebp (.reg .eax) :: .mov .ebx (argOp 2) :: (zero4 .ebp 2048 ++ (zero4 .ebx 0 ++ ctrArgs)))) := rfl

theorem sPreMem_frame (s₀ : State) :
    Frame [VG.Proof.CmacAes.X86.kR s₀, ⟨(VG.Proof.CmacAes.X86.Sc s₀).setWidth 64, 2064⟩, VG.Proof.CmacAes.X86.stkR s₀] (VG.Proof.CmacAes.X86.sSaved s₀) (VG.Proof.CmacAes.X86.sPreMem s₀) :=
  ((Proof.Cmac.frame_store4 _ _ _ _ _).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨(VG.Proof.CmacAes.X86.Sc s₀).setWidth 64, 2064⟩, by simp, Offset.sub_base _ (by decide)⟩).trans
  ((Proof.Cmac.frame_store4 _ _ _ _ _).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨VG.Proof.CmacAes.X86.kR s₀, by simp, Region.sub_prefix (by decide)⟩)

theorem spre_wp {s₀ : State} (hp : VG.Proof.CmacAes.X86.SPre s₀) : WP isa (.block subkeysPre) s₀ (VG.Proof.CmacAes.X86.SAfter s₀) := by
  have hsc := hp.scr_fit
  have hk := hp.k_fit
  have cA := hp.cA
  rw [VG.Proof.CmacAes.X86.subkeysPre_eq]
  refine VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀) rfl (hp.arg_in (by decide)) rfl fun s₁ u₁ => ?_
  have h₁ : s₁.gpr .eax = VG.Proof.CmacAes.X86.Sc s₀ := u₁.gpr
  refine Spill.save_ofNat_ok saved VG.Proof.CmacAes.X86.saved_fits (by rw [h₁]; omega) (fun p hp' => ?_) fun s₂ u₂ => ?_
  · have hb := VG.Proof.CmacAes.X86.saved_bound p hp'
    rw [h₁, u₁.wr, hp.wr]
    exact ⟨VG.Proof.CmacAes.X86.scR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hm₂ : s₂.mem = VG.Proof.CmacAes.X86.sSaved s₀ := by
    rw [u₂.mem, u₁.mem, h₁, VG.Proof.CmacAes.X86.sSaved]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p hp' => u₁.other _ (VG.Proof.CmacAes.X86.saved_ne_eax p hp')
  have esp₂ : s₂.gpr .esp = VG.Proof.CmacAes.X86.E s₀ := by rw [u₂.gpr, u₁.other _ (by decide)]
  have rw₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]
  have big₂ : Frame (VG.Proof.CmacAes.X86.SBig s₀) s₀.mem s₂.mem := by rw [hm₂]; exact (VG.Proof.CmacAes.X86.sSaved_frame s₀).mono (by simp)
  refine wp_mov fun s₃ u₃ => ?_
  refine VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀) (by rw [u₃.other _ (by decide), esp₂])
    (by rw [u₃.rd, u₃.wr, rw₂]; exact hp.arg_in (by decide))
    (by rw [u₃.mem]; exact hp.arg_keep big₂ (by decide)) fun s₄ u₄ => ?_
  have p₄ : s₄.gpr .ebp = VG.Proof.CmacAes.X86.Sc s₀ := by rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr, h₁]
  have b₄ : s₄.gpr .ebx = VG.Proof.CmacAes.X86.Kb s₀ := u₄.gpr
  have w₄ : s₄.wr = s₀.wr := by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  refine VG.Proof.CmacAes.X86.zero4_ok (b := .ebp) (d := 2048) (by decide) (by rw [p₄]; omega) ?_ fun s₅ g₅ m₅ rd₅ wr₅ => ?_
  · rw [p₄, w₄, hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.CmacAes.X86.scR s₀, by simp, 2048, rfl, by simp⟩
  have b₅ : s₅.gpr .ebx = VG.Proof.CmacAes.X86.Kb s₀ := by rw [g₅ _ (by decide), b₄]
  refine VG.Proof.CmacAes.X86.zero4_ok (b := .ebx) (d := 0) (by decide) (by rw [b₅]; omega) ?_ fun s₆ g₆ m₆ rd₆ wr₆ => ?_
  · rw [b₅, VG.Proof.CmacAes.X86.add0, wr₅, w₄, hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.CmacAes.X86.kR s₀, by simp, 0, by simp, by simp⟩
  have esp₆ : s₆.gpr .esp = VG.Proof.CmacAes.X86.E s₀ := by
    rw [g₆ _ (by decide), g₅ _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), esp₂]
  have mem₆ : s₆.mem = VG.Proof.CmacAes.X86.sPreMem s₀ := by
    rw [m₆, b₅, VG.Proof.CmacAes.X86.add0, m₅, p₄, u₄.mem, u₃.mem, hm₂]; rfl
  have big₆ : Frame (VG.Proof.CmacAes.X86.SBig s₀) s₀.mem s₆.mem := by rw [mem₆]; exact VG.Proof.CmacAes.X86.sbig_of (VG.Proof.CmacAes.X86.sPreMem_frame s₀)
  have rw₆ : s₆.rd ++ s₆.wr = s₀.rd ++ s₀.wr := by rw [rd₆, wr₆, rd₅, wr₅, u₄.rd, u₄.wr, u₃.rd, u₃.wr, rw₂]
  rw [VG.Proof.CmacAes.X86.ctrArgs_eq]
  refine VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀) esp₆ (by rw [rw₆]; exact hp.arg_in (by decide)) (hp.arg_keep big₆ (by decide))
    fun s₇ u₇ => ?_
  refine VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀) (by rw [u₇.other _ (by decide), esp₆])
    (by rw [u₇.rd, u₇.wr, rw₆]; exact hp.arg_in (by decide))
    (by rw [u₇.mem]; exact hp.arg_keep big₆ (by decide)) fun s₈ u₈ => ?_
  refine wp_mov fun s₉ u₉ => wp_addi fun s₁₀ u₁₀ => wp_movi fun s₁₁ u₁₁ => WP.block_nil ?_
  have keep : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → s₁₁.gpr r = s₆.gpr r := fun r ha hc hd hi => by
    rw [u₁₁.other _ hi, u₁₀.other _ hd, u₉.other _ hd, u₈.other _ hc, u₇.other _ ha]
  have p₆ : s₆.gpr .ebp = VG.Proof.CmacAes.X86.Sc s₀ := by rw [g₆ _ (by decide), g₅ _ (by decide), p₄]
  have b₆ : s₆.gpr .ebx = VG.Proof.CmacAes.X86.Kb s₀ := by rw [g₆ _ (by decide), b₅]
  have sp₁₁ : s₁₁.gpr .esp = VG.Proof.CmacAes.X86.E s₀ := by rw [keep _ (by decide) (by decide) (by decide) (by decide), esp₆]
  have rd₁₁ : s₁₁.rd = s₀.rd := by rw [u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, rd₆, rd₅, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₁₁ : s₁₁.wr = s₀.wr := by rw [u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, wr₆, wr₅, w₄]
  have mem₁₁ : s₁₁.mem = VG.Proof.CmacAes.X86.sPreMem s₀ := by rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, mem₆]
  have hb : below (s₁₁.gpr .esp) 28 = VG.Proof.CmacAes.X86.stkR s₀ := by rw [sp₁₁]; exact hp.below_eq
  refine ⟨⟨?_, ?_, ?_, ?_, u₁₁.gpr, ?_, hp.rounds, by rw [sp₁₁]; exact hp.esp28, ?_,
    hp.sch_k.sub_right (Region.sub_prefix (by decide)), hp.sch_scr.sub_right (Region.sub_prefix (by decide)),
    ?_, ?_, (hp.k_scr.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide)),
    by rw [hb]; exact hp.b_sch, ?_, by rw [hb]; exact hp.b_k.sub_right (Region.sub_prefix (by decide)),
    by rw [hb]; exact hp.b_scr.sub_right (Region.sub_prefix (by decide)), hp.sch_fit, ?_, by omega, by omega,
    ?_, ?_, ?_⟩, sp₁₁, rd₁₁, wr₁₁, mem₁₁⟩
  · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr]
  · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr]; exact VG.Proof.CmacAes.X86.arg_ofNat s₀ 1
  · rw [u₁₁.other _ (by decide), u₁₀.gpr, u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), p₆]
  · rw [keep _ (by decide) (by decide) (by decide) (by decide), b₆]
  · rw [keep _ (by decide) (by decide) (by decide) (by decide), p₆]
  · rw [cA]; exact hp.sch_scr.sub_right (Offset.sub_base _ (by decide))
  · rw [cA]
    exact (hp.k_scr.symm.sub_left (Offset.sub_base _ (by decide))).sub_right (Region.sub_prefix (by decide))
  · rw [cA]; exact Offset.disjoint_base _ (by decide) (by omega)
  · rw [hb, cA]; exact hp.b_scr.sub_right (Offset.sub_base _ (by decide))
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 2048) (by decide),
      Nat.mod_eq_of_lt (by omega)]; omega
  · rw [rd₁₁, wr₁₁, hp.rd]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.CmacAes.X86.schR s₀, by simp, 0, by simp, by simp⟩
  · rw [wr₁₁, hp.wr, cA]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨VG.Proof.CmacAes.X86.scR s₀, by simp, 2048, rfl, by simp⟩
    · exact ⟨VG.Proof.CmacAes.X86.kR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨VG.Proof.CmacAes.X86.scR s₀, by simp, 0, by simp, by simp⟩
  · rw [mem₁₁, VG.Proof.CmacAes.X86.sPreMem]; exact Proof.Cmac.zero4_bytes _ _

/-! ## The call, the doubling and the restore -/

theorem subkeysPost_eq : subkeysPost = dbl 0 0 ++ (dbl 0 16 ++ (.mov .eax (argOp 3) ::
    (saved.map fun p => Instr.mov p.1 (.mem (at_ .eax p.2))) ++ [])) := rfl

theorem subkeys_wp {s₀ : State} (h0 : subkeysX86.pre s₀) :
    WP isa (subkeys v.callee) s₀ fun s' => abiPreserved s₀ s' ∧ subkeysX86.post s₀ s' := by
  have hp := SPre.of h0
  have hk := hp.k_fit
  have hsc := hp.scr_fit
  have hR := hp.rounds
  have hRb : 16 * (VG.Proof.CmacAes.X86.R s₀ + 1) ≤ 240 := by rcases hR with h | h | h <;> omega
  have cA := hp.cA
  have cK : ∀ d n, d + n ≤ 32 → Covers [⟨(VG.Proof.CmacAes.X86.Kb s₀).setWidth 64 + BitVec.ofNat 64 d, n⟩] s₀.wr := fun d n h => by
    rw [hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.CmacAes.X86.kR s₀, by simp, d, rfl, h⟩
  have cKr : ∀ d n, d + n ≤ 32 → Covers [⟨(VG.Proof.CmacAes.X86.Kb s₀).setWidth 64 + BitVec.ofNat 64 d, n⟩] (s₀.rd ++ s₀.wr) :=
    fun d n h a k hi => by
      obtain ⟨r, hr, hc⟩ := cK d n h a k hi; exact ⟨r, List.mem_append_right _ hr, hc⟩
  unfold subkeys
  refine WP.seq (WP.mono (VG.Proof.CmacAes.X86.spre_wp hp) fun s₁ a => ?_)
  refine WP.seq (WP.mono (VG.Proof.CmacAes.X86.ctr_call v a.pre) fun s₂ h₂ => ?_)
  have hb : below (s₁.gpr .esp) 28 = VG.Proof.CmacAes.X86.stkR s₀ := by rw [a.esp]; exact hp.below_eq
  -- The memory after the call.
  have f₂ : Frame [VG.Proof.CmacAes.X86.kR s₀, ⟨(VG.Proof.CmacAes.X86.Sc s₀).setWidth 64, 2064⟩, VG.Proof.CmacAes.X86.stkR s₀] (VG.Proof.CmacAes.X86.sPreMem s₀) s₂.mem := by
    have fr := h₂.frame
    rw [hb, cA, a.mem] at fr
    exact fr.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨(VG.Proof.CmacAes.X86.Sc s₀).setWidth 64, 2064⟩, by simp, Offset.sub_base _ (by decide)⟩
      · exact ⟨VG.Proof.CmacAes.X86.kR s₀, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨⟨(VG.Proof.CmacAes.X86.Sc s₀).setWidth 64, 2064⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨VG.Proof.CmacAes.X86.stkR s₀, by simp, fun _ h => h⟩
  have fr₂ := (VG.Proof.CmacAes.X86.sPreMem_frame s₀).trans f₂
  have kC : (⟨(VG.Proof.CmacAes.X86.Kb s₀).setWidth 64, 16⟩ : Region).Disjoint ⟨(VG.Proof.CmacAes.X86.Sc s₀).setWidth 64 + BitVec.ofNat 64 2048, 16⟩ :=
    (hp.k_scr.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base _ (by decide))
  have zC : Spec.Aes.bytesAt (VG.Proof.CmacAes.X86.sPreMem s₀) ((VG.Proof.CmacAes.X86.Sc s₀).setWidth 64 + BitVec.ofNat 64 2048) 16 = Spec.Cmac.zeros 16 := by
    rw [VG.Proof.CmacAes.X86.sPreMem, Proof.Cmac.zero4, Proof.Cmac.bytesAt_frame16 (Proof.Cmac.frame_store4 _ _ _ _ _) (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact kC.symm)]
    exact Proof.Cmac.zero4_bytes _ _
  have L : Spec.Aes.bytesAt s₂.mem ((VG.Proof.CmacAes.X86.Kb s₀).setWidth 64) 16 = VG.Proof.CmacAes.X86.ciph s₀ (Spec.Cmac.zeros 16) := by
    have out := h₂.out
    rw [hp.sched_bytes (by rw [a.mem]; exact VG.Proof.CmacAes.X86.sbig_of (VG.Proof.CmacAes.X86.sPreMem_frame s₀)), cA, a.mem, zC] at out
    exact out
  have b₂ : s₂.gpr .ebx = VG.Proof.CmacAes.X86.Kb s₀ := by rw [h₂.saved .ebx (by simp [calleeSaved]), a.pre.ebx]
  have rdwr₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [h₂.rd, h₂.wr, a.rd, a.wr]
  have wr₂ : s₂.wr = s₀.wr := by rw [h₂.wr, a.wr]
  -- The doubling.
  rw [VG.Proof.CmacAes.X86.subkeysPost_eq]
  refine VG.Proof.CmacAes.X86.dbl_wp b₂ (by omega) (by omega) (by rw [rdwr₂]; exact cKr 0 16 (by decide))
    (by rw [wr₂]; exact cK 0 16 (by decide)) fun s₃ g₃ m₃ rd₃ wr₃ => ?_
  have b₃ : s₃.gpr .ebx = VG.Proof.CmacAes.X86.Kb s₀ := by
    rw [g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), b₂]
  refine VG.Proof.CmacAes.X86.dbl_wp b₃ (by omega) (by omega) (by rw [rd₃, wr₃, rdwr₂]; exact cKr 0 16 (by decide))
    (by rw [wr₃, wr₂]; exact cK 16 16 (by decide)) fun s₄ g₄ m₄ rd₄ wr₄ => ?_
  have f₄ : Frame [VG.Proof.CmacAes.X86.kR s₀, ⟨(VG.Proof.CmacAes.X86.Sc s₀).setWidth 64, 2064⟩, VG.Proof.CmacAes.X86.stkR s₀] (VG.Proof.CmacAes.X86.sSaved s₀) s₄.mem := by
    refine fr₂.trans (((VG.Proof.CmacAes.X86.dblMem_frame _ _ _ _).sub fun r hr => ?_).trans ((VG.Proof.CmacAes.X86.dblMem_frame _ _ _ _).sub fun r hr => ?_))
      |> fun h => by rw [m₄, m₃]; exact h
    all_goals simp only [List.mem_singleton] at hr; subst hr
    · exact ⟨VG.Proof.CmacAes.X86.kR s₀, by simp, Offset.sub_base _ (by decide)⟩
    · exact ⟨VG.Proof.CmacAes.X86.kR s₀, by simp, Offset.sub_base _ (by decide)⟩
  have big₄ := VG.Proof.CmacAes.X86.sbig_of f₄
  have esp₄ : s₄.gpr .esp = VG.Proof.CmacAes.X86.E s₀ := by
    rw [g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      h₂.saved .esp (by simp [calleeSaved]), a.esp]
  have rdwr₄ : s₄.rd ++ s₄.wr = s₀.rd ++ s₀.wr := by rw [rd₄, wr₄, rd₃, wr₃, rdwr₂]
  -- The restore.
  refine VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀) esp₄ (by rw [rdwr₄]; exact hp.arg_in (by decide)) (hp.arg_keep big₄ (by decide))
    fun s₅ u₅ => ?_
  have sl : ∀ r d, (r, d) ∈ saved → s₄.mem.readW ((VG.Proof.CmacAes.X86.Sc s₀).setWidth 64 + BitVec.ofNat 64 d) 32 = s₀.gpr r := by
    intro r d hrd
    have hb := VG.Proof.CmacAes.X86.saved_bound _ hrd
    rw [f₄.readW (r := ⟨(VG.Proof.CmacAes.X86.Sc s₀).setWidth 64 + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.k_scr.symm.sub_left (Offset.sub_base _ (by omega))
      · exact Offset.disjoint_base _ hb.1 (by omega)
      · exact hp.b_scr.symm.sub_left (Offset.sub_base _ (by omega))) (by decide)]
    exact VG.Proof.CmacAes.X86.saveMem_slot _ _ _ hrd
  have hsc' : (VG.X86.arg s₀ 3).toNat + 2176 ≤ 2 ^ 32 := hsc
  refine Spill.restore_ofNat_ok saved VG.Proof.CmacAes.X86.saved_fits (by rw [u₅.gpr]; omega) VG.Proof.CmacAes.X86.saved_ne_eax (fun p hp' => ?_)
    (fun p hp' => by rw [u₅.gpr, u₅.mem]; exact sl p.1 p.2 hp') fun s₆ r₆ => WP.block_nil ?_
  · have hb := VG.Proof.CmacAes.X86.saved_bound p hp'
    rw [u₅.gpr, u₅.rd, u₅.wr, rdwr₄, hp.rd, hp.wr]
    exact ⟨VG.Proof.CmacAes.X86.scR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  refine ⟨⟨r₆.abi (by decide) (by decide) (by rw [u₅.other _ (by decide), esp₄]), ?_⟩, ?_⟩
  · rw [r₆.mem, u₅.mem]; exact hp.ret_keep big₄
  · show Spec.Aes.bytesAt s₆.mem ((VG.Proof.CmacAes.X86.Kb s₀).setWidth 64) 32 = _
    have b₃' : Spec.Aes.bytesAt s₃.mem ((VG.Proof.CmacAes.X86.Kb s₀).setWidth 64) 16 =
        Spec.Cmac.dbl 16 (Spec.Aes.bytesAt s₂.mem ((VG.Proof.CmacAes.X86.Kb s₀).setWidth 64) 16) := by
      have := VG.Proof.CmacAes.X86.dblMem_bytes s₂.mem ((VG.Proof.CmacAes.X86.Kb s₀).setWidth 64) 0 0
      rw [VG.Proof.CmacAes.X86.add0] at this; rw [m₃, this]
    have lo : Spec.Aes.bytesAt s₄.mem ((VG.Proof.CmacAes.X86.Kb s₀).setWidth 64) 16 = Spec.Aes.bytesAt s₃.mem ((VG.Proof.CmacAes.X86.Kb s₀).setWidth 64) 16 := by
      rw [m₄]
      exact Proof.Cmac.bytesAt_frame16 (VG.Proof.CmacAes.X86.dblMem_frame _ _ _ _) fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (Offset.disjoint_base _ (by decide) (by omega)).symm
    have hi : Spec.Aes.bytesAt s₄.mem ((VG.Proof.CmacAes.X86.Kb s₀).setWidth 64 + BitVec.ofNat 64 16) 16 =
        Spec.Cmac.dbl 16 (Spec.Aes.bytesAt s₃.mem ((VG.Proof.CmacAes.X86.Kb s₀).setWidth 64) 16) := by
      have := VG.Proof.CmacAes.X86.dblMem_bytes s₃.mem ((VG.Proof.CmacAes.X86.Kb s₀).setWidth 64) 0 16
      rw [VG.Proof.CmacAes.X86.add0] at this; rw [m₄, this]
    rw [r₆.mem, u₅.mem, Proof.Cmac.bytesAt_32, lo, hi, b₃', L]
    rfl

end VG.Proof.CmacAes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.X86.Verified`. -/
section

section

/-!
# AES-CMAC on x86: `vg_cmac_aes_subkeys` is constant time

The code before the call is checked by the taint analysis from `esp` and the
stack arguments (which nothing writes, `argTaint`), the call of
`vg_aes_ctr32`, in its frame, is constant time by its own proof (`ctr_rel`),
and the code after it by the taint analysis again, from `esp`, the stack
arguments and `ebx` (the subkeys, which the correctness proof pins).
-/

namespace VG.Proof.CmacAes.X86

open VG VG.X86 VG.Impl.CmacAes.X86
open VG.Proof.Aes.X86 (Ctr32Impl)

variable (v : Ctr32Impl)

theorem SPre.argsOut {s₀ : State} (hp : VG.Proof.CmacAes.X86.SPre s₀) {s : State} (hesp : s.gpr .esp = VG.Proof.CmacAes.X86.E s₀) (hwr : s.wr = s₀.wr) :
    ArgsOut 4 s := by
  have hs : (s₀.gpr .esp).toNat + 20 ≤ 2 ^ 32 := hp.esp_fit
  refine ⟨by rw [hesp]; omega, ?_⟩
  rw [hwr, hp.wr, hesp]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) hp.ret_k hp.args_k
  · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) hp.ret_scr hp.args_scr

/-- What two runs agree on at a point between the calls. -/
structure SPt (s₀ : State) (s : State) : Prop where
  esp : s.gpr .esp = VG.Proof.CmacAes.X86.E s₀
  wr : s.wr = s₀.wr
  args : ∀ i < 4, s.mem.readW (argAddr s₀ i) 32 = VG.X86.arg s₀ i

section
variable {s₀ s₀' : State} (hq : subkeysX86.pub s₀ s₀')
include hq

theorem spub_arg {i : Nat} (hi : i < 4) : VG.X86.arg s₀ i = VG.X86.arg s₀' i := hq.2 i hi

/-- Two runs agree on `esp`, the stack arguments and the registers `rs`. -/
theorem SPt.agree (hp : VG.Proof.CmacAes.X86.SPre s₀) (hp' : VG.Proof.CmacAes.X86.SPre s₀') {rs : List Reg} {s₁ s₂ : State} (h₁ : VG.Proof.CmacAes.X86.SPt s₀ s₁)
    (h₂ : VG.Proof.CmacAes.X86.SPt s₀' s₂) (hr : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) :
    VG.X86.Taint.Agree (argTaint rs (4 + 4 * 4)) s₁ s₂ :=
  agree_argTaint hr (by rw [h₁.esp, h₂.esp]; exact hq.1) (hp.argsOut h₁.esp h₁.wr) (hp'.argsOut h₂.esp h₂.wr)
    fun i hi => by rw [VG.Proof.CmacAes.X86.arg_cur (h₁.esp) (h₁.args i hi), VG.Proof.CmacAes.X86.arg_cur (h₂.esp) (h₂.args i hi), VG.Proof.CmacAes.X86.spub_arg hq hi]

end

theorem SAfter.pt {s₀ : State} (hp : VG.Proof.CmacAes.X86.SPre s₀) {s : State} (h : VG.Proof.CmacAes.X86.SAfter s₀ s) : VG.Proof.CmacAes.X86.SPt s₀ s :=
  ⟨h.esp, h.wr, fun _ hi => hp.arg_keep (by rw [h.mem]; exact VG.Proof.CmacAes.X86.sbig_of (VG.Proof.CmacAes.X86.sPreMem_frame s₀)) hi⟩

/-- What is known after the call. -/
structure SPost (s₀ : State) (s : State) : Prop where
  ebx : s.gpr .ebx = VG.Proof.CmacAes.X86.Kb s₀
  pt : VG.Proof.CmacAes.X86.SPt s₀ s

theorem spost_wp {s₀ : State} (hp : VG.Proof.CmacAes.X86.SPre s₀) {s : State} (h : VG.Proof.CmacAes.X86.SAfter s₀ s) : WP isa (ctrCall v.callee) s (VG.Proof.CmacAes.X86.SPost s₀) :=
  WP.mono (VG.Proof.CmacAes.X86.ctr_call v h.pre) fun s' hc => by
    have hb : below (s.gpr .esp) 28 = VG.Proof.CmacAes.X86.stkR s₀ := by rw [h.esp]; exact hp.below_eq
    have fr := hc.frame
    rw [hb, hp.cA, h.mem] at fr
    have big : Frame (VG.Proof.CmacAes.X86.SBig s₀) s₀.mem s'.mem := (VG.Proof.CmacAes.X86.sbig_of (VG.Proof.CmacAes.X86.sPreMem_frame s₀)).trans (fr.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨VG.Proof.CmacAes.X86.scR s₀, by simp, Offset.sub_base _ (by decide)⟩
      · exact ⟨VG.Proof.CmacAes.X86.kR s₀, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨VG.Proof.CmacAes.X86.scR s₀, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨VG.Proof.CmacAes.X86.stkR s₀, by simp, fun _ h => h⟩)
    exact ⟨by rw [hc.saved .ebx (by simp [calleeSaved]), h.pre.ebx],
      ⟨by rw [hc.saved .esp (by simp [calleeSaved]), h.esp], by rw [hc.wr, h.wr], fun _ hi => hp.arg_keep big hi⟩⟩

theorem subkeys_rel {s₀ s₀' : State} (h0 : subkeysX86.pre s₀) (h0' : subkeysX86.pre s₀')
    (hq : subkeysX86.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (subkeys v.callee) fun _ _ => True := by
  have hp := SPre.of h0
  have hp' := SPre.of h0'
  have eW : VG.Proof.CmacAes.X86.W s₀ = VG.Proof.CmacAes.X86.W s₀' := VG.Proof.CmacAes.X86.spub_arg hq (by decide)
  have eR : VG.Proof.CmacAes.X86.R s₀ = VG.Proof.CmacAes.X86.R s₀' := by rw [VG.Proof.CmacAes.X86.R, VG.Proof.CmacAes.X86.R, VG.Proof.CmacAes.X86.spub_arg hq (by decide)]
  have eK : VG.Proof.CmacAes.X86.Kb s₀ = VG.Proof.CmacAes.X86.Kb s₀' := VG.Proof.CmacAes.X86.spub_arg hq (by decide)
  have eS : VG.Proof.CmacAes.X86.Sc s₀ = VG.Proof.CmacAes.X86.Sc s₀' := VG.Proof.CmacAes.X86.spub_arg hq (by decide)
  have pt₀ : ∀ {t : State}, VG.Proof.CmacAes.X86.SPt t t := ⟨rfl, rfl, fun _ _ => rfl⟩
  have a := ((RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') (argTaint [] (4 + 4 * 4))
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      exact SPt.agree hq hp hp' pt₀ pt₀ fun r hr => by simp at hr)
    (c := .block subkeysPre) (by taint_decide)).wp (F₁ := VG.Proof.CmacAes.X86.SAfter s₀) (F₂ := VG.Proof.CmacAes.X86.SAfter s₀')
    fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨VG.Proof.CmacAes.X86.spre_wp hp, VG.Proof.CmacAes.X86.spre_wp hp'⟩).mono (fun _ _ h => h)
    fun _ _ h => h.2
  have c := ((VG.Proof.CmacAes.X86.ctr_rel v (E := VG.Proof.CmacAes.X86.E s₀) (P := fun s₁ s₂ => VG.Proof.CmacAes.X86.SAfter s₀ s₁ ∧ VG.Proof.CmacAes.X86.SAfter s₀' s₂) fun s₁ s₂ h =>
      ⟨h.1.pre, by rw [eW, eS, eK, eR]; exact h.2.pre, h.1.esp, h.2.esp.trans hq.1.symm⟩).wp
      (F₁ := VG.Proof.CmacAes.X86.SPost s₀) (F₂ := VG.Proof.CmacAes.X86.SPost s₀') fun _ _ h => ⟨VG.Proof.CmacAes.X86.spost_wp v hp h.1, VG.Proof.CmacAes.X86.spost_wp v hp' h.2⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  have b := RelCT.taint (A := taint) (P := fun s₁ s₂ => VG.Proof.CmacAes.X86.SPost s₀ s₁ ∧ VG.Proof.CmacAes.X86.SPost s₀' s₂) (argTaint [.ebx] (4 + 4 * 4))
    (fun _ _ h => SPt.agree hq hp hp' h.1.pt h.2.pt fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.ebx, h.2.ebx, eK])
    (c := .block subkeysPost) (by taint_decide)
  exact a.seq (c.seq b)

theorem subkeys_ct : ConstantTime isa subkeysX86.pre subkeysX86.pub (subkeys v.callee) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (VG.Proof.CmacAes.X86.subkeys_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.X86

end

/-!
# AES-CMAC on x86: `Verified`

Correctness and constant time, a state satisfying each precondition, and the
shared contracts of `Spec/Cmac/Contract.lean`, with 28 bytes of stack: each
call of `vg_aes_ctr32` pushes its six arguments and the return address.
-/

namespace VG.Proof.CmacAes.X86

open VG VG.X86 VG.Impl.CmacAes.X86
open VG.Proof.Aes.X86 (Ctr32Impl)

variable (v : Ctr32Impl)

theorem callee_nosp_all : v.callee.code.allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  rw [Code.allInstrs_eq]
  exact List.all_eq_true.mpr fun i hi => by
    have h := v.nosp i hi
    simp only [h, Bool.not_false]

theorem subkeys_nosp : NoSp (subkeys v.callee) := by
  apply NoSp.of_all
  simp only [subkeys, ctrCall, Code.allInstrs, VG.Proof.CmacAes.X86.callee_nosp_all v]
  decide +kernel

theorem subkeys_stack : stackUse (subkeys v.callee) = 28 := by
  simp only [subkeys, ctrCall, stackUse, v.stack]
  decide +kernel

theorem subkeys_spSafe : (subkeys v.callee).all (fun i => !isa.writesSp i) = true := by
  simp only [subkeys, ctrCall, Code.all, v.spSafe]
  decide +kernel

theorem update_nosp : NoSp (update v.callee) := by
  apply NoSp.of_all
  simp only [update, body, ctrCall, Code.allInstrs, VG.Proof.CmacAes.X86.callee_nosp_all v]
  decide +kernel

theorem update_stack : stackUse (update v.callee) = 28 := by
  simp only [update, body, ctrCall, stackUse, v.stack]
  decide +kernel

theorem update_spSafe : (update v.callee).all (fun i => !isa.writesSp i) = true := by
  simp only [update, body, ctrCall, Code.all, v.spSafe]
  decide +kernel

theorem finalize_nosp : NoSp (finalize v.callee) := by
  apply NoSp.of_all
  simp only [finalize, finPre, partialBlock, copy, ctrCall, Code.allInstrs, VG.Proof.CmacAes.X86.callee_nosp_all v]
  decide +kernel

theorem finalize_stack : stackUse (finalize v.callee) = 28 := by
  simp only [finalize, finPre, partialBlock, copy, ctrCall, stackUse, v.stack]
  decide +kernel

theorem finalize_spSafe : (finalize v.callee).all (fun i => !isa.writesSp i) = true := by
  simp only [finalize, finPre, partialBlock, copy, ctrCall, Code.all, v.spSafe]
  decide +kernel

/-- A state satisfying `vg_cmac_aes_subkeys`'s precondition: the schedule
at `0x1000`, 10 rounds, the subkeys at `0x2000` and the scratch buffer at
`0x4000`, as stack arguments at `0x8004`. -/
def subSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 10
    else if a = 0x800d then 0x20 else if a = 0x8011 then 0x40 else 0
  rd := [⟨0x1000, 240⟩, ⟨0x8004, 16⟩]
  wr := [⟨0x2000, 32⟩, ⟨0x4000, 2176⟩]

theorem subkeys_verified : Verified X86.target (subkeys v.callee) (Spec.Cmac.aesSubkeysContract X86.abi 28) :=
  Verified.of_correct (fun _ hs => VG.Proof.CmacAes.X86.subkeys_wp v hs) (VG.Proof.CmacAes.X86.subkeys_ct v) (by
    have a0 : VG.X86.arg VG.Proof.CmacAes.X86.subSat 0 = 0x1000 := by decide
    have a1 : VG.X86.arg VG.Proof.CmacAes.X86.subSat 1 = 10 := by decide
    have a2 : VG.X86.arg VG.Proof.CmacAes.X86.subSat 2 = 0x2000 := by decide
    have a3 : VG.X86.arg VG.Proof.CmacAes.X86.subSat 3 = 0x4000 := by decide
    have e : argAddr VG.Proof.CmacAes.X86.subSat 0 = 0x8004 := by decide
    have esp : subSat.gpr .esp = 0x8000 := rfl
    sig_implies [Spec.Cmac.aesSubkeysContract, Spec.Cmac.aesSubkeysSig, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes, VG.Proof.CmacAes.X86.subkeysX86] [a0, a1, a2, a3, e, esp] using VG.Proof.CmacAes.X86.subSat)

/-- A state satisfying `vg_cmac_aes_finalize`'s precondition: the key at
`0x1000`, 10 rounds, the state at `0x2000`, no last bytes at `0x3000` and
the scratch buffer at `0x4000`, as stack arguments at `0x8004`. -/
def finSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 10
    else if a = 0x800d then 0x20 else if a = 0x8011 then 0x30 else if a = 0x8019 then 0x40 else 0
  rd := [⟨0x1000, 272⟩, ⟨0x3000, 0⟩, ⟨0x8004, 24⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x4000, 2176⟩]

theorem finalize_verified : Verified X86.target (finalize v.callee) (Spec.Cmac.aesFinalizeContract X86.abi 28) :=
  Verified.of_correct (fun _ hs => VG.Proof.CmacAes.X86.finalize_wp v hs) (VG.Proof.CmacAes.X86.finalize_ct v) (by
    have a0 : VG.X86.arg VG.Proof.CmacAes.X86.finSat 0 = 0x1000 := by decide
    have a1 : VG.X86.arg VG.Proof.CmacAes.X86.finSat 1 = 10 := by decide
    have a2 : VG.X86.arg VG.Proof.CmacAes.X86.finSat 2 = 0x2000 := by decide
    have a3 : VG.X86.arg VG.Proof.CmacAes.X86.finSat 3 = 0x3000 := by decide
    have a4 : VG.X86.arg VG.Proof.CmacAes.X86.finSat 4 = 0 := by decide
    have a5 : VG.X86.arg VG.Proof.CmacAes.X86.finSat 5 = 0x4000 := by decide
    have e : argAddr VG.Proof.CmacAes.X86.finSat 0 = 0x8004 := by decide
    have esp : finSat.gpr .esp = 0x8000 := rfl
    sig_implies [Spec.Cmac.aesFinalizeContract, Spec.Cmac.aesFinalizeSig, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes, VG.Proof.CmacAes.X86.finalizeX86] [a0, a1, a2, a3, a4, a5, e, esp] using VG.Proof.CmacAes.X86.finSat)

/-- A state satisfying `vg_cmac_aes_update`'s precondition: as `finSat`,
with no blocks. -/
def updSat : State := { VG.Proof.CmacAes.X86.finSat with
                                    rd := [⟨0x1000, 240⟩, ⟨0x3000, 0⟩, ⟨0x8004, 24⟩] }

theorem update_verified : Verified X86.target (update v.callee) (Spec.Cmac.aesUpdateContract X86.abi 28) :=
  Verified.of_correct (fun _ hs => VG.Proof.CmacAes.X86.update_wp v hs) (VG.Proof.CmacAes.X86.update_ct v) (by
    have a0 : VG.X86.arg VG.Proof.CmacAes.X86.updSat 0 = 0x1000 := by decide
    have a1 : VG.X86.arg VG.Proof.CmacAes.X86.updSat 1 = 10 := by decide
    have a2 : VG.X86.arg VG.Proof.CmacAes.X86.updSat 2 = 0x2000 := by decide
    have a3 : VG.X86.arg VG.Proof.CmacAes.X86.updSat 3 = 0x3000 := by decide
    have a4 : VG.X86.arg VG.Proof.CmacAes.X86.updSat 4 = 0 := by decide
    have a5 : VG.X86.arg VG.Proof.CmacAes.X86.updSat 5 = 0x4000 := by decide
    have e : argAddr VG.Proof.CmacAes.X86.updSat 0 = 0x8004 := by decide
    have esp : updSat.gpr .esp = 0x8000 := rfl
    sig_implies [Spec.Cmac.aesUpdateContract, Spec.Cmac.aesUpdateSig, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes, VG.Proof.CmacAes.X86.updateX86] [a0, a1, a2, a3, a4, a5, e, esp] using VG.Proof.CmacAes.X86.updSat)

end VG.Proof.CmacAes.X86

end
