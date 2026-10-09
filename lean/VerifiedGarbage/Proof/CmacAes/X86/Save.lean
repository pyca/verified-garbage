import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Proof.Aes.X86.Variant
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Impl.CmacAes.X86
import VerifiedGarbage.Proof.Cmac.Block32
import VerifiedGarbage.Proof.MdStream.X86.Common
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Omega

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
    let sched : Region := ⟨(arg s 0).setWidth 64, 240⟩
    let state : Region := ⟨(arg s 2).setWidth 64, 16⟩
    let data : Region := ⟨(arg s 3).setWidth 64, 16 * (arg s 4).toNat⟩
    let scr : Region := ⟨(arg s 5).setWidth 64, 2176⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 28, 28⟩
    s.rd = [sched, data, args] ∧ s.wr = [state, scr] ∧
      sched.Disjoint state ∧ sched.Disjoint scr ∧ data.Disjoint state ∧ data.Disjoint scr ∧
      state.Disjoint scr ∧ args.Disjoint state ∧ args.Disjoint scr ∧
      ret.Disjoint state ∧ ret.Disjoint scr ∧
      stack.Disjoint sched ∧ stack.Disjoint data ∧ stack.Disjoint state ∧ stack.Disjoint scr ∧
      (arg s 0).toNat + 240 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 16 ≤ 2 ^ 32 ∧
      (arg s 3).toNat + 16 * (arg s 4).toNat ≤ 2 ^ 32 ∧ (arg s 5).toNat + 2176 ≤ 2 ^ 32 ∧
      28 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 ∧
      ((arg s 1).toNat = 10 ∨ (arg s 1).toNat = 12 ∨ (arg s 1).toNat = 14)
  post s s' :=
    Spec.Aes.bytesAt s'.mem ((arg s 2).setWidth 64) 16 =
      Spec.Cmac.chain (ciphAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat)
        (Spec.Aes.bytesAt s.mem ((arg s 2).setWidth 64) 16)
        (Spec.Cmac.blocksAt s.mem ((arg s 3).setWidth 64) 16 (arg s 4).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 6, arg s₁ i = arg s₂ i

/-- `vg_cmac_aes_subkeys(schedule, rounds, subkeys, scratch)`. -/
def subkeysX86 : Contract isa where
  pre s :=
    let sched : Region := ⟨(arg s 0).setWidth 64, 240⟩
    let subk : Region := ⟨(arg s 2).setWidth 64, 32⟩
    let scr : Region := ⟨(arg s 3).setWidth 64, 2176⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 28, 28⟩
    s.rd = [sched, args] ∧ s.wr = [subk, scr] ∧
      sched.Disjoint subk ∧ sched.Disjoint scr ∧ subk.Disjoint scr ∧
      args.Disjoint subk ∧ args.Disjoint scr ∧ ret.Disjoint subk ∧ ret.Disjoint scr ∧
      stack.Disjoint sched ∧ stack.Disjoint subk ∧ stack.Disjoint scr ∧
      (arg s 0).toNat + 240 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 32 ≤ 2 ^ 32 ∧
      (arg s 3).toNat + 2176 ≤ 2 ^ 32 ∧ 28 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 ∧
      ((arg s 1).toNat = 10 ∨ (arg s 1).toNat = 12 ∨ (arg s 1).toNat = 14)
  post s s' :=
    let ks := Spec.Cmac.subkeys (ciphAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat) 16
    Spec.Aes.bytesAt s'.mem ((arg s 2).setWidth 64) 32 = ks.1 ++ ks.2
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 4, arg s₁ i = arg s₂ i

/-- `vg_cmac_aes_finalize(key, rounds, state, last, last_len, scratch)`. -/
def finalizeX86 : Contract isa where
  pre s :=
    let key : Region := ⟨(arg s 0).setWidth 64, 272⟩
    let state : Region := ⟨(arg s 2).setWidth 64, 16⟩
    let last : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
    let scr : Region := ⟨(arg s 5).setWidth 64, 2176⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 28, 28⟩
    s.rd = [key, last, args] ∧ s.wr = [state, scr] ∧
      key.Disjoint state ∧ key.Disjoint scr ∧ last.Disjoint state ∧ last.Disjoint scr ∧
      state.Disjoint scr ∧ args.Disjoint state ∧ args.Disjoint scr ∧
      ret.Disjoint state ∧ ret.Disjoint scr ∧
      stack.Disjoint key ∧ stack.Disjoint last ∧ stack.Disjoint state ∧ stack.Disjoint scr ∧
      (arg s 0).toNat + 272 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 16 ≤ 2 ^ 32 ∧
      (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧ (arg s 5).toNat + 2176 ≤ 2 ^ 32 ∧
      28 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 ∧
      ((arg s 1).toNat = 10 ∨ (arg s 1).toNat = 12 ∨ (arg s 1).toNat = 14) ∧ (arg s 4).toNat ≤ 16
  post s s' :=
    let ciph := ciphAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat
    let ks := Spec.Cmac.subkeys ciph 16
    Spec.Aes.bytesAt s.mem ((arg s 0).setWidth 64 + 240) 32 = ks.1 ++ ks.2 →
    ∀ msg : List Byte, msg.length % 16 = 0 → (msg = [] ∨ 0 < (arg s 4).toNat) →
      Spec.Aes.bytesAt s.mem ((arg s 2).setWidth 64) 16 =
        Spec.Cmac.chain ciph (Spec.Cmac.zeros 16) (Spec.Cmac.blocks 16 msg) →
      Spec.Aes.bytesAt s'.mem ((arg s 2).setWidth 64) 16 =
        Spec.Cmac.macFull ciph 16 (msg ++ Spec.Aes.bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 6, arg s₁ i = arg s₂ i

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

theorem xor4_eq (pb qb cb : Reg) (pd qd cd : Nat) : xor4 pb qb cb pd qd cd = xorBlk pb qb cb pd qd cd := rfl

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
    (k : ∀ s', Step s s' (s.mem.writeW C (s.mem.readW P 32 ^^^ s.mem.readW Q' 32)) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov .eax (.mem (at_ pb pd)) :: .mov .ecx (.mem (at_ qb qd)) :: .alu .xor .eax (.reg .ecx) ::
      .store (at_ cb cd) .eax :: is)) s Q := by
  subst hP hQ hC
  refine wp_movm (ea_at' _ _ _) rP fun s₁ u₁ => ?_
  refine wp_movm (by rw [ea_at', u₁.other _ hq]) (by rw [u₁.rd, u₁.wr]; exact rQ) fun s₂ u₂ => ?_
  refine wp_xor fun s₃ u₃ => ?_
  refine wp_store (by rw [ea_at', u₃.other _ hc₁, u₂.other _ hc₂, u₁.other _ hc₁])
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact wC) fun s₄ u₄ => k s₄ ⟨fun r h₁ h₂ => ?_, ?_, ?_, ?_⟩
  · rw [u₄.gpr, u₃.other _ h₁, u₂.other _ h₂, u₁.other _ h₁]
  · rw [u₄.mem, u₃.gpr, u₂.other _ (by decide), u₂.gpr, u₁.gpr, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]

/-- Word `i` of a block that does not wrap the 32-bit space. -/
theorem addr_word {b : BitVec 32} {d : Nat} (i : Nat) (h : b.toNat + d + 16 ≤ 2 ^ 32) (hi : i ≤ 12) :
    addr b (d + i) = b.setWidth 64 + BitVec.ofNat 64 d + BitVec.ofNat 64 i := by
  rw [addr_eq (by omega_arith), Offset.add_add]

theorem in_word {rs : List Region} {P : Addr} (h : Covers [⟨P, 16⟩] rs) {i : Nat} (hi : i ≤ 12) :
    InRegions rs (P + BitVec.ofNat 64 i) 4 :=
  h _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base P (by omega_arith) (by omega_arith)⟩

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
    (k : ∀ s', Step s s' (Proof.Cmac.xor4Mem s.mem ((s.gpr cb).setWidth 64 + BitVec.ofNat 64 cd)
        ((s.gpr pb).setWidth 64 + BitVec.ofNat 64 pd) ((s.gpr qb).setWidth 64 + BitVec.ofNat 64 qd)) →
      WP isa (.block is) s' Q) :
    WP isa (.block (xor4 pb qb cb pd qd cd ++ is)) s Q := by
  rw [xor4_eq]
  simp only [xorBlk, List.cons_append, List.nil_append]
  refine xw_ok hq₁ hc₁ hc₂ (addr_eq (by omega_arith)) (addr_eq (by omega_arith)) (addr_eq (by omega_arith))
    (in_word0 rP) (in_word0 rQ) (in_word0 wC) fun s₁ g₁ => ?_
  have e₁ : ∀ r, r ≠ .eax → r ≠ .ecx → s₁.gpr r = s.gpr r := g₁.gpr
  refine xw_ok (P := (s.gpr pb).setWidth 64 + BitVec.ofNat 64 pd + BitVec.ofNat 64 4)
    (Q' := (s.gpr qb).setWidth 64 + BitVec.ofNat 64 qd + BitVec.ofNat 64 4)
    (C := (s.gpr cb).setWidth 64 + BitVec.ofNat 64 cd + BitVec.ofNat 64 4) hq₁ hc₁ hc₂
    (by rw [e₁ _ hp₁ hp₂]; exact addr_word 4 fp (by decide))
    (by rw [e₁ _ hq₁ hq₂]; exact addr_word 4 fq (by decide))
    (by rw [e₁ _ hc₁ hc₂]; exact addr_word 4 fc (by decide))
    (by rw [g₁.rd, g₁.wr]; exact in_word rP (by decide)) (by rw [g₁.rd, g₁.wr]; exact in_word rQ (by decide))
    (by rw [g₁.wr]; exact in_word wC (by decide)) fun s₂ g₂ => ?_
  have e₂ : ∀ r, r ≠ .eax → r ≠ .ecx → s₂.gpr r = s.gpr r := fun r h₁ h₂ => by rw [g₂.gpr r h₁ h₂, e₁ r h₁ h₂]
  refine xw_ok (P := (s.gpr pb).setWidth 64 + BitVec.ofNat 64 pd + BitVec.ofNat 64 8)
    (Q' := (s.gpr qb).setWidth 64 + BitVec.ofNat 64 qd + BitVec.ofNat 64 8)
    (C := (s.gpr cb).setWidth 64 + BitVec.ofNat 64 cd + BitVec.ofNat 64 8) hq₁ hc₁ hc₂
    (by rw [e₂ _ hp₁ hp₂]; exact addr_word 8 fp (by decide))
    (by rw [e₂ _ hq₁ hq₂]; exact addr_word 8 fq (by decide))
    (by rw [e₂ _ hc₁ hc₂]; exact addr_word 8 fc (by decide))
    (by rw [g₂.rd, g₂.wr, g₁.rd, g₁.wr]; exact in_word rP (by decide))
    (by rw [g₂.rd, g₂.wr, g₁.rd, g₁.wr]; exact in_word rQ (by decide))
    (by rw [g₂.wr, g₁.wr]; exact in_word wC (by decide)) fun s₃ g₃ => ?_
  have e₃ : ∀ r, r ≠ .eax → r ≠ .ecx → s₃.gpr r = s.gpr r := fun r h₁ h₂ => by rw [g₃.gpr r h₁ h₂, e₂ r h₁ h₂]
  refine xw_ok (P := (s.gpr pb).setWidth 64 + BitVec.ofNat 64 pd + BitVec.ofNat 64 12)
    (Q' := (s.gpr qb).setWidth 64 + BitVec.ofNat 64 qd + BitVec.ofNat 64 12)
    (C := (s.gpr cb).setWidth 64 + BitVec.ofNat 64 cd + BitVec.ofNat 64 12) hq₁ hc₁ hc₂
    (by rw [e₃ _ hp₁ hp₂]; exact addr_word 12 fp (by decide))
    (by rw [e₃ _ hq₁ hq₂]; exact addr_word 12 fq (by decide))
    (by rw [e₃ _ hc₁ hc₂]; exact addr_word 12 fc (by decide))
    (by rw [g₃.rd, g₃.wr, g₂.rd, g₂.wr, g₁.rd, g₁.wr]; exact in_word rP (by decide))
    (by rw [g₃.rd, g₃.wr, g₂.rd, g₂.wr, g₁.rd, g₁.wr]; exact in_word rQ (by decide))
    (by rw [g₃.wr, g₂.wr, g₁.wr]; exact in_word wC (by decide)) fun s₄ g₄ => k s₄ ⟨?_, ?_, ?_, ?_⟩
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
  rw [zero4_eq]
  simp only [List.cons_append, List.nil_append]
  refine wp_movi fun s₀ u₀ => ?_
  have b₀ : s₀.gpr b = s.gpr b := u₀.other _ hb
  refine wp_store (a := (s.gpr b).setWidth 64 + BitVec.ofNat 64 d) (by rw [ea_at', b₀]; exact addr_eq (by omega_arith))
    (by rw [u₀.wr]; exact in_word0 wB) fun s₁ u₁ => ?_
  refine wp_store (a := (s.gpr b).setWidth 64 + BitVec.ofNat 64 d + BitVec.ofNat 64 4)
    (by rw [ea_at', u₁.gpr, b₀]; exact addr_word 4 fb (by decide))
    (by rw [u₁.wr, u₀.wr]; exact in_word wB (by decide)) fun s₂ u₂ => ?_
  refine wp_store (a := (s.gpr b).setWidth 64 + BitVec.ofNat 64 d + BitVec.ofNat 64 8)
    (by rw [ea_at', u₂.gpr, u₁.gpr, b₀]; exact addr_word 8 fb (by decide))
    (by rw [u₂.wr, u₁.wr, u₀.wr]; exact in_word wB (by decide)) fun s₃ u₃ => ?_
  refine wp_store (a := (s.gpr b).setWidth 64 + BitVec.ofNat 64 d + BitVec.ofNat 64 12)
    (by rw [ea_at', u₃.gpr, u₂.gpr, u₁.gpr, b₀]; exact addr_word 12 fb (by decide))
    (by rw [u₃.wr, u₂.wr, u₁.wr, u₀.wr]; exact in_word wB (by decide)) fun s₄ u₄ => k s₄ ?_ ?_ ?_ ?_
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
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_arith)

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

theorem hrs : Reg.esp ∉ ctrRegs := by decide

namespace CtrPre
variable {s : State} {W C D S : BitVec 32} {R : Nat} (h : CtrPre s W C D S R)
include h

theorem fit : 4 * ctrRegs.length + 4 ≤ (s.gpr .esp).toNat := by
  have := h.esp; simp only [List.length_cons, List.length_nil]; omega_arith

theorem args : arg (pushed ctrRegs s).callEntry 0 = W ∧ arg (pushed ctrRegs s).callEntry 1 = BitVec.ofNat 32 R ∧
    arg (pushed ctrRegs s).callEntry 2 = C ∧ arg (pushed ctrRegs s).callEntry 3 = D ∧
    arg (pushed ctrRegs s).callEntry 4 = 1 ∧ arg (pushed ctrRegs s).callEntry 5 = S := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  rw [callEntry_arg h.fit hrs (by decide)] <;> simp [h.eax, h.ecx, h.edx, h.ebx, h.edi, h.ebp]

theorem sub24 : Region.Sub (below (s.gpr .esp) 24) (below (s.gpr .esp) 28) := below_sub (by omega_arith) h.esp

theorem sub4 : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 28).setWidth 64, 4⟩ (below (s.gpr .esp) 28) := by
  have := below_inner (sp := s.gpr .esp) (a := 4) (b := 28) (k := 24) (by omega_arith) h.esp
  rw [show s.gpr .esp - BitVec.ofNat 32 28 = s.gpr .esp - BitVec.ofNat 32 24 - BitVec.ofNat 32 4 by
    rw [← VG.Offset.sub_add_eq]; rfl]
  exact this

theorem callPre : CallPre Proof.Aes.ctr32X86 ctrRegs (ctrRd (s.gpr .esp) W) (ctrWr C D S) s := by
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := h.args
  have hR := toNat_rounds h.rounds
  have eA : argAddr (pushed ctrRegs s).callEntry 0 = (s.gpr .esp - BitVec.ofNat 32 24).setWidth 64 := by
    rw [callEntry_argAddr0]; rfl
  have eSp : (pushed ctrRegs s).callEntry.gpr .esp = s.gpr .esp - BitVec.ofNat 32 28 := by
    rw [callEntry_esp']; rfl
  refine ⟨?_, ?_, ?_⟩
  · simp only [Proof.Aes.ctr32X86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, a4, a5, eA, eSp, hR,
      show (1 : BitVec 32).toNat = 1 from rfl, Nat.mul_one]
    refine ⟨trivial, trivial, h.wc, h.wd, h.ws, h.cd, h.cs, h.ds, (h.bc.sub_left h.sub24).symm.symm,
      (h.bd.sub_left h.sub24), (h.bs.sub_left h.sub24), h.bc.sub_left h.sub4, h.bd.sub_left h.sub4,
      h.bs.sub_left h.sub4, h.hW, h.hC, h.hD, h.hS, ?_, h.rounds⟩
    rw [sub_toNat (by have := h.esp; omega_arith)]; have := (s.gpr .esp).isLt; omega_arith
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

theorem ctr_call {s : State} {W C D S : BitVec 32} {R : Nat} (h : CtrPre s W C D S R) :
    WP isa (ctrCall v.callee) s (CtrPost s W C D S R) := by
  have hR := toNat_rounds h.rounds
  have hR' : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h' | h' | h' <;> omega_arith
  unfold ctrCall
  refine WP.callWith (rs := ctrRegs) (k := Proof.Aes.ctr32X86) v.ok v.nosp (by decide) hrs
    (by rw [v.stack]; have := h.esp; simp only [List.length_cons, List.length_nil]; omega_arith) h.callPre
    fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := h.args
  rw [v.stack] at f'
  have fE := callEntry_frame h.fit hrs
  rw [show 4 * ctrRegs.length + 4 = 28 from rfl] at fE
  have keep : ∀ {p : BitVec 32} {n k : Nat}, (below (s.gpr .esp) 28).Disjoint ⟨p.setWidth 64, n⟩ → k ≤ n →
      n ≤ 240 →
      Spec.Aes.bytesAt (pushed ctrRegs s).callEntry.mem (p.setWidth 64) k = Spec.Aes.bytesAt s.mem (p.setWidth 64) k :=
    fun hd hk hn => Proof.Cmac.bytesAt_frame fE (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hd.sub_right (Region.sub_prefix hk)).symm) (by omega_arith)
  obtain ⟨hdata, -⟩ := post
  simp only [arg_withRegions, State.withRegions_mem, a0, a1, a2, a3, a4, hR,
    show (1 : BitVec 32).toNat = 1 from rfl, m₂] at hdata
  have one : ∀ m : Mem, Spec.Gcm.blocksAt m (D.setWidth 64) 1 = [Spec.Gcm.blockAt m (D.setWidth 64)] :=
    fun m => by simp [Spec.Gcm.blocksAt]
  have bD : Spec.Gcm.blockAt (pushed ctrRegs s).callEntry.mem (D.setWidth 64) = 0 := by
    rw [Spec.Gcm.blockAt, keep h.bd (Nat.le_refl _) (by decide), h.zero, ofBytes_zeros]
  rw [one, one, bD, Proof.Cmac.ctr32_one, List.cons.injEq] at hdata
  refine ⟨rd', wr', cs', ?_, ?_⟩
  · exact f'.mono fun r hr => by simp only [List.cons_append, List.nil_append] at hr; simpa using hr
  · rw [Proof.Cmac.bytesAt_blockAt, hdata.1, Spec.Gcm.blockAt, keep h.bw hR' (Nat.le_refl _), keep h.bc (Nat.le_refl _) (by decide),
      Proof.Cmac.aesWith_bytes _ _ (Proof.Cmac.bytesAt_length _ _ _)]

/-- Calls of `vg_aes_ctr32` on one block, with the same arguments and stack
pointer in both runs, are constant time. -/
theorem ctr_rel {W C D S E : BitVec 32} {R : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → CtrPre s₁ W C D S R ∧ CtrPre s₂ W C D S R ∧ s₁.gpr .esp = E ∧ s₂.gpr .esp = E) :
    RelCT isa P (ctrCall v.callee) fun _ _ => True := by
  refine RelCT.callWith v.ok v.ct (ctrRd E W) (ctrWr C D S)
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
  rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with rfl | rfl | rfl | rfl | rfl | rfl
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
  Spill.saveMem_saved_ofNat m B g saved_fits (by decide) (r, d) h

/-! ## The stack arguments -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `mov d, [esp + 4 + 4 i]`, the stack argument `i` of the entry state `s₀`. -/
theorem wp_arg {d : Reg} {i : Nat} {s₀ : State} (hesp : s.gpr .esp = s₀.gpr .esp)
    (hin : InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4) (hv : s.mem.readW (argAddr s₀ i) 32 = arg s₀ i)
    (k : ∀ s', Upd s s' d (arg s₀ i) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (argOp i) :: is)) s Q :=
  wp_movm (by rw [ea_at', hesp]; rfl) hin fun s' u => k s' (hv ▸ u)

/-- `add d, [esp + 4 + 4 i]`. -/
theorem wp_addArg {d : Reg} {i : Nat} {s₀ : State} (hesp : s.gpr .esp = s₀.gpr .esp)
    (hin : InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4) (hv : s.mem.readW (argAddr s₀ i) 32 = arg s₀ i)
    (k : ∀ s', Upd s s' d (s.gpr d + arg s₀ i) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (argOp i) :: is)) s Q := by
  refine WP.cons (s' := (arithFlags s (s.gpr d + arg s₀ i)
    (2 ^ 32 ≤ (s.gpr d).toNat + (arg s₀ i).toNat) (addOverflow (s.gpr d) (arg s₀ i) (s.gpr d + arg s₀ i))).setReg d
      (s.gpr d + arg s₀ i)) ?_ (k _ (MdStream.X86.Upd.flags _ _ _ _ _ _))
  have ea : s.ea (at_ .esp (4 + 4 * i)) = argAddr s₀ i := by rw [ea_at', hesp]; rfl
  simp [exec, execAlu, readSrc, argOp, State.load32, ea, hin, hv]

end

end VG.Proof.CmacAes.X86
