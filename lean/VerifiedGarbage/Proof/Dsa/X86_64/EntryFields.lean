module
public import VerifiedGarbage.Impl.Dsa.X86_64.SignVerify
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp

import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Dsa.X86_64.Operands
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Attr.Core

/-! # Saving sign and verify arguments without changing stack inputs -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def signFields : List Instr :=
  [.mov32 .rax (.imm 0), .store (SignVerify.initial .signature) .rax,
    .store (SignVerify.initial .out) .rdi, .store (SignVerify.initial .p) .rdx,
    .store (SignVerify.initial .pLen) .r8, .store (SignVerify.initial .nonce) .r9,
    .mov .rax (.mem (Crt.stk 1)), .store (SignVerify.initial .qLen) .rax,
    .mov .rax (.mem (Crt.stk 2)), .store (SignVerify.initial .digest) .rax,
    .mov .rax (.mem (Crt.stk 3)), .store (SignVerify.initial .digestLen) .rax]

def verifyFields : List Instr :=
  [.mov32 .rax (.imm 0), .store (SignVerify.initial .out) .rax, .store (SignVerify.initial .nonce) .rax,
    .store (SignVerify.initial .p) .rdi, .store (SignVerify.initial .pLen) .rdx,
    .store (SignVerify.initial .qLen) .rcx, .store (SignVerify.initial .signature) .r8,
    .mov .rax (.mem (Crt.stk 1)), .store (SignVerify.initial .digest) .rax,
    .mov .rax (.mem (Crt.stk 2)), .store (SignVerify.initial .digestLen) .rax]

def signFieldMem (mem : Mem) (B out key plen nonce qlen digest digestLen : Addr) : Mem :=
  (((((((mem.writeW (off B Field.signature.offset) (0#64)).writeW (off B Field.out.offset) out).writeW (off B Field.p.offset) key).writeW
    (off B Field.pLen.offset) plen).writeW (off B Field.nonce.offset) nonce).writeW
    (off B Field.qLen.offset) qlen).writeW (off B Field.digest.offset) digest).writeW
    (off B Field.digestLen.offset) digestLen

def verifyFieldMem (mem : Mem) (B key plen qlen signature digest digestLen : Addr) : Mem :=
  (((((((mem.writeW (off B Field.out.offset) (0#64)).writeW (off B Field.nonce.offset) (0#64)).writeW (off B Field.p.offset) key).writeW (off B Field.pLen.offset) plen).writeW
    (off B Field.qLen.offset) qlen).writeW (off B Field.signature.offset) signature).writeW
    (off B Field.digest.offset) digest).writeW (off B Field.digestLen.offset) digestLen

theorem field_write_stack (mem : Mem) (B sp : Addr) (v : BitVec 64) (f : Field) {d Z : Nat}
    (hZ : pWorkspace ≤ Z) (hsep : ∀ i < 8, Z ≤ ofs B (off sp d + BitVec.ofNat 64 i)) :
    word (mem.writeW (off B f.offset) v) sp d = word mem sp d := by
  have hf := VG.Proof.Dsa.field_bounds f
  apply Mem.readW_congr
  intro i hi
  exact writeW_outside mem B v (Nat.le_trans hf.2 (by decide)) _ (Or.inr (Nat.le_trans (Nat.le_trans hf.2 hZ) (hsep i hi)))

theorem signFields_ok {s : State} {B sp qlen digest digestLen : Addr} {Z : Nat}
    (hs : Scr s B Z) (h11 : s.gpr .r11 = B) (hsp : s.gpr .rsp = sp) (hZ : pWorkspace ≤ Z)
    (hr : ∀ j, 1 ≤ j → j ≤ 3 → InRegions (s.rd ++ s.wr) (off sp (8 * j)) 8)
    (hsep : ∀ j, 1 ≤ j → j ≤ 3 → ∀ i < 8, Z ≤ ofs B (off sp (8 * j) + BitVec.ofNat 64 i))
    (hq : word s.mem sp 8 = qlen) (hd : word s.mem sp 16 = digest) (hdl : word s.mem sp 24 = digestLen) :
    WP isa (.block signFields) s fun t =>
      t.mem = signFieldMem s.mem B (s.gpr .rdi) (s.gpr .rdx) (s.gpr .r8) (s.gpr .r9) qlen digest digestLen ∧
      Keep [.rax] s t := by
  refine WP.keep [.rax] ?_ rfl
  have hw (f : Field) := hs.st (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 hZ)
  have hstack (mem : Mem) (v : BitVec 64) (f : Field) (j : Nat) (hj : 1 ≤ j ∧ j ≤ 3) :=
    field_write_stack mem B sp v f hZ (hsep j hj.1 hj.2)
  unfold signFields
  rw [show Crt.stk 1 = ({ base := .rsp, disp := 8 } : MemOp) from rfl,
    show Crt.stk 2 = ({ base := .rsp, disp := 16 } : MemOp) from rfl,
    show Crt.stk 3 = ({ base := .rsp, disp := 24 } : MemOp) from rfl]
  xrun [State.ea, SignVerify.initial, h11, hsp, fieldAddress,
    show sp + BitVec.ofInt 64 8 = off sp 8 from rfl,
    show sp + BitVec.ofInt 64 16 = off sp 16 from rfl,
    show sp + BitVec.ofInt 64 24 = off sp 24 from rfl,
    hw .signature, hw .out, hw .p, hw .pLen, hw .nonce, hw .qLen, hw .digest, hw .digestLen,
    hr 1 (by decide) (by decide), hr 2 (by decide) (by decide), hr 3 (by decide) (by decide),
    hstack _ _ _ 1 (by decide), hstack _ _ _ 2 (by decide), hstack _ _ _ 3 (by decide), hq, hd, hdl]
  rfl

theorem verifyFields_ok {s : State} {B sp digest digestLen : Addr} {Z : Nat}
    (hs : Scr s B Z) (h11 : s.gpr .r11 = B) (hsp : s.gpr .rsp = sp) (hZ : pWorkspace ≤ Z)
    (hr : ∀ j, 1 ≤ j → j ≤ 2 → InRegions (s.rd ++ s.wr) (off sp (8 * j)) 8)
    (hsep : ∀ j, 1 ≤ j → j ≤ 2 → ∀ i < 8, Z ≤ ofs B (off sp (8 * j) + BitVec.ofNat 64 i))
    (hd : word s.mem sp 8 = digest) (hdl : word s.mem sp 16 = digestLen) :
    WP isa (.block verifyFields) s fun t =>
      t.mem = verifyFieldMem s.mem B (s.gpr .rdi) (s.gpr .rdx) (s.gpr .rcx) (s.gpr .r8) digest digestLen ∧
      Keep [.rax] s t := by
  refine WP.keep [.rax] ?_ rfl
  have hw (f : Field) := hs.st (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 hZ)
  have hstack (mem : Mem) (v : BitVec 64) (f : Field) (j : Nat) (hj : 1 ≤ j ∧ j ≤ 2) :=
    field_write_stack mem B sp v f hZ (hsep j hj.1 hj.2)
  unfold verifyFields
  rw [show Crt.stk 1 = ({ base := .rsp, disp := 8 } : MemOp) from rfl,
    show Crt.stk 2 = ({ base := .rsp, disp := 16 } : MemOp) from rfl]
  xrun [State.ea, SignVerify.initial, h11, hsp, fieldAddress,
    show sp + BitVec.ofInt 64 8 = off sp 8 from rfl,
    show sp + BitVec.ofInt 64 16 = off sp 16 from rfl,
    hw .out, hw .nonce, hw .p, hw .pLen, hw .qLen, hw .signature, hw .digest, hw .digestLen,
    hr 1 (by decide) (by decide), hr 2 (by decide) (by decide),
    hstack _ _ _ 1 (by decide), hstack _ _ _ 2 (by decide), hd, hdl]
  rfl

end VG.Proof.Dsa.X86_64
