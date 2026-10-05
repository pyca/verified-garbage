import VerifiedGarbage.Spec.Siv.Contract
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.AesGcm.X86.Fn
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Impl.AesSiv.X86
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.CmacAes.Stream.X86.Frame
import VerifiedGarbage.Proof.AesGcm.X86.StreamCrypt
import VerifiedGarbage.Proof.AesSiv.Long
import VerifiedGarbage.Proof.AesSiv.Scratch
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.StackScratch
import VerifiedGarbage.Proof.Framework.X86.Inline

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.X86.Contract`. -/
section

/-!
# AES-SIV on x86: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Siv/Contract.lean` (with `init`'s working space as
an argument, `Proof/AesSiv/Scratch.lean`), which imply these
(`Verified.lean`). The arguments are on the stack, from `[esp + 4]`
(cdecl); the shared contracts let the functions overwrite them
(`writeArgs`), which they do not: the proofs are on states where they are
read-only (`Verified.of_narrow`), so that the taint analysis knows they are
public.
-/

namespace VG.Proof.AesSiv.X86

open VG VG.X86

/-- `initCore(key, key_len, ctx, scratch)`: its calls push their four
arguments and the return address, and `vg_cmac_aes_subkeys`'s own calls
theirs, 48 bytes below `esp`. -/
def initX86 : Contract isa where
  pre s :=
    let key : Region := ⟨(VG.X86.arg s 0).setWidth 64, (VG.X86.arg s 1).toNat⟩
    let ctx : Region := ⟨(VG.X86.arg s 2).setWidth 64, 512⟩
    let scr : Region := ⟨(VG.X86.arg s 3).setWidth 64, 2560⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 48, 48⟩
    s.rd = [key, args] ∧ s.wr = [ctx, scr] ∧
      key.Disjoint ctx ∧ key.Disjoint scr ∧ key.Disjoint args ∧ ctx.Disjoint scr ∧ ctx.Disjoint args ∧
      scr.Disjoint args ∧ ret.Disjoint key ∧ ret.Disjoint ctx ∧ ret.Disjoint scr ∧ ret.Disjoint args ∧
      stack.Disjoint key ∧ stack.Disjoint ctx ∧ stack.Disjoint scr ∧ stack.Disjoint args ∧
      (VG.X86.arg s 0).toNat + (VG.X86.arg s 1).toNat ≤ 2 ^ 32 ∧ (VG.X86.arg s 2).toNat + 512 ≤ 2 ^ 32 ∧
      (VG.X86.arg s 3).toNat + 2560 ≤ 2 ^ 32 ∧ 48 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 ∧
      ((VG.X86.arg s 1).toNat = 32 ∨ (VG.X86.arg s 1).toNat = 48 ∨ (VG.X86.arg s 1).toNat = 64)
  post s s' :=
    Spec.Siv.KeyRepr s'.mem ((VG.X86.arg s 2).setWidth 64) (Spec.Aes.bytesAt s.mem ((VG.X86.arg s 0).setWidth 64) (VG.X86.arg s 1).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 4, VG.X86.arg s₁ i = VG.X86.arg s₂ i

end VG.Proof.AesSiv.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.X86.Env`. -/
section

/-!
# AES-SIV on x86: where everything is

Untrusted: everything here is checked by Lean. The key context (512 bytes
at `C`), the working space (2576 bytes at `W`) and the 56 bytes of stack
below `SP` that the calls use (`Lay`); what a state may access (`Perm`); the
registers holding `W` and the stack pointer (`Env`); and the public values
the entry keeps in `W` (`Slots`). The pieces write the parts of `W` in
`mutR` (and the data, and the stack below `SP`), so the slots and our
caller's registers saved in `W` stay as the entry left them.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.X86

open VG VG.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86 (w64 toNat_ofNat32 toNat_add32 w64_add covers_off in_off in_left covers_left
  covers_cons covers_nil slotv)

/-! ## Covering -/

theorem covers_of_mem {r : Region} {ts : List Region} (h : r ∈ ts) : Covers [r] ts := by
  intro a n ⟨x, hx, hc⟩
  simp only [List.mem_singleton] at hx; subst hx; exact ⟨x, h, hc⟩

/-! ## The regions -/

/-- The key context, `W` and the stack below `SP` used by the calls. -/
structure Lay (C W SP : BitVec 32) : Prop where
  fc : C.toNat + 512 ≤ 2 ^ 32
  fw : W.toNat + 2576 ≤ 2 ^ 32
  sp : 56 ≤ SP.toNat
  c_w : (⟨w64 C, 512⟩ : Region).Disjoint ⟨w64 W, 2576⟩
  stk_c : (below SP 56).Disjoint ⟨w64 C, 512⟩
  stk_w : (below SP 56).Disjoint ⟨w64 W, 2576⟩

/-- What a state may access. -/
structure Perm (C W : BitVec 32) (s : State) : Prop where
  c : Covers [⟨w64 C, 512⟩] (s.rd ++ s.wr)
  w : Covers [⟨w64 W, 2576⟩] s.wr

/-- The registers holding `W` and the stack pointer, and what the state may
access. -/
structure Env (C W SP : BitVec 32) (s : State) : Prop where
  ebp : s.gpr .ebp = W
  esp : s.gpr .esp = SP
  perm : VG.Proof.AesSiv.X86.Perm C W s

theorem Perm.of_eq {C W : BitVec 32} {s s' : State} (h : VG.Proof.AesSiv.X86.Perm C W s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    VG.Proof.AesSiv.X86.Perm C W s' := ⟨by rw [hrd, hwr]; exact h.c, by rw [hwr]; exact h.w⟩

/-- An environment, after code that keeps `ebp`, `esp` and the permissions. -/
theorem Env.keep {C W SP : BitVec 32} {s s' : State} (h : VG.Proof.AesSiv.X86.Env C W SP s) (hbp : s'.gpr .ebp = s.gpr .ebp)
    (hsp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesSiv.X86.Env C W SP s' :=
  ⟨by rw [hbp, h.ebp], by rw [hsp, h.esp], h.perm.of_eq hrd hwr⟩

namespace Lay

theorem cSub {C : Addr} {d n : Nat} (h : d + n ≤ 512) : Region.Sub ⟨C + BitVec.ofNat 64 d, n⟩ ⟨C, 512⟩ :=
  Offset.sub_base _ h

theorem wSub {W : Addr} {d n : Nat} (h : d + n ≤ 2576) : Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 2576⟩ :=
  Offset.sub_base _ h

/-- Parts of `W` are disjoint. -/
theorem w_w {W : BitVec 32} {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 2576) (hd : d + k ≤ 2576) :
    (⟨w64 W + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 d, k⟩ :=
  Offset.disjoint _ h (by omega) (by omega)

variable {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP)
include L

theorem c_w' {a n d k : Nat} (ha : a + n ≤ 512) (hd : d + k ≤ 2576) :
    (⟨w64 C + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 d, k⟩ :=
  (L.c_w.sub_left (VG.Proof.AesSiv.X86.Lay.cSub ha)).sub_right (VG.Proof.AesSiv.X86.Lay.wSub hd)

theorem stk_w' {a n : Nat} (ha : a + n ≤ 2576) : (below SP 56).Disjoint ⟨w64 W + BitVec.ofNat 64 a, n⟩ :=
  L.stk_w.sub_right (VG.Proof.AesSiv.X86.Lay.wSub ha)

theorem stk_c' {a n : Nat} (ha : a + n ≤ 512) : (below SP 56).Disjoint ⟨w64 C + BitVec.ofNat 64 a, n⟩ :=
  L.stk_c.sub_right (VG.Proof.AesSiv.X86.Lay.cSub ha)

theorem aW {o : Nat} (ho : o < 2576) : w64 (W + BitVec.ofNat 32 o) = w64 W + BitVec.ofNat 64 o :=
  w64_add (by have := L.fw; omega)

/-- `aW` for `setWidth`, as the callees' arguments state it. -/
theorem sW {o : Nat} (ho : o < 2576) : (W + BitVec.ofNat 32 o).setWidth 64 = w64 W + BitVec.ofNat 64 o :=
  L.aW ho

theorem nW {o : Nat} (ho : o < 2576) : (W + BitVec.ofNat 32 o).toNat = W.toNat + o :=
  toNat_add32 (by have := L.fw; omega)

theorem aC {o : Nat} (ho : o < 512) : w64 (C + BitVec.ofNat 32 o) = w64 C + BitVec.ofNat 64 o :=
  w64_add (by have := L.fc; omega)

theorem nC {o : Nat} (ho : o < 512) : (C + BitVec.ofNat 32 o).toNat = C.toNat + o :=
  toNat_add32 (by have := L.fc; omega)

end Lay

namespace Perm

variable {C W : BitVec 32} {s : State} (P : VG.Proof.AesSiv.X86.Perm C W s)
include P

theorem cR {d n : Nat} (h : d + n ≤ 512) : InRegions (s.rd ++ s.wr) (w64 C + BitVec.ofNat 64 d) n :=
  in_off P.c h (by decide)

theorem wW {d n : Nat} (h : d + n ≤ 2576) : InRegions s.wr (w64 W + BitVec.ofNat 64 d) n :=
  in_off P.w h (by decide)

theorem wR {d n : Nat} (h : d + n ≤ 2576) : InRegions (s.rd ++ s.wr) (w64 W + BitVec.ofNat 64 d) n :=
  in_left (P.wW h)

theorem cC {d n : Nat} (h : d + n ≤ 512) : Covers [⟨w64 C + BitVec.ofNat 64 d, n⟩] (s.rd ++ s.wr) :=
  covers_off P.c h (by decide)

theorem wC {d n : Nat} (h : d + n ≤ 2576) : Covers [⟨w64 W + BitVec.ofNat 64 d, n⟩] s.wr :=
  covers_off P.w h (by decide)

end Perm

/-! ## Buffers -/

/-- A buffer of `n` bytes at `D` that the code may read, apart from `W` and
the stack below `SP`. -/
structure Buf (W SP : BitVec 32) (s : State) (D : BitVec 32) (n : Nat) : Prop where
  rd : Covers [⟨w64 D, n⟩] (s.rd ++ s.wr)
  wrap : D.toNat + n ≤ 2 ^ 32
  w : (⟨w64 D, n⟩ : Region).Disjoint ⟨w64 W, 2576⟩
  stk : (below SP 56).Disjoint ⟨w64 D, n⟩

namespace Buf

variable {W SP : BitVec 32} {s : State} {D : BitVec 32} {n : Nat} (h : VG.Proof.AesSiv.X86.Buf W SP s D n)
include h

theorem of_eq {s' : State} (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesSiv.X86.Buf W SP s' D n :=
  { h with rd := by rw [hrd, hwr]; exact h.rd }

theorem lt : n < 2 ^ 64 := by have := h.wrap; omega

omit h in
/-- The address of byte `k`. -/
theorem ptr {k : Nat} (hk : D.toNat + k < 2 ^ 32) : w64 (D + BitVec.ofNat 32 k) = w64 D + BitVec.ofNat 64 k :=
  w64_add hk

/-- The bytes from `k` on. -/
theorem drop {k : Nat} (hk : k ≤ n) (hw : D.toNat + k < 2 ^ 32) : VG.Proof.AesSiv.X86.Buf W SP s (D + BitVec.ofNat 32 k) (n - k) where
  rd := by rw [VG.Proof.AesSiv.X86.Buf.ptr hw]; exact covers_off h.rd (by omega) h.lt
  wrap := by rw [toNat_add32 hw]; have := h.wrap; omega
  w := by rw [VG.Proof.AesSiv.X86.Buf.ptr hw]; exact h.w.sub_left (Offset.sub_base _ (by omega))
  stk := by rw [VG.Proof.AesSiv.X86.Buf.ptr hw]; exact h.stk.sub_right (Offset.sub_base _ (by omega))

/-- The first `k` bytes. -/
theorem take {k : Nat} (hk : k ≤ n) : VG.Proof.AesSiv.X86.Buf W SP s D k where
  rd := fun a m ⟨r, hr, hc⟩ => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.rd a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩
  wrap := by have := h.wrap; omega
  w := h.w.sub_left (Region.sub_prefix hk)
  stk := h.stk.sub_right (Region.sub_prefix hk)

end Buf

/-! ## The slots -/

/-- The public values the entry keeps in `W` that no piece changes: the key
context, the rounds, the data and its length. -/
structure Slots (W C : BitVec 32) (R : Nat) (D : BitVec 32) (n : Nat) (m : Mem) : Prop where
  ctx : slotv m W Impl.AesSiv.X86.ctxO = C
  rounds : slotv m W Impl.AesSiv.X86.roundsO = BitVec.ofNat 32 R
  data : slotv m W Impl.AesSiv.X86.dataO = D
  len : slotv m W Impl.AesSiv.X86.lenO = BitVec.ofNat 32 n

/-- The parts of `W` the pieces write: the blocks at `[0, 128)`, the CMAC
state and `dbl(D)` at `[144, 176)`, the descriptors' cursor and count at
`[184, 192)`, the variables of the pieces at `[200, 256)`, and from `256` on
(the working space of the functions called, and `D`). -/
abbrev wA (W : BitVec 32) : Region := ⟨w64 W + BitVec.ofNat 64 16, 112⟩
abbrev wB (W : BitVec 32) : Region := ⟨w64 W + BitVec.ofNat 64 144, 32⟩
abbrev wV (W : BitVec 32) : Region := ⟨w64 W + BitVec.ofNat 64 184, 8⟩
abbrev wS (W : BitVec 32) : Region := ⟨w64 W + BitVec.ofNat 64 200, 56⟩
abbrev wC (W : BitVec 32) : Region := ⟨w64 W + BitVec.ofNat 64 256, 2320⟩

/-- What the pieces may change: those parts of `W`, the stack below `SP`
and the data. -/
abbrev mutR (W SP D : BitVec 32) (n : Nat) : List Region :=
  [VG.Proof.AesSiv.X86.wA W, VG.Proof.AesSiv.X86.wB W, VG.Proof.AesSiv.X86.wV W, VG.Proof.AesSiv.X86.wS W, VG.Proof.AesSiv.X86.wC W, below SP 56, ⟨w64 D, n⟩]

/-- The part of `W` at `[d, d + k)`, when it misses the parts the pieces write. -/
theorem kept_mut {C W SP D : BitVec 32} {n : Nat} (L : VG.Proof.AesSiv.X86.Lay C W SP)
    (hD : (⟨w64 D, n⟩ : Region).Disjoint ⟨w64 W, 2576⟩) {d k : Nat}
    (hd : 128 ≤ d ∧ d + k ≤ 144 ∨ 176 ≤ d ∧ d + k ≤ 184 ∨ 192 ≤ d ∧ d + k ≤ 200) :
    ∀ r ∈ VG.Proof.AesSiv.X86.mutR W SP D n, (⟨w64 W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Lay.w_w (.inr (by omega)) (by omega) (by decide)
  · exact Lay.w_w (by omega) (by omega) (by decide)
  · exact Lay.w_w (by omega) (by omega) (by decide)
  · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (L.stk_w' (by omega)).symm
  · exact (hD.sub_right (Lay.wSub (by omega))).symm

/-- The slots, after code that changes only `mutR`. -/
theorem slots_mut {C W SP D' : BitVec 32} {n' : Nat} (L : VG.Proof.AesSiv.X86.Lay C W SP)
    (hD : (⟨w64 D', n'⟩ : Region).Disjoint ⟨w64 W, 2576⟩) {m m' : Mem} (hf : Frame (VG.Proof.AesSiv.X86.mutR W SP D' n') m m')
    {R : Nat} {D : BitVec 32} {n : Nat} (S : VG.Proof.AesSiv.X86.Slots W C R D n m) : VG.Proof.AesSiv.X86.Slots W C R D n m' := by
  have k : ∀ o, (128 ≤ o ∧ o + 4 ≤ 144 ∨ 176 ≤ o ∧ o + 4 ≤ 184 ∨ 192 ≤ o ∧ o + 4 ≤ 200) →
      slotv m' W o = slotv m W o := fun o ho =>
    hf.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (VG.Proof.AesSiv.X86.kept_mut L hD ho) (by decide)
  exact ⟨by rw [k _ (by decide)]; exact S.ctx, by rw [k _ (by decide)]; exact S.rounds,
    by rw [k _ (by decide)]; exact S.data, by rw [k _ (by decide)]; exact S.len⟩

end VG.Proof.AesSiv.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.X86.Run`. -/
section

/-!
# AES-SIV on x86: running straight-line blocks

Untrusted: everything here is checked by Lean. `crun [facts]` runs a block
symbolically (`runBlock_cons`, `runStep_some`, the semantics of the
instructions the code uses, and reads through the writes with `RegUpd`,
keeping the registers folded), as AES-GCM's `xrun` does, with the offsets
of the AES-SIV code.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesSiv.X86
open VG.Impl.AesGcm.X86 (at_ imm slot argOp)
open VG.Proof.AesGcm.X86 (store32_eq store8_eq gpr_setMem mem_setMem rd_setMem wr_setMem cf_setMem zf_setMem
  readW_writeW_off CT)

/-- A word at `p + a`, after a byte written at `p + b` elsewhere. -/
theorem readW_writeB_off (m : Mem) (p : Addr) (v : BitVec 8) {a b : Nat} (h : a + 4 ≤ b ∨ b + 1 ≤ a)
    (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (m.writeW (p + BitVec.ofNat 64 b) v).readW (p + BitVec.ofNat 64 a) 32 = m.readW (p + BitVec.ofNat 64 a) 32 :=
  Mem.readW_writeW_sep (Offset.sep _ h (by omega) (by omega)) (by decide)

theorem add_ofNat_assoc (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- Runs a block of the instructions the AES-SIV code uses. The facts given
rewrite the addresses and discharge the permissions. -/
macro "crun" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp (disch := first | decide | omega) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc, execAlu, execShift, State.load32, store32_eq, State.load8, store8_eq,
    State.ea, at_, imm, slot, argOp, zOff, tailOff, ksOff, cbOff, tOff, stOff, dbOff, ctxO, roundsO, adsO, leftO,
    dataO, lenO, strO, slenO, nbO, jO, okO, csOff, dOff, List.cons_append, List.nil_append, List.append_assoc,
    Option.bind_some, Option.map_some, readW_writeW_off, readW_writeB_off, gpr_setReg_self, gpr_setReg_of_ne, gpr_arithFlags, gpr_setFlags, mem_setReg,
    mem_arithFlags, mem_setFlags, rd_setReg, rd_arithFlags, rd_setFlags, wr_setReg, wr_arithFlags,
    wr_setFlags, cf_setReg, cf_arithFlags, zf_setReg, zf_arithFlags, gpr_setMem, mem_setMem, rd_setMem,
    wr_setMem, cf_setMem, zf_setMem, ite_true, ite_false, reduceCtorEq, Nat.reduceAdd, ↓reduceIte, Nat.reduceLT,
    Nat.reduceLeDiff, Nat.reduceSub, Nat.reduceEqDiff, Nat.reduceMul, and_self, and_true, true_and,
    eq_self_iff_true, Reg8.reg, $ts,*]) <;>
  try rfl)

/-- Reads registers through the writes of a block. -/
macro "cregs" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp (disch := first | decide | with_reducible assumption) only [gpr_setMem, gpr_setReg_self, gpr_setReg_of_ne, gpr_arithFlags, gpr_setFlags,
    $ts,*]))

/-- Reads the memory, flags and permissions through the writes of a block. -/
macro "cmems" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp (disch := first | decide | omega) only [mem_setMem, mem_setReg, mem_arithFlags, mem_setFlags,
    rd_setMem, rd_setReg, rd_arithFlags, rd_setFlags, wr_setMem, wr_setReg, wr_arithFlags, wr_setFlags,
    zf_setMem, zf_setReg, zf_arithFlags, cf_setMem, cf_setReg, cf_arithFlags, gpr_setMem, gpr_setReg_self,
    gpr_setReg_of_ne, gpr_arithFlags, gpr_setFlags, Mem.readW_writeW_self32, readW_writeW_off, readW_writeB_off, zOff, tailOff,
    ksOff, cbOff, tOff, stOff, dbOff, ctxO, roundsO, adsO, leftO, dataO, lenO, strO, slenO, nbO, jO, okO, csOff, dOff,
    Nat.reduceAdd, Reg8.reg, eq_self_iff_true, and_self, $ts,*]))

theorem eval_e {s : State} {b : Bool} (h : s.zf = some b) : isa.eval .e s = some b := h

theorem eval_ne {s : State} {b : Bool} (h : s.zf = some b) : isa.eval .ne s = some !b := by
  show s.zf.map _ = _; rw [h]; rfl

theorem eval_b {s : State} {b : Bool} (h : s.cf = some b) : isa.eval .b s = some b := h

theorem seq_assoc {a b c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa (.seq (.seq a b) c) s Q) :
    WP isa (.seq a (.seq b c)) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp (WP.seq_iff.mp h)) fun _ h => WP.seq h)

/-- A block, then code: the block constant time by the taint analysis from
the registers `rs`, which `I` pins, and the code from what the block leaves
(`F`, from the state it started in). -/
theorem CT.block_seq {I : State → Prop} {is : List Instr} {c : Prog isa} {F : State → State → Prop}
    (rs : List Reg) (hr : ∀ s₁ s₂, I s₁ → I s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) {hc : Taint.Hint VG.X86.taint.T}
    (h : (VG.X86.taint.check (τr rs) (.block is) hc).isSome = true)
    (blk : ∀ s, I s → ∃ s', runBlock isa is s = some s' ∧ F s s') (h₂ : CT (fun s' => ∃ s, I s ∧ F s s') c) :
    CT I (.seq (.block is) c) :=
  CT.seq (CT.taint rs hr h) (fun s hs => let ⟨s', r, f⟩ := blk s hs; WP.of_runBlock ⟨s', r, s, hs, f⟩) h₂

/-- `a; (b; (c; d))` from `(a; (b; c)); d`. -/
theorem CT.assoc3 {I : State → Prop} {a b c d : Prog isa}
    (h : Proof.AesGcm.X86.CT I (.seq (.seq a (.seq b c)) d)) : Proof.AesGcm.X86.CT I (.seq a (.seq b (.seq c d))) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq a₁ e₁ =>
    cases e₁ with
    | seq b₁ e₁ =>
      cases e₁ with
      | seq c₁ d₁ =>
        cases e₂ with
        | seq a₂ e₂ =>
          cases e₂ with
          | seq b₂ e₂ =>
            cases e₂ with
            | seq c₂ d₂ =>
              obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq (.seq a₁ (.seq b₁ c₁)) d₁) (.seq (.seq a₂ (.seq b₂ c₂)) d₂)
              simp only [List.append_assoc] at ht
              exact ⟨ht, hq⟩

/-- A register pinned. -/
theorem pin1 {I : State → Prop} {a : Reg} {x : BitVec 32} (h : ∀ s, I s → s.gpr a = x) :
    ∀ s₁ s₂, I s₁ → I s₂ → ∀ r ∈ [a], s₁.gpr r = s₂.gpr r := fun s₁ s₂ h₁ h₂ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h _ h₁, h _ h₂]

/-- `ebp` pinned. -/
theorem pin_ebp {I : State → Prop} {W : BitVec 32} (h : ∀ s, I s → s.gpr .ebp = W) :
    ∀ s₁ s₂, I s₁ → I s₂ → ∀ r ∈ [Reg.ebp], s₁.gpr r = s₂.gpr r := fun s₁ s₂ h₁ h₂ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h _ h₁, h _ h₂]

/-- Two registers pinned. -/
theorem pin2 {I : State → Prop} {a b : Reg} {x y : BitVec 32} (h : ∀ s, I s → s.gpr a = x ∧ s.gpr b = y) :
    ∀ s₁ s₂, I s₁ → I s₂ → ∀ r ∈ [a, b], s₁.gpr r = s₂.gpr r := fun s₁ s₂ h₁ h₂ r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [(h _ h₁).1, (h _ h₂).1]
  · rw [(h _ h₁).2, (h _ h₂).2]

/-- Three registers pinned. -/
theorem pin3 {I : State → Prop} {a b c : Reg} {x y z : BitVec 32}
    (h : ∀ s, I s → s.gpr a = x ∧ s.gpr b = y ∧ s.gpr c = z) :
    ∀ s₁ s₂, I s₁ → I s₂ → ∀ r ∈ [a, b, c], s₁.gpr r = s₂.gpr r := fun s₁ s₂ h₁ h₂ r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [(h _ h₁).1, (h _ h₂).1]
  · rw [(h _ h₁).2.1, (h _ h₂).2.1]
  · rw [(h _ h₁).2.2, (h _ h₂).2.2]

/-- A loop of `n` iterations, its body constant time and leaving the
condition to loop back exactly while iterations are left. -/
theorem CT.loopN {body : Prog isa} {c : Cond} (Inv : Nat → State → Prop)
    (hb : ∀ n, Proof.AesGcm.X86.CT (Inv n) body)
    (hw : ∀ n s, Inv n s → WP isa body s fun s' => 0 < n ∧ isa.eval c s' = some (decide (n ≠ 1)) ∧
      (n ≠ 1 → Inv (n - 1) s'))
    (n : Nat) : Proof.AesGcm.X86.CT (Inv n) (.loop body c) := by
  refine RelCT.loop (M := isa) (Q := fun _ _ => True) (fun n (s₁ s₂ : State) => Inv n s₁ ∧ Inv n s₂) (fun n => ?_) n
  have h := RelCT.wp (hb n) (F₁ := fun s' => 0 < n ∧ isa.eval c s' = some (decide (n ≠ 1)) ∧
      (n ≠ 1 → Inv (n - 1) s')) (F₂ := fun s' => 0 < n ∧ isa.eval c s' = some (decide (n ≠ 1)) ∧
      (n ≠ 1 → Inv (n - 1) s')) fun s₁ s₂ h => ⟨hw n s₁ h.1, hw n s₂ h.2⟩
  refine RelCT.mono h (fun _ _ h => h) fun s₁ s₂ ⟨_, ⟨hn, c₁, i₁⟩, ⟨_, c₂, i₂⟩⟩ => ⟨by rw [c₁, c₂], fun _ => trivial,
    fun ht => ?_⟩
  rw [c₁] at ht
  have h1 : n ≠ 1 := by simpa using ht
  exact ⟨n - 1, by omega, i₁ h1, i₂ h1⟩

end VG.Proof.AesSiv.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.X86.FinRaw`. -/
section

/-!
# AES-SIV on x86: calling `vg_cmac_aes_finalize` with any subkeys

Untrusted: everything here is checked by Lean. `vg_cmac_aes_finalize`'s
contract gives the CMAC of the message only when the subkeys in its `key`
are those of the key schedule's cipher. Its code needs no such thing: it
computes `CIPH_K(C ⊕ Mₙ)` from whatever subkeys `key` holds, for the chaining
value `C` at `state` and the last block `Mₙ` of §6.2 step 4
(`finalize_raw_wp`, as x86-64's AES-SIV has it). AES-SIV's contracts compute
with the subkeys its key context holds (`Spec.Siv.ctxMac`), so its calls use
this (`finr_call`), with `WP.callWith` from this correctness of the same
code.
-/

namespace VG.Proof.AesSiv.X86

open VG VG.X86
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Proof.CmacAes.X86
open VG.Proof.CmacAes.Stream.X86 (FArgs rs6 hrs6 fin_nosp fin_stack entry_bytes eq_ofNat fRd fWr)
open VG.Impl.CmacAes.X86 (finalize finPre saved)

/-- What `vg_cmac_aes_finalize`'s code computes, from any subkeys. -/
def finalizeRawX86 : Contract isa where
  pre := finalizeX86.pre
  post s s' :=
    Spec.Aes.bytesAt s'.mem ((VG.X86.arg s 2).setWidth 64) 16 =
      Spec.Cmac.aesWith (VG.X86.arg s 1).toNat (Spec.Aes.bytesAt s.mem ((VG.X86.arg s 0).setWidth 64) (16 * ((VG.X86.arg s 1).toNat + 1)))
        (Spec.Cmac.xor (mn s) (Spec.Aes.bytesAt s.mem ((VG.X86.arg s 2).setWidth 64) 16))
  pub := finalizeX86.pub

theorem finalize_raw_wp (v : Ctr32Impl) {s₀ : State} (h0 : finalizeX86.pre s₀) :
    WP isa (finalize v.callee) s₀ fun s' => abiPreserved s₀ s' ∧ finalizeRawX86.post s₀ s' := by
  have hp := FPre.of h0
  have hR := hp.rounds
  have hRb : 16 * (R s₀ + 1) ≤ 240 := by rcases hR with h | h | h <;> omega
  have hsc : (VG.X86.arg s₀ 5).toNat + 2176 ≤ 2 ^ 32 := hp.scr_fit
  have cA := hp.cA
  unfold finalize
  refine WP.seq (WP.mono (VG.Proof.CmacAes.X86.finPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (VG.Proof.CmacAes.X86.ctr_call v h₁.pre) fun s₂ h₂ => ?_)
  have hb : below (s₁.gpr .esp) 28 = VG.Proof.CmacAes.X86.stkR s₀ := by rw [h₁.esp]; exact hp.below_eq
  have f₁ : Frame [VG.Proof.CmacAes.X86.stR s₀, ⟨(S s₀).setWidth 64, 2064⟩, VG.Proof.CmacAes.X86.stkR s₀] (VG.Proof.CmacAes.X86.savedMem s₀) s₁.mem :=
    h₁.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨(S s₀).setWidth 64, 2064⟩, by simp, Offset.sub_base _ (by decide)⟩
      · exact ⟨VG.Proof.CmacAes.X86.stR s₀, by simp, fun _ h => h⟩
  have f₂ : Frame [VG.Proof.CmacAes.X86.stR s₀, ⟨(S s₀).setWidth 64, 2064⟩, VG.Proof.CmacAes.X86.stkR s₀] (VG.Proof.CmacAes.X86.savedMem s₀) s₂.mem := by
    have fr := h₂.frame
    rw [hb, cA] at fr
    refine f₁.trans (fr.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨⟨(S s₀).setWidth 64, 2064⟩, by simp, Offset.sub_base _ (by decide)⟩
    · exact ⟨VG.Proof.CmacAes.X86.stR s₀, by simp, fun _ h => h⟩
    · exact ⟨⟨(S s₀).setWidth 64, 2064⟩, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨VG.Proof.CmacAes.X86.stkR s₀, by simp, fun _ h => h⟩
  have big₁ := UPre.big_of f₁
  have big₂ := UPre.big_of f₂
  have esp₂ : s₂.gpr .esp = E s₀ := by rw [h₂.saved .esp (by simp [calleeSaved]), h₁.esp]
  have rdwr₂ : s₂.rd ++ s₂.wr = [keyR s₀, lastR s₀, VG.Proof.CmacAes.X86.argsR s₀, VG.Proof.CmacAes.X86.stR s₀, scrR s₀] := by
    rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr, hp.rd, hp.wr]; rfl
  have hrw₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr]
  have sl : ∀ r d, (r, d) ∈ saved → s₂.mem.readW ((S s₀).setWidth 64 + BitVec.ofNat 64 d) 32 = s₀.gpr r := by
    intro r d hrd
    have hb := VG.Proof.CmacAes.X86.saved_bound _ hrd
    rw [f₂.readW (r := ⟨(S s₀).setWidth 64 + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.st_scr.symm.sub_left (UPre.scr_sub (by omega))
      · exact Offset.disjoint_base _ hb.1 (by omega)
      · exact hp.b_scr.symm.sub_left (UPre.scr_sub (by omega))) (by decide), savedMem_slot s₀ hrd]
  have sch : Spec.Aes.bytesAt s₁.mem ((VG.Proof.CmacAes.X86.W s₀).setWidth 64) (16 * (R s₀ + 1)) =
      Spec.Aes.bytesAt s₀.mem ((VG.Proof.CmacAes.X86.W s₀).setWidth 64) (16 * (R s₀ + 1)) :=
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
    exact ⟨scrR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  refine ⟨⟨r₄.abi (by decide) (by decide) (by rw [u₃.other _ (by decide), esp₂]), ?_⟩, ?_⟩
  · rw [r₄.mem, u₃.mem]
    have rs : (VG.Proof.CmacAes.X86.retR s₀).Disjoint (VG.Proof.CmacAes.X86.stkR s₀) := by
      have := Offset.disjoint_below_above ((E s₀).setWidth 64) (m := 28) (a := 0) (l := 4) (by decide)
      rw [add0] at this
      exact this.symm
    exact big₂.readW (r := VG.Proof.CmacAes.X86.retR s₀) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.ret_st
      · exact hp.ret_scr
      · exact rs) (by decide)
  · show Spec.Aes.bytesAt s₄.mem ((St s₀).setWidth 64) 16 = _
    rw [r₄.mem, u₃.mem, h₂.out, sch, cA, h₁.blk]

theorem finalize_raw_correct (v : Ctr32Impl) (s : State) (hs : finalizeRawX86.pre s) :
    ∃ t s', Exec isa (finalize v.callee) s t s' ∧ abiPreserved s s' ∧ finalizeRawX86.post s s' :=
  VG.Proof.AesSiv.X86.finalize_raw_wp v hs

/-- What a call of `vg_cmac_aes_finalize` leaves, from any subkeys. -/
structure FRPost (s : State) (K St P S : BitVec 32) (L R : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨St.setWidth 64, 16⟩, ⟨S.setWidth 64, 2176⟩, below (s.gpr .esp) 56] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem (St.setWidth 64) 16 =
    Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem (K.setWidth 64) (16 * (R + 1)))
      (Spec.Cmac.xor (Spec.Cmac.lastBlock 16 (Spec.Aes.bytesAt s.mem (K.setWidth 64 + BitVec.ofNat 64 240) 16)
          (Spec.Aes.bytesAt s.mem (K.setWidth 64 + BitVec.ofNat 64 256) 16)
          (Spec.Aes.bytesAt s.mem (P.setWidth 64) L))
        (Spec.Aes.bytesAt s.mem (St.setWidth 64) 16))

theorem finr_call (v : Ctr32Impl) {s : State} {K St P S : BitVec 32} {L R : Nat} (h : FArgs s K St P S L R) :
    WP isa (Impl.CmacAes.Stream.X86.call6 ("vg_cmac_aes_finalize" ++ v.suffix) (finalize v.callee)) s
      (VG.Proof.AesSiv.X86.FRPost s K St P S L R) := by
  have hR := VG.Proof.CmacAes.X86.toNat_rounds h.rounds
  have hL : (BitVec.ofNat 32 L).toNat = L := eq_ofNat rfl (by have := h.len; omega)
  have hRb : 16 * (R + 1) ≤ 272 := by rcases h.rounds with h | h | h <;> omega
  have he := h.esp
  refine WP.callWith (rs := rs6) (k := VG.Proof.AesSiv.X86.finalizeRawX86) (fun _ hs => VG.Proof.AesSiv.X86.finalize_raw_wp v hs) (fin_nosp v) (by simp)
    hrs6 (by rw [(fin_stack v)]; simp only [List.length_cons, List.length_nil]; omega)
    ⟨h.callPre.pre, h.callPre.cov, h.callPre.covw⟩
    fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  obtain ⟨a0, a1, a2, a3, a4, -⟩ := h.args
  rw [(fin_stack v)] at f'
  refine ⟨rd', wr', cs', f'.mono fun r hr => by simpa using hr, ?_⟩
  have keep : ∀ {p : Addr} {k : Nat}, (below (s.gpr .esp) 56).Disjoint ⟨p, k⟩ → k ≤ 2 ^ 64 →
      Spec.Aes.bytesAt (pushed rs6 s).callEntry.mem p k = Spec.Aes.bytesAt s.mem p k :=
    fun hd hk => entry_bytes h.fit hrs6 (by simp) he hd hk
  simp only [VG.Proof.AesSiv.X86.finalizeRawX86, mn, VG.Proof.CmacAes.X86.W, Dp, N, arg_withRegions, State.withRegions_mem, a0, a1, a2, a3, a4, hR, hL,
    m₂] at post
  have eK := keep (h.bK.sub_right (Region.sub_prefix hRb)) (by omega)
  have eK1 := keep (p := K.setWidth 64 + BitVec.ofNat 64 240) (k := 16)
    (h.bK.sub_right (Offset.sub_base (K.setWidth 64) (d := 240) (n := 16) (by decide))) (by decide)
  have eK2 := keep (p := K.setWidth 64 + BitVec.ofNat 64 256) (k := 16)
    (h.bK.sub_right (Offset.sub_base (K.setWidth 64) (d := 256) (n := 16) (by decide))) (by decide)
  have eSt := keep h.bSt (by decide)
  have eP := keep h.bP (by omega)
  rw [eK, eK1, eK2, eSt, eP] at post
  exact post

end VG.Proof.AesSiv.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.X86.Callee`. -/
section

/-!
# AES-SIV on x86: the functions called

Untrusted: everything here is checked by Lean. The calls of
`vg_cmac_aes_update` are those of streaming AES-CMAC
(`Proof.CmacAes.Stream.X86.upd_call`), those of `vg_cmac_aes_finalize` from
any subkeys (`finr_call`), and those of `vg_aes_ctr32` those of AES-GCM
(`Proof.AesGcm.X86.ctr_call`), with `ebp` moved to the working space around
them (`ctrCall_ok`). Their arguments are built from the environment: the key
context, a block of `W` as the state or the counter block, the data or
blocks of `W` as the data (`Src`), and the working space at `W + 256`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesSiv.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (blockAt blocksAt ctr32 aesWith)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (imm)
open VG.Proof.AesGcm.X86 (w64 toNat_ofNat32 toNat_add32 w64_add covers_left covers_cons covers_nil CtrCall CtrPost
  GcmImpl gpr_setMem CT)
open VG.Proof.CmacAes.Stream.X86 (UArgs UPost FArgs)

theorem below_sub56 {SP : BitVec 32} {k : Nat} (hk : k ≤ 56) (hs : 56 ≤ SP.toNat) :
    Region.Sub (below SP k) (below SP 56) :=
  VG.X86.below_sub hk hs

/-- Where a state may be in `W`: below the working space of the functions
called, or above it (`D`). -/
abbrev StOk (y : Nat) : Prop := y + 16 ≤ 256 ∨ (2432 ≤ y ∧ y + 16 ≤ 2576)

theorem stOk_scr {W : BitVec 32} {y : Nat} (h : VG.Proof.AesSiv.X86.StOk y) :
    (⟨w64 W + BitVec.ofNat 64 y, 16⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 256, 2176⟩ := by
  rcases h with h | h
  · exact Lay.w_w (.inl h) (by omega) (by decide)
  · exact Lay.w_w (.inr (by omega)) (by omega) (by decide)

/-! ## Data for a call -/

/-- `k` bytes at `Q`, which the code may read, apart from the working space
of the functions called and the stack below `SP`. -/
structure Src (W SP : BitVec 32) (s : State) (Q : BitVec 32) (k : Nat) : Prop where
  rd : Covers [⟨w64 Q, k⟩] (s.rd ++ s.wr)
  wrap : Q.toNat + k ≤ 2 ^ 32
  qs : (⟨w64 Q, k⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 256, 2176⟩
  stk : (below SP 56).Disjoint ⟨w64 Q, k⟩

/-- Bytes of `W` below 256 as data. -/
theorem srcW {C W SP : BitVec 32} {s : State} (L : VG.Proof.AesSiv.X86.Lay C W SP) (P : VG.Proof.AesSiv.X86.Perm C W s) {t k : Nat} (hk : t + k ≤ 256) :
    VG.Proof.AesSiv.X86.Src W SP s (W + BitVec.ofNat 32 t) k where
  rd := by rw [L.aW (o := t) (by omega)]; exact covers_left (P.wC (by omega))
  wrap := by rw [L.nW (o := t) (by omega)]; have := L.fw; omega
  qs := by rw [L.aW (o := t) (by omega)]; exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  stk := by rw [L.aW (o := t) (by omega)]; exact L.stk_w' (by omega)

/-- A buffer as data. -/
theorem srcBuf {W SP : BitVec 32} {s : State} {Q : BitVec 32} {k : Nat} (h : VG.Proof.AesSiv.X86.Buf W SP s Q k) : VG.Proof.AesSiv.X86.Src W SP s Q k :=
  ⟨h.rd, h.wrap, h.w.sub_right (Lay.wSub (by decide)), h.stk⟩

theorem Src.of_eq {W SP : BitVec 32} {s s' : State} {Q : BitVec 32} {k : Nat} (h : VG.Proof.AesSiv.X86.Src W SP s Q k)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesSiv.X86.Src W SP s' Q k :=
  { h with rd := by rw [hrd, hwr]; exact h.rd }

theorem Src.take {W SP : BitVec 32} {s : State} {Q : BitVec 32} {k j : Nat} (h : VG.Proof.AesSiv.X86.Src W SP s Q k) (hj : j ≤ k) :
    VG.Proof.AesSiv.X86.Src W SP s Q j where
  rd := fun a m ⟨r, hr, hc⟩ => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.rd a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩
  wrap := by have := h.wrap; omega
  qs := h.qs.sub_left (Region.sub_prefix hj)
  stk := h.stk.sub_right (Region.sub_prefix hj)

/-! ## `vg_cmac_aes_update` -/

/-- The arguments of `vg_cmac_aes_update`: `K1`'s schedule, the state at
`W + y`, `n` blocks at `Q`, and the working space at `W + 256`. -/
theorem uargs {C W SP : BitVec 32} {s : State} (L : VG.Proof.AesSiv.X86.Lay C W SP) (E : VG.Proof.AesSiv.X86.Env C W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {y : Nat} (hy : VG.Proof.AesSiv.X86.StOk y) {Q : BitVec 32} {n : Nat}
    (hq : VG.Proof.AesSiv.X86.Src W SP s Q (16 * n)) (hqy : (⟨w64 Q, 16 * n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 y, 16⟩)
    (hn : 16 * n < 2 ^ 32) (eax : s.gpr .eax = C) (ecx : s.gpr .ecx = BitVec.ofNat 32 R)
    (edx : s.gpr .edx = W + BitVec.ofNat 32 y) (ebx : s.gpr .ebx = Q) (esi : s.gpr .esi = BitVec.ofNat 32 n)
    (edi : s.gpr .edi = W + BitVec.ofNat 32 256) :
    UArgs s C (W + BitVec.ofNat 32 y) Q (W + BitVec.ofNat 32 256) R n where
  eax := eax
  ecx := ecx
  edx := edx
  ebx := ebx
  esi := esi
  edi := edi
  rounds := hR
  esp := by rw [E.esp]; exact L.sp
  hn := hn
  wc := by
    rw [L.sW (o := y) (by omega)]
    simpa using L.c_w' (a := 0) (n := 240) (d := y) (k := 16) (by decide) (by omega)
  ws := by rw [L.sW (o := 256) (by omega)]; simpa using L.c_w' (a := 0) (n := 240) (d := 256) (k := 2176) (by decide) (by decide)
  dc := by rw [L.sW (o := y) (by omega)]; exact hqy
  ds := by rw [L.sW (o := 256) (by omega)]; exact hq.qs
  cs := by rw [L.sW (o := y) (by omega), L.sW (o := 256) (by omega)]; exact VG.Proof.AesSiv.X86.stOk_scr hy
  bW := by rw [E.esp]; simpa using L.stk_c' (a := 0) (n := 240) (by decide)
  bD := by rw [E.esp]; exact hq.stk
  bC := by rw [E.esp, L.sW (o := y) (by omega)]; exact L.stk_w' (by omega)
  bS := by rw [E.esp, L.sW (o := 256) (by omega)]; exact L.stk_w' (by decide)
  fW := by have := L.fc; omega
  fC := by rw [L.nW (o := y) (by omega)]; have := L.fw; omega
  fD := hq.wrap
  fS := by rw [L.nW (o := 256) (by omega)]; have := L.fw; omega
  reads := by
    refine covers_cons ?_ (covers_cons hq.rd covers_nil)
    simpa using E.perm.cC (d := 0) (n := 240) (by decide)
  writes := by
    rw [L.sW (o := y) (by omega), L.sW (o := 256) (by omega)]
    exact covers_cons (E.perm.wC (by omega)) (covers_cons (E.perm.wC (by decide)) covers_nil)

/-- A call of `vg_cmac_aes_update`, with its arguments (`uargs`). -/
theorem updCall_ok (v : Ctr32Impl) {C W SP : BitVec 32} {s : State} (L : VG.Proof.AesSiv.X86.Lay C W SP) (E : VG.Proof.AesSiv.X86.Env C W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {y : Nat} (hy : VG.Proof.AesSiv.X86.StOk y) {Q : BitVec 32} {n : Nat}
    (hq : VG.Proof.AesSiv.X86.Src W SP s Q (16 * n)) (hqy : (⟨w64 Q, 16 * n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 y, 16⟩)
    (hn : 16 * n < 2 ^ 32) (eax : s.gpr .eax = C) (ecx : s.gpr .ecx = BitVec.ofNat 32 R)
    (edx : s.gpr .edx = W + BitVec.ofNat 32 y) (ebx : s.gpr .ebx = Q) (esi : s.gpr .esi = BitVec.ofNat 32 n)
    (edi : s.gpr .edi = W + BitVec.ofNat 32 256) :
    WP isa (updCall v.callee v.suffix) s fun s' => VG.Proof.AesSiv.X86.Env C W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      Frame [⟨w64 W + BitVec.ofNat 64 y, 16⟩, ⟨w64 W + BitVec.ofNat 64 256, 2176⟩, below SP 56] s.mem s'.mem ∧
      bytesAt s'.mem (w64 W + BitVec.ofNat 64 y) 16 =
        Spec.Cmac.chain (Spec.Cmac.aesWith R (bytesAt s.mem (w64 C) (16 * (R + 1))))
          (bytesAt s.mem (w64 W + BitVec.ofNat 64 y) 16) (Spec.Cmac.blocksAt s.mem (w64 Q) 16 n) := by
  refine WP.mono (Proof.CmacAes.Stream.X86.upd_call v (VG.Proof.AesSiv.X86.uargs L E hR hy hq hqy hn eax ecx edx ebx esi edi))
    fun s' h => ⟨E.keep (h.saved _ (by decide)) (h.saved _ (by decide)) h.rd h.wr, h.rd, h.wr, h.saved, ?_, ?_⟩
  · have f := h.frame
    rw [L.sW (o := y) (by omega), L.sW (o := 256) (by omega), E.esp] at f
    exact f
  · have o := h.out
    rw [L.sW (o := y) (by omega)] at o
    exact o

/-- Calls of `vg_cmac_aes_update` with the same arguments are constant time. -/
theorem updCall_ct (v : Ctr32Impl) {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {y : Nat} (hy : VG.Proof.AesSiv.X86.StOk y) {Q : BitVec 32} {n : Nat} (hn : 16 * n < 2 ^ 32) {I : State → Prop}
    (hI : ∀ s, I s → VG.Proof.AesSiv.X86.Env C W SP s ∧ VG.Proof.AesSiv.X86.Src W SP s Q (16 * n) ∧
      (⟨w64 Q, 16 * n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 y, 16⟩ ∧ s.gpr .eax = C ∧
      s.gpr .ecx = BitVec.ofNat 32 R ∧ s.gpr .edx = W + BitVec.ofNat 32 y ∧ s.gpr .ebx = Q ∧
      s.gpr .esi = BitVec.ofNat 32 n ∧ s.gpr .edi = W + BitVec.ofNat 32 256) :
    CT I (updCall v.callee v.suffix) :=
  Proof.CmacAes.Stream.X86.upd_rel v (E := SP) fun s₁ s₂ ⟨h₁, h₂⟩ => by
    obtain ⟨E₁, q₁, y₁, a₁, c₁, d₁, b₁, i₁, j₁⟩ := hI s₁ h₁
    obtain ⟨E₂, q₂, y₂, a₂, c₂, d₂, b₂, i₂, j₂⟩ := hI s₂ h₂
    exact ⟨VG.Proof.AesSiv.X86.uargs L E₁ hR hy q₁ y₁ hn a₁ c₁ d₁ b₁ i₁ j₁, VG.Proof.AesSiv.X86.uargs L E₂ hR hy q₂ y₂ hn a₂ c₂ d₂ b₂ i₂ j₂, E₁.esp, E₂.esp⟩

/-! ## `vg_cmac_aes_finalize` -/

/-- The arguments of `vg_cmac_aes_finalize`: the key context (`K1`'s
schedule and its subkeys), the state at `W + y`, the last `l ≤ 16` bytes at
`P`, and the working space at `W + 256`. -/
theorem fargs {C W SP : BitVec 32} {s : State} (L : VG.Proof.AesSiv.X86.Lay C W SP) (E : VG.Proof.AesSiv.X86.Env C W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {y : Nat} (hy : VG.Proof.AesSiv.X86.StOk y) {P : BitVec 32} {l : Nat} (hl : l ≤ 16)
    (hp : VG.Proof.AesSiv.X86.Src W SP s P l) (hpy : (⟨w64 P, l⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 y, 16⟩)
    (eax : s.gpr .eax = C) (ecx : s.gpr .ecx = BitVec.ofNat 32 R)
    (edx : s.gpr .edx = W + BitVec.ofNat 32 y) (ebx : s.gpr .ebx = P) (esi : s.gpr .esi = BitVec.ofNat 32 l)
    (edi : s.gpr .edi = W + BitVec.ofNat 32 256) :
    FArgs s C (W + BitVec.ofNat 32 y) P (W + BitVec.ofNat 32 256) l R where
  eax := eax
  ecx := ecx
  edx := edx
  ebx := ebx
  esi := esi
  edi := edi
  rounds := hR
  len := hl
  esp := by rw [E.esp]; exact L.sp
  kst := by
    rw [L.sW (o := y) (by omega)]
    simpa using L.c_w' (a := 0) (n := 272) (d := y) (k := 16) (by decide) (by omega)
  ks := by rw [L.sW (o := 256) (by omega)]; simpa using L.c_w' (a := 0) (n := 272) (d := 256) (k := 2176) (by decide) (by decide)
  pst := by rw [L.sW (o := y) (by omega)]; exact hpy
  ps := by rw [L.sW (o := 256) (by omega)]; exact hp.qs
  sts := by rw [L.sW (o := y) (by omega), L.sW (o := 256) (by omega)]; exact VG.Proof.AesSiv.X86.stOk_scr hy
  bK := by rw [E.esp]; simpa using L.stk_c' (a := 0) (n := 272) (by decide)
  bP := by rw [E.esp]; exact hp.stk
  bSt := by rw [E.esp, L.sW (o := y) (by omega)]; exact L.stk_w' (by omega)
  bS := by rw [E.esp, L.sW (o := 256) (by omega)]; exact L.stk_w' (by decide)
  fK := by have := L.fc; omega
  fSt := by rw [L.nW (o := y) (by omega)]; have := L.fw; omega
  fP := hp.wrap
  fS := by rw [L.nW (o := 256) (by omega)]; have := L.fw; omega
  reads := by
    refine covers_cons ?_ (covers_cons hp.rd covers_nil)
    simpa using E.perm.cC (d := 0) (n := 272) (by decide)
  writes := by
    rw [L.sW (o := y) (by omega), L.sW (o := 256) (by omega)]
    exact covers_cons (E.perm.wC (by omega)) (covers_cons (E.perm.wC (by decide)) covers_nil)

/-- A call of `vg_cmac_aes_finalize`, with its arguments (`fargs`): the state
becomes `CIPH_K1(C ⊕ Mₙ)` for the last block `Mₙ` made with the context's
subkeys. -/
theorem finCall_ok (v : Ctr32Impl) {C W SP : BitVec 32} {s : State} (L : VG.Proof.AesSiv.X86.Lay C W SP) (E : VG.Proof.AesSiv.X86.Env C W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {y : Nat} (hy : VG.Proof.AesSiv.X86.StOk y) {P : BitVec 32} {l : Nat} (hl : l ≤ 16)
    (hp : VG.Proof.AesSiv.X86.Src W SP s P l) (hpy : (⟨w64 P, l⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 y, 16⟩)
    (eax : s.gpr .eax = C) (ecx : s.gpr .ecx = BitVec.ofNat 32 R)
    (edx : s.gpr .edx = W + BitVec.ofNat 32 y) (ebx : s.gpr .ebx = P) (esi : s.gpr .esi = BitVec.ofNat 32 l)
    (edi : s.gpr .edi = W + BitVec.ofNat 32 256) :
    WP isa (finCall v.callee v.suffix) s fun s' => VG.Proof.AesSiv.X86.Env C W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      Frame [⟨w64 W + BitVec.ofNat 64 y, 16⟩, ⟨w64 W + BitVec.ofNat 64 256, 2176⟩, below SP 56] s.mem s'.mem ∧
      bytesAt s'.mem (w64 W + BitVec.ofNat 64 y) 16 =
        Spec.Cmac.aesWith R (bytesAt s.mem (w64 C) (16 * (R + 1)))
          (Spec.Cmac.xor (Spec.Cmac.lastBlock 16 (bytesAt s.mem (w64 C + BitVec.ofNat 64 240) 16)
              (bytesAt s.mem (w64 C + BitVec.ofNat 64 256) 16) (bytesAt s.mem (w64 P) l))
            (bytesAt s.mem (w64 W + BitVec.ofNat 64 y) 16)) := by
  refine WP.mono (VG.Proof.AesSiv.X86.finr_call v (VG.Proof.AesSiv.X86.fargs L E hR hy hl hp hpy eax ecx edx ebx esi edi))
    fun s' h => ⟨E.keep (h.saved _ (by decide)) (h.saved _ (by decide)) h.rd h.wr, h.rd, h.wr, h.saved, ?_, ?_⟩
  · have f := h.frame
    rw [L.sW (o := y) (by omega), L.sW (o := 256) (by omega), E.esp] at f
    exact f
  · have o := h.out
    rw [L.sW (o := y) (by omega)] at o
    exact o

/-- Calls of `vg_cmac_aes_finalize` with the same arguments are constant time. -/
theorem finCall_ct (v : Ctr32Impl) {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {y : Nat} (hy : VG.Proof.AesSiv.X86.StOk y) {P : BitVec 32} {l : Nat} (hl : l ≤ 16) {I : State → Prop}
    (hI : ∀ s, I s → VG.Proof.AesSiv.X86.Env C W SP s ∧ VG.Proof.AesSiv.X86.Src W SP s P l ∧
      (⟨w64 P, l⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 y, 16⟩ ∧ s.gpr .eax = C ∧
      s.gpr .ecx = BitVec.ofNat 32 R ∧ s.gpr .edx = W + BitVec.ofNat 32 y ∧ s.gpr .ebx = P ∧
      s.gpr .esi = BitVec.ofNat 32 l ∧ s.gpr .edi = W + BitVec.ofNat 32 256) :
    CT I (finCall v.callee v.suffix) :=
  Proof.CmacAes.Stream.X86.fin_rel v (E := SP) fun s₁ s₂ ⟨h₁, h₂⟩ => by
    obtain ⟨E₁, q₁, y₁, a₁, c₁, d₁, b₁, i₁, j₁⟩ := hI s₁ h₁
    obtain ⟨E₂, q₂, y₂, a₂, c₂, d₂, b₂, i₂, j₂⟩ := hI s₂ h₂
    exact ⟨VG.Proof.AesSiv.X86.fargs L E₁ hR hy hl q₁ y₁ a₁ c₁ d₁ b₁ i₁ j₁, VG.Proof.AesSiv.X86.fargs L E₂ hR hy hl q₂ y₂ a₂ c₂ d₂ b₂ i₂ j₂, E₁.esp, E₂.esp⟩

/-! ## `vg_aes_ctr32` -/

/-- The frame and call of `vg_aes_ctr32`: AES-GCM's, with any implementation
of `vg_aes_ghash` beside it. -/
theorem ctrFrame_ok (v : Ctr32Impl) {s : State} {K C D S : BitVec 32} {R n : Nat} (h : CtrCall s K C D S R n) :
    WP isa (.frame (.push [.ebp, .edi, .ebx, .edx, .ecx, .eax]) (.call v.callee.name v.callee.code) (.pop .eax 6)) s
      (CtrPost s K C D S R n) :=
  Proof.AesGcm.X86.ctr_call ⟨v, .scalar⟩ h

/-- `k` bytes at `D` that `vg_aes_ctr32` may write: apart from the key
context, the counter block at `W + c`, the working space of the functions
called and the stack below `SP`. -/
structure Dst (C W SP : BitVec 32) (s : State) (D : BitVec 32) (k c : Nat) : Prop where
  wr : Covers [⟨w64 D, k⟩] s.wr
  wrap : D.toNat + k ≤ 2 ^ 32
  dk : (⟨w64 C, 512⟩ : Region).Disjoint ⟨w64 D, k⟩
  dc : (⟨w64 D, k⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 c, 16⟩
  ds : (⟨w64 D, k⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 256, 2048⟩
  stk : (below SP 56).Disjoint ⟨w64 D, k⟩

theorem Dst.of_eq {C W SP : BitVec 32} {s s' : State} {D : BitVec 32} {k c : Nat} (h : VG.Proof.AesSiv.X86.Dst C W SP s D k c)
    (hwr : s'.wr = s.wr) : VG.Proof.AesSiv.X86.Dst C W SP s' D k c :=
  { h with wr := by rw [hwr]; exact h.wr }

/-- A block of `W` below 256 as `vg_aes_ctr32`'s data. -/
theorem dstW {C W SP : BitVec 32} {s : State} (L : VG.Proof.AesSiv.X86.Lay C W SP) (P : VG.Proof.AesSiv.X86.Perm C W s) {c q : Nat} (hc : c + 16 ≤ 256)
    (hq : q + 16 ≤ 256) (hqc : q + 16 ≤ c ∨ c + 16 ≤ q) : VG.Proof.AesSiv.X86.Dst C W SP s (W + BitVec.ofNat 32 q) 16 c where
  wr := by rw [L.aW (o := q) (by omega)]; exact P.wC (by omega)
  wrap := by rw [L.nW (o := q) (by omega)]; have := L.fw; omega
  dk := by rw [L.aW (o := q) (by omega)]; exact L.c_w.sub_right (Lay.wSub (by omega))
  dc := by rw [L.aW (o := q) (by omega)]; exact Lay.w_w hqc (by omega) (by omega)
  ds := by rw [L.aW (o := q) (by omega)]; exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  stk := by rw [L.aW (o := q) (by omega)]; exact L.stk_w' (by omega)

/-- The arguments of `vg_aes_ctr32`: `K2`'s schedule at `C + 272`, the
counter block at `W + c`, `n` blocks at `D`, and the working space at
`W + 256` (where `ebp` is moved). -/
theorem cargs {C W SP : BitVec 32} {s : State} (L : VG.Proof.AesSiv.X86.Lay C W SP) (P : VG.Proof.AesSiv.X86.Perm C W s) (esp : s.gpr .esp = SP) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {c : Nat} (hc : c + 16 ≤ 256) {D : BitVec 32} {n : Nat}
    (hD : VG.Proof.AesSiv.X86.Dst C W SP s D (16 * n) c) (eax : s.gpr .eax = C + BitVec.ofNat 32 272)
    (ecx : s.gpr .ecx = BitVec.ofNat 32 R) (edx : s.gpr .edx = W + BitVec.ofNat 32 c)
    (ebx : s.gpr .ebx = D) (edi : s.gpr .edi = BitVec.ofNat 32 n)
    (ebp : s.gpr .ebp = W + BitVec.ofNat 32 256) :
    CtrCall s (C + BitVec.ofNat 32 272) (W + BitVec.ofNat 32 c) D (W + BitVec.ofNat 32 256) R n := by
  have hsp := L.sp
  have b28 : Region.Sub (below SP 28) (below SP 56) := VG.Proof.AesSiv.X86.below_sub56 (by decide) hsp
  refine ⟨eax, ecx, edx, ebx, edi, ebp, hR, by rw [esp]; omega, ?_, ?_, ?_, ?_, ?_, hD.ds.sub_right ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, hD.wrap, ?_, ?_, ?_⟩
  · rw [L.aC (o := 272) (by omega), L.aW (o := c) (by omega)]; exact L.c_w' (by decide) (by omega)
  · rw [L.aC (o := 272) (by omega)]; exact hD.dk.sub_left (Lay.cSub (by decide))
  · rw [L.aC (o := 272) (by omega), L.aW (o := 256) (by omega)]; exact L.c_w' (by decide) (by decide)
  · rw [L.aW (o := c) (by omega)]; exact hD.dc.symm
  · rw [L.aW (o := c) (by omega), L.aW (o := 256) (by omega)]
    exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  · rw [L.aW (o := 256) (by omega)]; exact fun _ h => h
  · rw [esp, L.aC (o := 272) (by omega)]; exact (L.stk_c' (by decide)).sub_left b28
  · rw [esp, L.aW (o := c) (by omega)]; exact (L.stk_w' (by omega)).sub_left b28
  · rw [esp]; exact hD.stk.sub_left b28
  · rw [esp, L.aW (o := 256) (by omega)]; exact (L.stk_w' (by decide)).sub_left b28
  · rw [L.nC (o := 272) (by omega)]; have := L.fc; omega
  · rw [L.nW (o := c) (by omega)]; have := L.fw; omega
  · rw [L.nW (o := 256) (by omega)]; have := L.fw; omega
  · rw [L.aC (o := 272) (by omega)]; exact P.cC (by decide)
  · rw [L.aW (o := c) (by omega), L.aW (o := 256) (by omega)]
    exact covers_cons (P.wC (by omega)) (covers_cons hD.wr (covers_cons (P.wC (by decide)) covers_nil))

/-- A call of `vg_aes_ctr32` on `n` blocks at `D`, from the counter block at
`W + c`, under `K2`. -/
theorem ctrCall_ok (v : Ctr32Impl) {C W SP : BitVec 32} {s : State} (L : VG.Proof.AesSiv.X86.Lay C W SP) (E : VG.Proof.AesSiv.X86.Env C W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {c : Nat} (hc : c + 16 ≤ 256) {D : BitVec 32} {n : Nat}
    (hD : VG.Proof.AesSiv.X86.Dst C W SP s D (16 * n) c) (eax : s.gpr .eax = C + BitVec.ofNat 32 272)
    (ecx : s.gpr .ecx = BitVec.ofNat 32 R) (edx : s.gpr .edx = W + BitVec.ofNat 32 c)
    (ebx : s.gpr .ebx = D) (edi : s.gpr .edi = BitVec.ofNat 32 n) :
    WP isa (ctrCall v.callee) s fun s' => VG.Proof.AesSiv.X86.Env C W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ [Reg.ebx, .esi, .edi], s'.gpr r = s.gpr r) ∧
      Frame [⟨w64 W + BitVec.ofNat 64 c, 16⟩, ⟨w64 D, 16 * n⟩,
        ⟨w64 W + BitVec.ofNat 64 256, 2048⟩, below SP 56] s.mem s'.mem ∧
      blocksAt s'.mem (w64 D) n =
        ctr32 (VG.Spec.Gcm.aesWith R (bytesAt s.mem (w64 C + BitVec.ofNat 64 272) (16 * (R + 1))))
          (blockAt s.mem (w64 W + BitVec.ofNat 64 c)) (blocksAt s.mem (w64 D) n) ∧
      blockAt s'.mem (w64 W + BitVec.ofNat 64 c) =
        Nat.repeat Spec.Gcm.inc32 n (blockAt s.mem (w64 W + BitVec.ofNat 64 c)) := by
  have hsp := L.sp
  have b28 : Region.Sub (below SP 28) (below SP 56) := VG.Proof.AesSiv.X86.below_sub56 (by decide) hsp
  -- `ebp := W + 256`.
  refine WP.seq (WP.of_runBlock ⟨_, by crun [], ?_⟩)
  -- The call.
  have e256 : s.gpr .ebp + BitVec.ofNat 32 256 = W + BitVec.ofNat 32 256 := by rw [E.ebp]
  refine WP.seq (WP.mono (VG.Proof.AesSiv.X86.ctrFrame_ok v (VG.Proof.AesSiv.X86.cargs L (E.perm.of_eq (by cmems []) (by cmems [])) (by cregs [E.esp]) hR hc
    (hD.of_eq (by cmems [])) (by cregs [eax]) (by cregs [ecx]) (by cregs [edx]) (by cregs [ebx]) (by cregs [edi])
    (by cregs [e256]))) fun s₂ P => ?_)
  -- `ebp := W`.
  have hbp₂ : s₂.gpr .ebp = W + BitVec.ofNat 32 256 := by
    rw [P.saved _ (by decide)]; cregs [E.ebp]
  have hsp₂ : s₂.gpr .esp = SP := by rw [P.saved _ (by decide)]; cregs [E.esp]
  refine WP.of_runBlock ⟨_, by crun [hbp₂], ?_⟩
  refine ⟨⟨by cregs [hbp₂]; exact BitVec.add_sub_cancel _ _, by cregs [hsp₂],
    E.perm.of_eq (by cmems [P.rd]) (by cmems [P.wr])⟩, by cmems [P.rd], by cmems [P.wr], ?_, ?_, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> (cregs []; rw [P.saved _ (by decide)]; cregs [])
  · have f := P.frame
    rw [L.aW (o := c) (by omega), L.aW (o := 256) (by omega)] at f
    cmems []
    refine f.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · refine ⟨below SP 56, by simp, ?_⟩
      simpa [gpr_setReg_of_ne, E.esp] using b28
  · have o := P.out
    rw [L.aW (o := c) (by omega), L.aC (o := 272) (by omega)] at o
    cmems []
    exact o
  · have o := P.ctr
    rw [L.aW (o := c) (by omega)] at o
    cmems []
    exact o

/-- Calls of `vg_aes_ctr32` with the same arguments are constant time. -/
theorem ctrCall_ct (v : Ctr32Impl) {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {c : Nat} (hc : c + 16 ≤ 256) {D : BitVec 32} {n : Nat} {I : State → Prop}
    (hI : ∀ s, I s → VG.Proof.AesSiv.X86.Env C W SP s ∧ VG.Proof.AesSiv.X86.Dst C W SP s D (16 * n) c ∧ s.gpr .eax = C + BitVec.ofNat 32 272 ∧
      s.gpr .ecx = BitVec.ofNat 32 R ∧ s.gpr .edx = W + BitVec.ofNat 32 c ∧ s.gpr .ebx = D ∧
      s.gpr .edi = BitVec.ofNat 32 n) :
    CT I (ctrCall v.callee) := by
  -- The state after `ebp := W + 256`, as `CtrCall` needs it.
  have call : ∀ s, I s → ∀ s', runBlock isa [.alu .add .ebp (imm csOff)] s = some s' →
      CtrCall s' (C + BitVec.ofNat 32 272) (W + BitVec.ofNat 32 c) D (W + BitVec.ofNat 32 256) R n ∧
        s'.gpr .esp = SP := by
    intro s hs s' run
    obtain ⟨E, hD, eax, ecx, edx, ebx, edi⟩ := hI s hs
    have e := run
    simp (disch := first | decide | omega) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
      imm, csOff, Option.bind_some, Option.some.injEq] at e
    subst e
    have e256 : s.gpr .ebp + BitVec.ofNat 32 256 = W + BitVec.ofNat 32 256 := by rw [E.ebp]
    exact ⟨VG.Proof.AesSiv.X86.cargs L (E.perm.of_eq (by cmems []) (by cmems [])) (by cregs [E.esp]) hR hc (hD.of_eq (by cmems []))
      (by cregs [eax]) (by cregs [ecx]) (by cregs [edx]) (by cregs [ebx]) (by cregs [edi]) (by cregs [e256]),
      by cregs [E.esp]⟩
  refine CT.seq (J := fun s' => ∃ s, I s ∧ runBlock isa [.alu .add .ebp (imm csOff)] s = some s')
    (CT.taint [.ebp] (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [(hI _ h₁).1.ebp, (hI _ h₂).1.ebp]) (by taint_decide))
    (fun s hs => WP.of_runBlock ⟨_, by crun [], s, hs, by crun []⟩) ?_
  refine CT.seq (J := fun s => s.gpr .ebp = W + BitVec.ofNat 32 256)
    ((Proof.AesGcm.X86.ctr_ct ⟨v, .scalar⟩ (E := SP) fun s ⟨s₀, h₀, run⟩ => call s₀ h₀ s run :
      CT _ (.frame (.push [.ebp, .edi, .ebx, .edx, .ecx, .eax]) (.call v.callee.name v.callee.code) (.pop .eax 6))))
    (fun s ⟨s₀, h₀, run⟩ => WP.mono (VG.Proof.AesSiv.X86.ctrFrame_ok v (call s₀ h₀ s run).1) fun s₁ g => by
      rw [g.saved .ebp (by decide), (call s₀ h₀ s run).1.ebp]) ?_
  exact CT.taint [.ebp] (fun s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁, h₂]) (by taint_decide)

end VG.Proof.AesSiv.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.X86.Entry`. -/
section

/-!
# AES-SIV on x86: the entry of `encrypt` and `decrypt`

Untrusted: everything here is checked by Lean. The entry (`entry_ok`) saves
our caller's registers in `W` (AES-GCM's `save_ok`), copies the stack
arguments into their slots (`keeps_ok`): the slots (`Slots`) hold the
arguments. The exit is AES-GCM's (`exit_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesSiv.X86
open VG.Impl.AesGcm.X86 (at_ imm slot argOp keep entry saveAt)
open VG.Proof.AesGcm.X86 (w64 slotv argA argsR argA_contains argA_sub SavedAt save_ok KeepEnv keeps_ok keepR
  runBlock_app_of in_off)

/-- The arguments the entry copies, and where. -/
abbrev entryPs : List (Nat × Nat) :=
  [(0, ctxO), (1, roundsO), (2, adsO), (3, leftO), (4, dataO), (5, lenO)]

theorem sivEntry_eq : sivEntry = entry 7 (entryPs.flatMap (fun p => keep p.1 p.2)) := rfl

/-- What the entry leaves. -/
structure Entered (s : State) (W : BitVec 32) (s' : State) : Prop where
  ebp : s'.gpr .ebp = W
  esp : s'.gpr .esp = s.gpr .esp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : SavedAt s'.mem W s
  slots : ∀ p ∈ VG.Proof.AesSiv.X86.entryPs, slotv s'.mem W p.2 = VG.X86.arg s p.1
  frame : Frame [⟨w64 W + BitVec.ofNat 64 128, 2432⟩] s.mem s'.mem

/-- The entry, from `W` (the stack argument 7). -/
theorem entry_ok {s : State} {W : BitVec 32} (hW : arg s 7 = W) (wW : Covers [⟨w64 W, 2560⟩] s.wr)
    (rA : Covers [argsR (s.gpr .esp) 8] (s.rd ++ s.wr)) (aw : (argsR (s.gpr .esp) 8).Disjoint ⟨w64 W, 2560⟩)
    (fa : (s.gpr .esp).toNat + 4 + 4 * 8 ≤ 2 ^ 32) (fw : W.toNat + 2560 ≤ 2 ^ 32) :
    WP isa sivEntry s (Entered s W) := by
  rw [sivEntry_eq]
  generalize hSP : s.gpr .esp = SP at rA aw fa
  have i₀ : InRegions (s.rd ++ s.wr) (argA SP 7) 4 := rA _ _ ⟨_, List.mem_singleton_self _, argA_contains (by decide) fa⟩
  refine WP.seq (WP.of_runBlock ⟨_, by crun [hSP, i₀], ?_⟩)
  have hax : (s.setReg .eax (s.mem.readW (argA SP 7) 32)).gpr .eax = W := by
    rw [gpr_setReg_self, ← hSP]; exact hW
  set s₀ := s.setReg .eax (s.mem.readW (argA SP 7) 32) with hs₀
  obtain ⟨s₁, run₁, bp₁, g₁, rd₁, wr₁, sv₁, f₁⟩ := save_ok s₀ hax (by rw [hs₀]; exact wW) fw
  have sp₁ : s₁.gpr .esp = SP := by rw [g₁ _ (by decide), hs₀, gpr_setReg_of_ne _ _ (by decide), hSP]
  have f₁' : Frame [⟨w64 W + BitVec.ofNat 64 128, 16⟩] s.mem s₁.mem := f₁
  have argW : ∀ {i}, i < 8 → ∀ {d k : Nat}, d + k ≤ 2560 → ∀ r ∈ [(⟨w64 W + BitVec.ofNat 64 d, k⟩ : Region)],
      (⟨argA SP i, 4⟩ : Region).Disjoint r := fun hi _ _ hk r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (aw.sub_left (argA_sub hi fa)).sub_right (Offset.sub_base _ hk)
  have hA₁ : ∀ i < 8, s₁.mem.readW (argA SP i) 32 = arg s i := fun i hi => by
    rw [f₁'.readW (r := ⟨argA SP i, 4⟩) (Region.contains_self _ _) (argW hi (by decide)) (by decide)]
    rw [arg, argAddr, hSP]
  have ke : KeepEnv W SP 8 s₁ := ⟨bp₁, sp₁, by rw [wr₁]; exact wW, by rw [rd₁, wr₁]; exact rA, aw, fa, fw⟩
  obtain ⟨s₃, run₃, sl₃, f₃, g₃, rd₃, wr₃⟩ := keeps_ok entryPs (fun p hp => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide) (by decide) ke
  have bp₃ : s₃.gpr .ebp = W := by rw [g₃ _ (by decide), bp₁]
  have sp₃ : s₃.gpr .esp = SP := by rw [g₃ _ (by decide), sp₁]
  refine WP.of_runBlock ⟨_, runBlock_app_of run₁ run₃, ?_⟩
  -- What the entry wrote.
  have f₃' : Frame [⟨w64 W + BitVec.ofNat 64 128, 2432⟩] s.mem s₃.mem := by
    refine (f₁'.sub fun r hr => ?_).trans (f₃.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
    · simp only [List.mem_map] at hr
      obtain ⟨p, hp, rfl⟩ := hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
  have hsv : SavedAt s₃.mem W s := by
    have := sv₁.frame f₃ fun r hr => by
      simp only [List.mem_map] at hr
      obtain ⟨p, hp, rfl⟩ := hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    obtain ⟨a, b, c, d⟩ := this
    refine ⟨a.trans ?_, b.trans ?_, c.trans ?_, d.trans ?_⟩ <;>
      simp only [hs₀, gpr_setReg_of_ne _ _ (by decide : Reg.ebx ≠ .eax), gpr_setReg_of_ne _ _ (by decide : Reg.esi ≠ .eax),
        gpr_setReg_of_ne _ _ (by decide : Reg.edi ≠ .eax), gpr_setReg_of_ne _ _ (by decide : Reg.ebp ≠ .eax)]
  refine ⟨bp₃, by rw [sp₃, hSP], by rw [rd₃, rd₁]; rfl, by rw [wr₃, wr₁]; rfl, hsv, ?_, f₃'⟩
  intro p hp
  have e := sl₃ p hp
  have hp1 : p.1 < 8 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  rw [hA₁ p.1 hp1] at e
  exact e

end VG.Proof.AesSiv.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.X86.CmacOf`. -/
section

/-!
# AES-SIV on x86: the CMAC of a string (`cmacOf`)

Untrusted: everything here is checked by Lean. `cmacOf stOff` computes the
CMAC of the string at `W + strO` (`W + slenO` bytes) with the context's PRF
into the state at `W + 144`: the code zeroes the state, computes `16 nb`,
the bytes of the whole blocks before the last 1 to 16
(`Spec.Cmac.chainedLen`, `chained_bv`), stores it at `W + nbO`, chains the
`nb` blocks with `vg_cmac_aes_update` and finalizes the rest with
`vg_cmac_aes_finalize` from the context's subkeys (`Siv.cmacWith_chained`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesSiv.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4)
open VG.Proof.AesGcm.X86 (w64 toNat_ofNat32 toNat_add32 slotv zero4_fold length_bytesAt shr4 ofNat_sub32
  and_self_beq32 covers_left readW_writeW_off CT)

/-! ## The length of the whole blocks -/

/-- `and` with `0xfffffff0`: rounding down to a multiple of 16. -/
theorem and_m16 (x : BitVec 32) : x &&& BitVec.ofNat 32 4294967280 = BitVec.ofNat 32 (x.toNat / 16 * 16) := by
  have : BitVec.ofNat 32 4294967280 = BitVec.ofNat 32 ((2 ^ 28 - 1) <<< 4) := by decide
  rw [this]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have hx := x.isLt
  generalize x.toNat = n at *
  rw [Nat.mod_eq_of_lt (by decide), Nat.mod_eq_of_lt (by omega),
    show n / 16 * 16 = (n >>> 4) <<< 4 by rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
    Nat.testBit_two_pow_sub_one]
  by_cases hi : 4 ≤ i
  · by_cases h2 : i - 4 < 28
    · simp [hi, h2, show 4 + (i - 4) = i by omega]
    · have : n.testBit i = false := Nat.testBit_lt_two_pow (by
        calc n < 2 ^ 32 := hx
          _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega))
      simp [hi, h2, this, show 4 + (i - 4) = i by omega]
  · simp [hi]

/-- `chainedLen 16 k` as the code computes it, for `k > 0`: `(k − 1) & ~15`. -/
theorem chained_bv {k : Nat} (h0 : 0 < k) (hk : k < 2 ^ 32) :
    (BitVec.ofNat 32 k - BitVec.ofNat 32 1) &&& BitVec.ofNat 32 4294967280 =
      BitVec.ofNat 32 (Spec.Cmac.chainedLen 16 k) := by
  rw [show (1#32 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ofNat_sub32 h0 hk, VG.Proof.AesSiv.X86.and_m16, VG.Proof.AesGcm.X86.toNat_ofNat32 (by omega)]
  congr 1
  simp only [Spec.Cmac.chainedLen]
  omega

theorem chainedLen_le (k : Nat) : Spec.Cmac.chainedLen 16 k ≤ k := by
  simp only [Spec.Cmac.chainedLen]; omega

theorem chainedLen_rest (k : Nat) : k - Spec.Cmac.chainedLen 16 k ≤ 16 := by
  simp only [Spec.Cmac.chainedLen]; omega

theorem chainedLen_div (k : Nat) : 16 * (Spec.Cmac.chainedLen 16 k / 16) = Spec.Cmac.chainedLen 16 k := by
  simp only [Spec.Cmac.chainedLen]; omega

/-! ## What `cmacOf` writes -/

/-- The CMAC state, `16 nb` at `W + nbO`, the working space of the functions
called and the stack below `SP`. -/
abbrev cmacR (W SP : BitVec 32) : List Region :=
  [⟨w64 W + BitVec.ofNat 64 stOff, 16⟩, ⟨w64 W + BitVec.ofNat 64 nbO, 4⟩, ⟨w64 W + BitVec.ofNat 64 256, 2176⟩,
    below SP 56]

/-- What `cmacOf` leaves: the CMAC of `S` with the context's PRF in the state
at `W + 144`. -/
structure CmacPost (C W SP : BitVec 32) (R : Nat) (s : State) (S : List Byte) (s' : State) : Prop where
  env : VG.Proof.AesSiv.X86.Env C W SP s'
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame (VG.Proof.AesSiv.X86.cmacR W SP) s.mem s'.mem
  out : bytesAt s'.mem (w64 W + BitVec.ofNat 64 stOff) 16 = Spec.Siv.ctxMac s.mem (w64 C) R S

/-- What the string's CMAC needs: the key context and the rounds in their
slots, the string `P` (`k` bytes) at `W + strO` and `W + slenO`. -/
structure CmacPre (C W SP : BitVec 32) (R : Nat) (P : BitVec 32) (k : Nat) (s : State) : Prop where
  env : VG.Proof.AesSiv.X86.Env C W SP s
  ctx : slotv s.mem W ctxO = C
  rounds : slotv s.mem W roundsO = BitVec.ofNat 32 R
  str : slotv s.mem W strO = P
  slen : slotv s.mem W slenO = BitVec.ofNat 32 k
  k32 : k < 2 ^ 32
  buf : VG.Proof.AesSiv.X86.Buf W SP s P k

/-! ## Before the update -/

theorem cmacA_ok {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {R : Nat} {P : BitVec 32} {k : Nat} {s : State}
    (h : VG.Proof.AesSiv.X86.CmacPre C W SP R P k s) :
    ∃ s₁, runBlock isa (zero4 stOff ++ ([.mov .ecx (imm 0), .mov .eax (slot slenO), .alu .test .eax (.reg .eax)] :
        List Instr)) s = some s₁ ∧
      s₁.mem = Cmac.zero4 s.mem (w64 W + BitVec.ofNat 64 stOff) ∧ s₁.gpr .ecx = BitVec.ofNat 32 0 ∧
      s₁.gpr .eax = BitVec.ofNat 32 k ∧ s₁.zf = some (decide (k = 0)) ∧ s₁.gpr .ebp = W ∧ s₁.gpr .esp = SP ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have E := h.env
  have hk := h.buf.lt
  have hz := zero4_fold s.mem W stOff
  simp only [Nat.reduceAdd, stOff] at hz
  have fz : Frame [⟨w64 W + BitVec.ofNat 64 144, 16⟩] s.mem (Cmac.zero4 s.mem (w64 W + BitVec.ofNat 64 144)) :=
    Cmac.frame_store4 _ _ _ _ _
  have hk' : slotv (Cmac.zero4 s.mem (w64 W + BitVec.ofNat 64 144)) W slenO = BitVec.ofNat 32 k := by
    exact (fz.readW (w := 32) (r := ⟨w64 W + BitVec.ofNat 64 slenO, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (by decide) (by decide) (by decide))
      (by decide)).trans h.slen
  refine ⟨_, by crun [zero4, E.ebp, L.aW, E.perm.wW, E.perm.wR, hz, hk'], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cmems [hz]
  · cregs []
  · cregs [hk']
  · cmems [hk']; rw [and_self_beq32 h.k32]
  · cregs [E.ebp]
  · cregs [E.esp]
  all_goals cmems []

theorem cmacB_ok {s : State} {k : Nat} (hax : s.gpr .eax = BitVec.ofNat 32 k) (h0 : 0 < k) (hk : k < 2 ^ 32) :
    ∃ s', runBlock isa [.mov .ecx (.reg .eax), .alu .sub .ecx (imm 1), .alu .and .ecx (imm 0xfffffff0)] s =
        some s' ∧
      s'.gpr .ecx = BitVec.ofNat 32 (Spec.Cmac.chainedLen 16 k) ∧ s'.gpr .ebp = s.gpr .ebp ∧
      s'.gpr .esp = s.gpr .esp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cregs [hax, VG.Proof.AesSiv.X86.chained_bv h0 hk]
  · cregs []
  · cregs []
  all_goals cmems []

theorem cmacC_ok {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {R : Nat} {P : BitVec 32} {s : State}
    (E : VG.Proof.AesSiv.X86.Env C W SP s) (hc : slotv s.mem W ctxO = C) (hr : slotv s.mem W roundsO = BitVec.ofNat 32 R)
    (hp : slotv s.mem W strO = P) {c : Nat} (hcl : c < 2 ^ 32) (hcx : s.gpr .ecx = BitVec.ofNat 32 c) :
    ∃ s', runBlock isa (([.store (at_ .ebp nbO) .ecx, .mov .esi (.reg .ecx), .shift .shr .esi 4,
        .mov .ebx (slot strO)] : List Instr) ++ macArgs stOff) s = some s' ∧
      s'.mem = s.mem.writeW (w64 W + BitVec.ofNat 64 nbO) (BitVec.ofNat 32 c) ∧
      s'.gpr .eax = C ∧ s'.gpr .ecx = BitVec.ofNat 32 R ∧ s'.gpr .edx = W + BitVec.ofNat 32 144 ∧
      s'.gpr .ebx = P ∧ s'.gpr .esi = BitVec.ofNat 32 (c / 16) ∧ s'.gpr .edi = W + BitVec.ofNat 32 256 ∧
      s'.gpr .ebp = W ∧ s'.gpr .esp = SP ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hsh := VG.Proof.AesGcm.X86.shr4 hcl
  have rd : ∀ o, o + 4 ≤ nbO →
      slotv (s.mem.writeW (w64 W + BitVec.ofNat 64 nbO) (BitVec.ofNat 32 c)) W o = slotv s.mem W o :=
    fun o h₁ => readW_writeW_off _ _ _ (.inl h₁) (by simp only [nbO] at h₁; omega) (by decide)
  have hc' := (rd ctxO (by decide)).trans hc
  have hr' := (rd roundsO (by decide)).trans hr
  have hp' := (rd strO (by decide)).trans hp
  refine ⟨_, by crun [macArgs, E.ebp, L.aW, E.perm.wW, E.perm.wR, hcx, hc', hr', hp'], ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · cmems [hcx]
  · cregs [hc']
  · cregs [hr']
  · cregs [E.ebp]
  · cregs [hp']
  · cregs [hcx, hsh]
  · cregs [E.ebp]
  · cregs [E.ebp]
  · cregs [E.esp]
  all_goals cmems []

/-- What `cmacPre` leaves: the arguments of `vg_cmac_aes_update` for the
whole blocks before the last bytes, the zero state, and their length at
`W + nbO`. -/
structure CmacMid (C W SP : BitVec 32) (R : Nat) (P : BitVec 32) (k : Nat) (s s₁ : State) : Prop where
  env : VG.Proof.AesSiv.X86.Env C W SP s₁
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr
  mem : s₁.mem = (Cmac.zero4 s.mem (w64 W + BitVec.ofNat 64 stOff)).writeW (w64 W + BitVec.ofNat 64 nbO)
    (BitVec.ofNat 32 (Spec.Cmac.chainedLen 16 k))
  eax : s₁.gpr .eax = C
  ecx : s₁.gpr .ecx = BitVec.ofNat 32 R
  edx : s₁.gpr .edx = W + BitVec.ofNat 32 144
  ebx : s₁.gpr .ebx = P
  esi : s₁.gpr .esi = BitVec.ofNat 32 (Spec.Cmac.chainedLen 16 k / 16)
  edi : s₁.gpr .edi = W + BitVec.ofNat 32 256

theorem cmacPre_ok {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {R : Nat} {P : BitVec 32} {k : Nat} {s : State}
    (h : VG.Proof.AesSiv.X86.CmacPre C W SP R P k s) : WP isa (cmacPre stOff) s (VG.Proof.AesSiv.X86.CmacMid C W SP R P k s) := by
  have E := h.env
  have hk := h.buf.lt
  have hk32 := h.k32
  have hcl := VG.Proof.AesSiv.X86.chainedLen_le k
  obtain ⟨s₁, run₁, m₁, cx₁, ax₁, zf₁, bp₁, sp₁, rd₁, wr₁⟩ := VG.Proof.AesSiv.X86.cmacA_ok L h
  have E₁ : VG.Proof.AesSiv.X86.Env C W SP s₁ := ⟨bp₁, sp₁, E.perm.of_eq rd₁ wr₁⟩
  have fz : Frame [⟨w64 W + BitVec.ofNat 64 144, 16⟩] s.mem s₁.mem := by
    rw [m₁]; exact Cmac.frame_store4 _ _ _ _ _
  have keep : ∀ o, 176 ≤ o → o + 4 ≤ 208 → slotv s₁.mem W o = slotv s.mem W o := fun o h₁ h₂ =>
    fz.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by omega)) (by omega) (by decide))
      (by decide)
  have last (s₂ : State) (E₂ : VG.Proof.AesSiv.X86.Env C W SP s₂) (rd₂ : s₂.rd = s.rd) (wr₂ : s₂.wr = s.wr) (m₂ : s₂.mem = s₁.mem)
      (cx₂ : s₂.gpr .ecx = BitVec.ofNat 32 (Spec.Cmac.chainedLen 16 k)) :
      WP isa (.block ([.store (at_ .ebp nbO) .ecx, .mov .esi (.reg .ecx), .shift .shr .esi 4,
        .mov .ebx (slot strO)] ++ macArgs stOff)) s₂ (VG.Proof.AesSiv.X86.CmacMid C W SP R P k s) := by
    obtain ⟨s₃, run₃, m₃, ax₃, cx₃, dx₃, bx₃, si₃, di₃, bp₃, sp₃, rd₃, wr₃⟩ := VG.Proof.AesSiv.X86.cmacC_ok (R := R) (P := P) L E₂
      (by rw [m₂, keep _ (by decide) (by decide)]; exact h.ctx)
      (by rw [m₂, keep _ (by decide) (by decide)]; exact h.rounds)
      (by rw [m₂, keep _ (by decide) (by decide)]; exact h.str) (by omega) cx₂
    exact WP.of_runBlock ⟨s₃, run₃, ⟨bp₃, sp₃, E.perm.of_eq (by rw [rd₃, rd₂]) (by rw [wr₃, wr₂])⟩,
      by rw [rd₃, rd₂], by rw [wr₃, wr₂], by rw [m₃, m₂, m₁], ax₃, cx₃, dx₃, bx₃, si₃, di₃⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have mid : WP isa (.ite .e (.block []) (.block [.mov .ecx (.reg .eax), .alu .sub .ecx (imm 1),
      .alu .and .ecx (imm 0xfffffff0)])) s₁ fun s₂ =>
      s₂.gpr .ecx = BitVec.ofNat 32 (Spec.Cmac.chainedLen 16 k) ∧ VG.Proof.AesSiv.X86.Env C W SP s₂ ∧ s₂.rd = s.rd ∧
        s₂.wr = s.wr ∧ s₂.mem = s₁.mem := by
    refine WP.ite (decide (k = 0)) (VG.Proof.AesSiv.X86.eval_e zf₁) (fun hz => ?_) (fun hz => ?_)
    · have hk0 : k = 0 := of_decide_eq_true hz
      refine WP.of_runBlock ⟨s₁, rfl, ?_, E₁, rd₁, wr₁, rfl⟩
      rw [cx₁, hk0]; rfl
    · have hk0 : 0 < k := Nat.pos_of_ne_zero (of_decide_eq_false hz)
      obtain ⟨s₂, run₂, cx₂, bp₂, sp₂, m₂, rd₂, wr₂⟩ := VG.Proof.AesSiv.X86.cmacB_ok ax₁ hk0 hk32
      exact WP.of_runBlock ⟨s₂, run₂, cx₂, E₁.keep bp₂ sp₂ rd₂ wr₂, by rw [rd₂, rd₁], by rw [wr₂, wr₁], m₂⟩
  exact WP.seq (WP.mono mid fun s₂ ⟨cx₂, E₂, rd₂, wr₂, m₂⟩ => last s₂ E₂ rd₂ wr₂ m₂ cx₂)

theorem chainedLen_lt {k : Nat} (h0 : 0 < k) : Spec.Cmac.chainedLen 16 k < k := by
  simp only [Spec.Cmac.chainedLen]; omega

/-! ## Between the calls -/

theorem cmacMid_ok {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {R : Nat} {P : BitVec 32} {k c : Nat} {s : State}
    (E : VG.Proof.AesSiv.X86.Env C W SP s) (hc : slotv s.mem W ctxO = C) (hr : slotv s.mem W roundsO = BitVec.ofNat 32 R)
    (hp : slotv s.mem W strO = P) (hk : slotv s.mem W slenO = BitVec.ofNat 32 k)
    (hn : slotv s.mem W nbO = BitVec.ofNat 32 c) (hck : c ≤ k) (hk32 : k < 2 ^ 32) :
    ∃ s', runBlock isa (cmacMid stOff) s = some s' ∧ s'.mem = s.mem ∧
      s'.gpr .eax = C ∧ s'.gpr .ecx = BitVec.ofNat 32 R ∧ s'.gpr .edx = W + BitVec.ofNat 32 144 ∧
      s'.gpr .ebx = P + BitVec.ofNat 32 c ∧ s'.gpr .esi = BitVec.ofNat 32 (k - c) ∧
      s'.gpr .edi = W + BitVec.ofNat 32 256 ∧ s'.gpr .ebp = W ∧ s'.gpr .esp = SP ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hsub := ofNat_sub32 hck hk32
  refine ⟨_, by crun [cmacMid, macArgs, E.ebp, L.aW, E.perm.wR, hc, hr, hp, hk, hn], ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · rfl
  · cregs [hc]
  · cregs [hr]
  · cregs [E.ebp]
  · cregs [hp, hn]
  · cregs [hk, hn, hsub]
  · cregs [E.ebp]
  · cregs [E.ebp]
  · cregs [E.esp]
  all_goals rfl

/-! ## The whole -/

theorem cmacR_c {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {d n : Nat} (hd : d + n ≤ 512) :
    ∀ r ∈ VG.Proof.AesSiv.X86.cmacR W SP, (⟨w64 C + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.c_w' hd (by decide)
  · exact L.c_w' hd (by decide)
  · exact L.c_w' hd (by decide)
  · exact (L.stk_c' hd).symm

theorem cmacR_buf {W SP : BitVec 32} {s : State} {P : BitVec 32} {k : Nat} (B : VG.Proof.AesSiv.X86.Buf W SP s P k) :
    ∀ r ∈ VG.Proof.AesSiv.X86.cmacR W SP, (⟨w64 P, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact B.w.sub_right (Lay.wSub (by decide))
  · exact B.w.sub_right (Lay.wSub (by decide))
  · exact B.w.sub_right (Lay.wSub (by decide))
  · exact B.stk.symm

theorem sub_cmacR {W SP : BitVec 32} {rs : List Region} (h : ∀ r ∈ rs, ∃ r' ∈ VG.Proof.AesSiv.X86.cmacR W SP, Region.Sub r r')
    {m m' : Mem} (hf : Frame rs m m') : Frame (VG.Proof.AesSiv.X86.cmacR W SP) m m' := hf.sub h

/-- The CMAC of the string at `W + strO`. -/
theorem cmacOf_ok (v : Ctr32Impl) {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {P : BitVec 32} {k : Nat} {s : State} (h : VG.Proof.AesSiv.X86.CmacPre C W SP R P k s) :
    WP isa (cmacOf v.callee v.suffix stOff) s (VG.Proof.AesSiv.X86.CmacPost C W SP R s (bytesAt s.mem (w64 P) k)) := by
  have hk32 := h.k32
  have hcl := VG.Proof.AesSiv.X86.chainedLen_le k
  have hrest := VG.Proof.AesSiv.X86.chainedLen_rest k
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with h | h | h <;> omega
  refine WP.seq (WP.mono (VG.Proof.AesSiv.X86.cmacPre_ok L h) fun s₁ M => ?_)
  -- The whole blocks.
  have B₁ : VG.Proof.AesSiv.X86.Buf W SP s₁ P (16 * (Spec.Cmac.chainedLen 16 k / 16)) :=
    (h.buf.take (by rw [VG.Proof.AesSiv.X86.chainedLen_div]; exact hcl)).of_eq M.rd M.wr
  refine WP.seq (WP.mono (VG.Proof.AesSiv.X86.updCall_ok v L M.env hR (y := 144) (.inl (by decide)) (VG.Proof.AesSiv.X86.srcBuf B₁)
    (B₁.w.sub_right (Lay.wSub (by decide))) (by rw [VG.Proof.AesSiv.X86.chainedLen_div]; omega) M.eax M.ecx M.edx M.ebx M.esi M.edi)
    fun s₂ ⟨E₂, rd₂, wr₂, _, f₂, o₂⟩ => ?_)
  -- The slots after the update.
  have fz : Frame [⟨w64 W + BitVec.ofNat 64 144, 16⟩, ⟨w64 W + BitVec.ofNat 64 nbO, 4⟩] s.mem s₁.mem := by
    rw [M.mem]
    exact ((Cmac.frame_store4 _ _ _ _ _).sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩).writeW (by simp) _
      (Region.contains_self _ _)
  have f₁₂ : Frame (VG.Proof.AesSiv.X86.cmacR W SP) s.mem s₂.mem := by
    refine (fz.sub fun r hr => ?_).trans (f₂.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  have keep₂ : ∀ o, 176 ≤ o → o + 4 ≤ 208 → slotv s₂.mem W o = slotv s.mem W o := fun o h₁ h₂ =>
    f₁₂.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact Lay.w_w (.inr (by simp only [stOff]; omega)) (by omega) (by decide)
      · exact Lay.w_w (.inl (by simp only [nbO]; omega)) (by omega) (by decide)
      · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
      · exact (L.stk_w' (by omega)).symm) (by decide)
  have hn₂ : slotv s₂.mem W nbO = BitVec.ofNat 32 (Spec.Cmac.chainedLen 16 k) := by
    rw [show slotv s₂.mem W nbO = slotv s₁.mem W nbO from f₂.readW (r := ⟨w64 W + BitVec.ofNat 64 nbO, 4⟩)
      (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact (L.stk_w' (by decide)).symm) (by decide), M.mem]
    exact Mem.readW_writeW_self32 _ _ _
  -- Between the calls.
  obtain ⟨s₃, run₃, m₃, ax₃, cx₃, dx₃, bx₃, si₃, di₃, bp₃, sp₃, rd₃, wr₃⟩ := VG.Proof.AesSiv.X86.cmacMid_ok (C := C) (R := R) (P := P) (k := k) L E₂
    (by rw [keep₂ _ (by decide) (by decide)]; exact h.ctx) (by rw [keep₂ _ (by decide) (by decide)]; exact h.rounds)
    (by rw [keep₂ _ (by decide) (by decide)]; exact h.str) (by rw [keep₂ _ (by decide) (by decide)]; exact h.slen)
    hn₂ hcl hk32
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have E₃ : VG.Proof.AesSiv.X86.Env C W SP s₃ := ⟨bp₃, sp₃, E₂.perm.of_eq rd₃ wr₃⟩
  -- The last bytes.
  have hwc : P.toNat + Spec.Cmac.chainedLen 16 k < 2 ^ 32 := by
    have := h.buf.wrap
    have := P.isLt
    by_cases h0 : k = 0
    · subst h0; simp only [Spec.Cmac.chainedLen]; omega
    · have := VG.Proof.AesSiv.X86.chainedLen_lt (Nat.pos_of_ne_zero h0); omega
  have B₃ : VG.Proof.AesSiv.X86.Buf W SP s₃ (P + BitVec.ofNat 32 (Spec.Cmac.chainedLen 16 k)) (k - Spec.Cmac.chainedLen 16 k) :=
    (h.buf.drop hcl hwc).of_eq (by rw [rd₃, rd₂, M.rd]) (by rw [wr₃, wr₂, M.wr])
  refine WP.mono (VG.Proof.AesSiv.X86.finCall_ok v L E₃ hR (y := 144) (.inl (by decide)) hrest (VG.Proof.AesSiv.X86.srcBuf B₃)
    (B₃.w.sub_right (Lay.wSub (by decide))) ax₃ cx₃ dx₃ bx₃ si₃ di₃) fun s₄ ⟨E₄, rd₄, wr₄, _, f₄, o₄⟩ => ?_
  have f₁₄ : Frame (VG.Proof.AesSiv.X86.cmacR W SP) s.mem s₄.mem := f₁₂.trans (by
    rw [← m₃]
    exact f₄.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩)
  refine ⟨E₄, by rw [rd₄, rd₃, rd₂, M.rd], by rw [wr₄, wr₃, wr₂, M.wr], f₁₄, ?_⟩
  -- The bytes the calls read are those at the start.
  have hC {d n : Nat} (hd : d + n ≤ 512) (m : Mem) (hm : Frame (VG.Proof.AesSiv.X86.cmacR W SP) s.mem m) :
      bytesAt m (w64 C + BitVec.ofNat 64 d) n = bytesAt s.mem (w64 C + BitVec.ofNat 64 d) n :=
    Proof.AesGcm.X86.bytesAt_frame hm (VG.Proof.AesSiv.X86.cmacR_c L hd) (by omega)
  have hP {d n : Nat} (hd : d + n ≤ k) (m : Mem) (hm : Frame (VG.Proof.AesSiv.X86.cmacR W SP) s.mem m) :
      bytesAt m (w64 P + BitVec.ofNat 64 d) n = bytesAt s.mem (w64 P + BitVec.ofNat 64 d) n :=
    Proof.AesGcm.X86.bytesAt_frame hm (fun r hr => (VG.Proof.AesSiv.X86.cmacR_buf h.buf r hr).sub_left (Offset.sub_base _ hd))
      (by have := h.buf.lt; omega)
  have f₁₃ : Frame (VG.Proof.AesSiv.X86.cmacR W SP) s.mem s₃.mem := by rw [m₃]; exact f₁₂
  have f₁₁ : Frame (VG.Proof.AesSiv.X86.cmacR W SP) s.mem s₁.mem := fz.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  have sch₃ := hC (d := 0) (n := 16 * (R + 1)) (by omega) _ f₁₃
  have sch₁ := hC (d := 0) (n := 16 * (R + 1)) (by omega) _ f₁₁
  have k1 := hC (d := 240) (n := 16) (by decide) _ f₁₃
  have k2 := hC (d := 256) (n := 16) (by decide) _ f₁₃
  have pre := hP (d := 0) (n := Spec.Cmac.chainedLen 16 k) (by omega) _ f₁₁
  have rest := hP (d := Spec.Cmac.chainedLen 16 k) (n := k - Spec.Cmac.chainedLen 16 k) (by omega) _ f₁₃
  rw [BitVec.add_zero] at sch₃ sch₁ pre
  have hz : bytesAt s₁.mem (w64 W + BitVec.ofNat 64 144) 16 = Spec.Cmac.zeros 16 := by
    rw [M.mem, Proof.AesGcm.X86.bytesAt_frame (rs := [⟨w64 W + BitVec.ofNat 64 nbO, 4⟩])
      ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide))
      (by decide), Cmac.zero4_bytes]
  have hS : (bytesAt s.mem (w64 P) k).length = k := length_bytesAt _ _ _
  have hsplit : k = Spec.Cmac.chainedLen 16 k + (k - Spec.Cmac.chainedLen 16 k) := by omega
  have aP : w64 (P + BitVec.ofNat 32 (Spec.Cmac.chainedLen 16 k)) =
      w64 P + BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 k) := Buf.ptr hwc
  rw [o₄, sch₃, k1, k2, aP, rest, m₃, o₂, Proof.Cmac.Stream.blocksAt_eq, VG.Proof.AesSiv.X86.chainedLen_div, sch₁, hz, pre,
    Spec.Siv.ctxMac, Spec.Siv.schedCiph, Siv.cmacWith_chained, hS]
  have tk : (bytesAt s.mem (w64 P) k).take (Spec.Cmac.chainedLen 16 k) =
      bytesAt s.mem (w64 P) (Spec.Cmac.chainedLen 16 k) := by
    have := take_bytesAt s.mem (w64 P) (a := Spec.Cmac.chainedLen 16 k) (b := k - Spec.Cmac.chainedLen 16 k)
    rwa [← hsplit] at this
  have dr : (bytesAt s.mem (w64 P) k).drop (Spec.Cmac.chainedLen 16 k) =
      bytesAt s.mem (w64 P + BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 k)) (k - Spec.Cmac.chainedLen 16 k) := by
    have := drop_bytesAt s.mem (w64 P) (a := Spec.Cmac.chainedLen 16 k) (b := k - Spec.Cmac.chainedLen 16 k)
    rwa [← hsplit] at this
  rw [tk, dr, Proof.Cmac.xor_comm]
  rfl

/-! ## Constant time -/

/-- The slots `cmacOf` keeps. -/
theorem cmacR_slot {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {m m' : Mem} (hf : Frame (VG.Proof.AesSiv.X86.cmacR W SP) m m') {o : Nat}
    (h₁ : 176 ≤ o) (h₂ : o + 4 ≤ 208) : slotv m' W o = slotv m W o :=
  hf.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Lay.w_w (.inr (by simp only [stOff]; omega)) (by omega) (by decide)
    · exact Lay.w_w (.inl (by simp only [nbO]; omega)) (by omega) (by decide)
    · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
    · exact (L.stk_w' (by omega)).symm) (by decide)

/-- After the update: what `cmacMid` and the finalization need. -/
structure CmacAft (C W SP : BitVec 32) (R : Nat) (P : BitVec 32) (k : Nat) (s s₂ : State) : Prop where
  env : VG.Proof.AesSiv.X86.Env C W SP s₂
  rd : s₂.rd = s.rd
  wr : s₂.wr = s.wr
  frame : Frame (VG.Proof.AesSiv.X86.cmacR W SP) s.mem s₂.mem
  nb : slotv s₂.mem W nbO = BitVec.ofNat 32 (Spec.Cmac.chainedLen 16 k)

theorem cmacUpd_ok (v : Ctr32Impl) {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {P : BitVec 32} {k : Nat} {s s₁ : State} (h : VG.Proof.AesSiv.X86.CmacPre C W SP R P k s) (M : VG.Proof.AesSiv.X86.CmacMid C W SP R P k s s₁) :
    WP isa (updCall v.callee v.suffix) s₁ (VG.Proof.AesSiv.X86.CmacAft C W SP R P k s) := by
  have hcl := VG.Proof.AesSiv.X86.chainedLen_le k
  have B₁ : VG.Proof.AesSiv.X86.Buf W SP s₁ P (16 * (Spec.Cmac.chainedLen 16 k / 16)) :=
    (h.buf.take (by rw [VG.Proof.AesSiv.X86.chainedLen_div]; exact hcl)).of_eq M.rd M.wr
  refine WP.mono (VG.Proof.AesSiv.X86.updCall_ok v L M.env hR (y := 144) (.inl (by decide)) (VG.Proof.AesSiv.X86.srcBuf B₁)
    (B₁.w.sub_right (Lay.wSub (by decide))) (by rw [VG.Proof.AesSiv.X86.chainedLen_div]; have := h.k32; omega) M.eax M.ecx M.edx M.ebx
    M.esi M.edi) fun s₂ ⟨E₂, rd₂, wr₂, _, f₂, _⟩ => ⟨E₂, by rw [rd₂, M.rd], by rw [wr₂, M.wr], ?_, ?_⟩
  · have fz : Frame [⟨w64 W + BitVec.ofNat 64 144, 16⟩, ⟨w64 W + BitVec.ofNat 64 nbO, 4⟩] s.mem s₁.mem := by
      rw [M.mem]
      exact ((Cmac.frame_store4 _ _ _ _ _).sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩).writeW (by simp) _
        (Region.contains_self _ _)
    refine (fz.sub fun r hr => ?_).trans (f₂.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  · rw [show slotv s₂.mem W nbO = slotv s₁.mem W nbO from f₂.readW (r := ⟨w64 W + BitVec.ofNat 64 nbO, 4⟩)
      (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact (L.stk_w' (by decide)).symm) (by decide), M.mem]
    exact Mem.readW_writeW_self32 _ _ _

theorem roundDown_ct {I : State → Prop} :
    CT I (.block [.mov .ecx (.reg .eax), .alu .sub .ecx (imm 1), .alu .and .ecx (imm 0xfffffff0)]) :=
  CT.taint [] (fun _ _ _ _ r hr => by simp at hr) (by taint_decide)

theorem cmacPre_ct {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {R : Nat} {P : BitVec 32} {k : Nat} :
    CT (VG.Proof.AesSiv.X86.CmacPre C W SP R P k) (cmacPre stOff) := by
  refine CT.block_seq [.ebp] (VG.Proof.AesSiv.X86.pin_ebp fun s h => h.env.ebp) (by taint_decide) (fun s hs => VG.Proof.AesSiv.X86.cmacA_ok L hs) ?_
  refine CT.seq (J := fun s => s.gpr .ebp = W)
    (CT.ite (decide (k = 0)) (fun _ ⟨_, _, _, _, _, zf, _⟩ => VG.Proof.AesSiv.X86.eval_e zf) (fun _ => CT.nil)
      (fun _ => VG.Proof.AesSiv.X86.roundDown_ct))
    (fun s₁ ⟨s, hs, _, _, ax, zf, bp, _⟩ => ?_) (CT.taint [.ebp] (VG.Proof.AesSiv.X86.pin_ebp fun _ h => h) (by taint_decide))
  refine WP.ite (decide (k = 0)) (VG.Proof.AesSiv.X86.eval_e zf) (fun _ => WP.of_runBlock ⟨_, rfl, bp⟩) (fun hz => ?_)
  have hk0 : 0 < k := Nat.pos_of_ne_zero (of_decide_eq_false hz)
  obtain ⟨s₂, run₂, _, bp₂, _⟩ := VG.Proof.AesSiv.X86.cmacB_ok ax hk0 hs.k32
  exact WP.of_runBlock ⟨s₂, run₂, by rw [bp₂, bp]⟩

/-- `cmacOf` is constant time from what it starts from. -/
theorem cmacOf_ct (v : Ctr32Impl) {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {P : BitVec 32} {k : Nat} (hk : k < 2 ^ 32) : CT (VG.Proof.AesSiv.X86.CmacPre C W SP R P k) (cmacOf v.callee v.suffix stOff) := by
  have hcl := VG.Proof.AesSiv.X86.chainedLen_le k
  have hrest := VG.Proof.AesSiv.X86.chainedLen_rest k
  refine CT.seq (J := fun s₁ => ∃ s, VG.Proof.AesSiv.X86.CmacPre C W SP R P k s ∧ VG.Proof.AesSiv.X86.CmacMid C W SP R P k s s₁) (VG.Proof.AesSiv.X86.cmacPre_ct L)
    (fun s hs => WP.mono (VG.Proof.AesSiv.X86.cmacPre_ok L hs) fun s₁ M => ⟨s, hs, M⟩) ?_
  refine CT.seq (J := fun s₂ => ∃ s, VG.Proof.AesSiv.X86.CmacPre C W SP R P k s ∧ VG.Proof.AesSiv.X86.CmacAft C W SP R P k s s₂)
    (VG.Proof.AesSiv.X86.updCall_ct v L hR (y := 144) (.inl (by decide)) (Q := P) (n := Spec.Cmac.chainedLen 16 k / 16)
      (by rw [VG.Proof.AesSiv.X86.chainedLen_div]; omega) fun s₁ ⟨s, hs, M⟩ => ?_)
    (fun s₁ ⟨s, hs, M⟩ => WP.mono (VG.Proof.AesSiv.X86.cmacUpd_ok v L hR hs M) fun s₂ A => ⟨s, hs, A⟩) ?_
  · have B₁ : VG.Proof.AesSiv.X86.Buf W SP s₁ P (16 * (Spec.Cmac.chainedLen 16 k / 16)) :=
      (hs.buf.take (by rw [VG.Proof.AesSiv.X86.chainedLen_div]; exact hcl)).of_eq M.rd M.wr
    exact ⟨M.env, VG.Proof.AesSiv.X86.srcBuf B₁, B₁.w.sub_right (Lay.wSub (by decide)), M.eax, M.ecx, M.edx, M.ebx, M.esi, M.edi⟩
  refine CT.block_seq [.ebp] (VG.Proof.AesSiv.X86.pin_ebp fun s h => let ⟨_, _, A⟩ := h; A.env.ebp) (by taint_decide)
    (fun s₂ ⟨s, hs, A⟩ => VG.Proof.AesSiv.X86.cmacMid_ok (C := C) (R := R) (P := P) (k := k) L A.env
      (by rw [VG.Proof.AesSiv.X86.cmacR_slot L A.frame (by decide) (by decide)]; exact hs.ctx)
      (by rw [VG.Proof.AesSiv.X86.cmacR_slot L A.frame (by decide) (by decide)]; exact hs.rounds)
      (by rw [VG.Proof.AesSiv.X86.cmacR_slot L A.frame (by decide) (by decide)]; exact hs.str)
      (by rw [VG.Proof.AesSiv.X86.cmacR_slot L A.frame (by decide) (by decide)]; exact hs.slen) A.nb hcl hs.k32) ?_
  refine VG.Proof.AesSiv.X86.finCall_ct v L hR (y := 144) (.inl (by decide)) (P := P + BitVec.ofNat 32 (Spec.Cmac.chainedLen 16 k)) hrest fun s₃ ⟨s₂, ⟨s, hs, A⟩, m₃, ax, cx, dx, bx, si, di,
    bp, sp, rd₃, wr₃⟩ => ?_
  have hwc : P.toNat + Spec.Cmac.chainedLen 16 k < 2 ^ 32 := by
    have := hs.buf.wrap
    have := P.isLt
    by_cases h0 : k = 0
    · subst h0; simp only [Spec.Cmac.chainedLen]; omega
    · have := VG.Proof.AesSiv.X86.chainedLen_lt (Nat.pos_of_ne_zero h0); omega
  have B₃ : VG.Proof.AesSiv.X86.Buf W SP s₃ (P + BitVec.ofNat 32 (Spec.Cmac.chainedLen 16 k)) (k - Spec.Cmac.chainedLen 16 k) :=
    (hs.buf.drop hcl hwc).of_eq (by rw [rd₃, A.rd]) (by rw [wr₃, A.wr])
  exact ⟨⟨bp, sp, A.env.perm.of_eq rd₃ wr₃⟩, VG.Proof.AesSiv.X86.srcBuf B₃, B₃.w.sub_right (Lay.wSub (by decide)), ax, cx, dx, bx, si,
    di⟩

end VG.Proof.AesSiv.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.X86.Ctr`. -/
section

/-!
# AES-SIV on x86: CTR (`ctr`)

Untrusted: everything here is checked by Lean. As on ARMv7
(`Proof/AesSiv/Arm/Ctr.lean`): `counter 0` sets the counter block at
`W + 96` to `Q`, the IV at `W` with bit 7 of its bytes 8 and 12 cleared
(`counter_bytes`, `Proof.AesSiv.counter_words4`). `ctrWhole` encrypts the
whole blocks of the data by one call of `vg_aes_ctr32` from `Q`, whose
counters do not wrap around (`Proof.AesSiv.counter_low`,
`Proof.AesSiv.repeat_inc32`), and which leaves `Q + nb` in the counter block
(`ctrWhole_ok`); `ctrTail` XORs the last bytes with the first bytes of the
keystream block of that counter, which `vg_aes_ctr32` computes on a zero
block at `W + 80` (`ctrTail_ok`). Together, CTR's output on the data
(`ctr_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesSiv.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (blockAt blocksAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4 xorLoop)
open VG.Proof.AesGcm.X86 (w64 toNat_ofNat32 slotv zero4_fold length_bytesAt readW_writeW_off covers_off shr4
  and15 ofNat_sub32 XorPre XorPost xorLoop_ok xorBytes length_xorBytes CT)
open VG.Proof.Cmac (le4 store4)

/-- The data: `n` bytes at `D` the code may read and write, apart from the
key context, `W` and the stack below `SP`. -/
structure Dat (C W SP : BitVec 32) (s : State) (D : BitVec 32) (n : Nat) : Prop where
  buf : VG.Proof.AesSiv.X86.Buf W SP s D n
  wr : Covers [⟨w64 D, n⟩] s.wr
  c : (⟨w64 C, 512⟩ : Region).Disjoint ⟨w64 D, n⟩

theorem Dat.of_eq {C W SP : BitVec 32} {s s' : State} {D : BitVec 32} {n : Nat} (h : VG.Proof.AesSiv.X86.Dat C W SP s D n)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesSiv.X86.Dat C W SP s' D n :=
  ⟨h.buf.of_eq hrd hwr, by rw [hwr]; exact h.wr, h.c⟩

/-- The first `k` bytes of the data as `vg_aes_ctr32`'s. -/
theorem Dat.dst {C W SP : BitVec 32} {s : State} {D : BitVec 32} {n : Nat} (h : VG.Proof.AesSiv.X86.Dat C W SP s D n) {k : Nat}
    (hk : k ≤ n) {c : Nat} (hc : c + 16 ≤ 256) : VG.Proof.AesSiv.X86.Dst C W SP s D k c where
  wr := fun a m ⟨r, hr, hc'⟩ => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.wr a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc' ⊢; omega⟩
  wrap := by have := h.buf.wrap; omega
  dk := h.c.sub_right (Region.sub_prefix hk)
  dc := (h.buf.w.sub_left (Region.sub_prefix hk)).sub_right (Lay.wSub (by omega))
  ds := (h.buf.w.sub_left (Region.sub_prefix hk)).sub_right (Lay.wSub (by decide))
  stk := h.buf.stk.sub_right (Region.sub_prefix hk)

/-- What CTR writes: the keystream and counter blocks, the working space of
`vg_aes_ctr32`, the stack below `SP` and the data. -/
abbrev ctrR (W SP D : BitVec 32) (n : Nat) : List Region :=
  [⟨w64 W + BitVec.ofNat 64 ksOff, 32⟩, ⟨w64 W + BitVec.ofNat 64 256, 2048⟩, below SP 56, ⟨w64 D, n⟩]

theorem beq_zero32 {a : Nat} (ha : a < 2 ^ 32) : (BitVec.ofNat 32 a == 0) = decide (a = 0) := by
  have := Proof.AesGcm.X86.and_self_beq32 ha
  rwa [BitVec.and_self] at this

/-! ## The counter -/

theorem counter_ok {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {s : State} (E : VG.Proof.AesSiv.X86.Env C W SP s) :
    ∃ s', runBlock isa (counter 0) s = some s' ∧
      s'.mem = store4 s.mem (w64 W + BitVec.ofNat 64 cbOff) (s.mem.readW (w64 W + BitVec.ofNat 64 0) 32)
        (s.mem.readW (w64 W + BitVec.ofNat 64 4) 32) (s.mem.readW (w64 W + BitVec.ofNat 64 8) 32 &&& qm4)
        (s.mem.readW (w64 W + BitVec.ofNat 64 12) 32 &&& qm4) ∧
      s'.gpr .ebp = W ∧ s'.gpr .esp = SP ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [counter, E.ebp, L.aW, E.perm.wW, E.perm.wR], ?_, ?_, ?_, ?_, ?_⟩
  · cmems [store4, VG.Proof.AesSiv.X86.add_ofNat_assoc, qm4]
    rfl
  · cregs [E.ebp]
  · cregs [E.esp]
  all_goals cmems []

/-- `Q` at `W + 96`. -/
theorem counter_bytes (m : Mem) (W : BitVec 32) :
    bytesAt (store4 m (w64 W + BitVec.ofNat 64 cbOff) (m.readW (w64 W + BitVec.ofNat 64 0) 32)
        (m.readW (w64 W + BitVec.ofNat 64 4) 32) (m.readW (w64 W + BitVec.ofNat 64 8) 32 &&& qm4)
        (m.readW (w64 W + BitVec.ofNat 64 12) 32 &&& qm4)) (w64 W + BitVec.ofNat 64 cbOff) 16 =
      Spec.Siv.counter (bytesAt m (w64 W) 16) := by
  rw [Proof.Cmac.bytesAt_store4, counter_words4, BitVec.add_zero, Proof.Cmac.bytesAt_split4 m (w64 W), ← Proof.Cmac.le4_readW,
    ← Proof.Cmac.le4_readW, ← Proof.Cmac.le4_readW, ← Proof.Cmac.le4_readW]

/-! ## The whole blocks -/

theorem whole1_ok {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {s : State} (E : VG.Proof.AesSiv.X86.Env C W SP s) {n : Nat}
    (hl : slotv s.mem W lenO = BitVec.ofNat 32 n) (hn : n < 2 ^ 32) :
    ∃ s', runBlock isa [.mov .edi (slot lenO), .shift .shr .edi 4, .alu .test .edi (.reg .edi)] s = some s' ∧
      s'.gpr .edi = BitVec.ofNat 32 (n / 16) ∧ s'.zf = some (decide (n / 16 = 0)) ∧
      (∀ r, r ≠ .edi → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hsh := VG.Proof.AesGcm.X86.shr4 hn
  refine ⟨_, by crun [E.ebp, L.aW, E.perm.wR, hl], ?_, ?_, fun r h₁ => ?_, ?_, ?_, ?_⟩
  · cregs [hl, hsh]
  · cmems [hl, hsh]; rw [Proof.AesGcm.X86.and_self_beq32 (by omega)]
  · cregs []
  all_goals cmems []

theorem ctrArgs_ok {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {R : Nat} {s : State} (E : VG.Proof.AesSiv.X86.Env C W SP s)
    (hc : slotv s.mem W ctxO = C) (hr : slotv s.mem W roundsO = BitVec.ofNat 32 R) {D : BitVec 32}
    (hd : slotv s.mem W dataO = D) :
    ∃ s', runBlock isa (ctrArgs ++ ([.mov .ebx (slot dataO)] : List Instr)) s = some s' ∧
      s'.gpr .eax = C + BitVec.ofNat 32 272 ∧ s'.gpr .ecx = BitVec.ofNat 32 R ∧
      s'.gpr .edx = W + BitVec.ofNat 32 cbOff ∧ s'.gpr .ebx = D ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .ebx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  refine ⟨_, by crun [ctrArgs, E.ebp, L.aW, E.perm.wR, hc, hr, hd], ?_, ?_, ?_, ?_, fun r h₁ h₂ h₃ h₄ => ?_, ?_, ?_,
    ?_⟩
  · cregs [hc]
  · cregs [hr]
  · cregs [E.ebp]
  · cregs [hd]
  · cregs []
  all_goals cmems []

/-! ## The last bytes -/

theorem tail1_ok {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {s : State} (E : VG.Proof.AesSiv.X86.Env C W SP s) {n : Nat}
    (hl : slotv s.mem W lenO = BitVec.ofNat 32 n) (hn : n < 2 ^ 32) :
    ∃ s', runBlock isa [.mov .ecx (slot lenO), .alu .and .ecx (imm 15)] s = some s' ∧
      s'.gpr .ecx = BitVec.ofNat 32 (n % 16) ∧ s'.zf = some (decide (n % 16 = 0)) ∧
      (∀ r, r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ha := VG.Proof.AesGcm.X86.and15 (BitVec.ofNat 32 n)
  rw [VG.Proof.AesGcm.X86.toNat_ofNat32 hn] at ha
  refine ⟨_, by crun [E.ebp, L.aW, E.perm.wR, hl], ?_, ?_, fun r h₁ => ?_, ?_, ?_, ?_⟩
  · cregs [hl, ha]
  · cmems [hl, ha]; rw [VG.Proof.AesSiv.X86.beq_zero32 (by omega)]
  · cregs []
  all_goals cmems []

theorem tailArgs_ok' {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {R : Nat} {s : State} (E : VG.Proof.AesSiv.X86.Env C W SP s)
    (hc : slotv s.mem W ctxO = C) (hr : slotv s.mem W roundsO = BitVec.ofNat 32 R) :
    ∃ s', runBlock isa (zero4 ksOff ++ ctrArgs ++ ([.mov .ebx (.reg .ebp), .alu .add .ebx (imm ksOff),
        .mov .edi (imm 1)] : List Instr)) s = some s' ∧
      s'.mem = Cmac.zero4 s.mem (w64 W + BitVec.ofNat 64 ksOff) ∧
      s'.gpr .eax = C + BitVec.ofNat 32 272 ∧ s'.gpr .ecx = BitVec.ofNat 32 R ∧
      s'.gpr .edx = W + BitVec.ofNat 32 cbOff ∧ s'.gpr .ebx = W + BitVec.ofNat 32 ksOff ∧
      s'.gpr .edi = BitVec.ofNat 32 1 ∧ s'.gpr .ebp = W ∧ s'.gpr .esp = SP ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have z := zero4_fold s.mem W ksOff
  simp only [Nat.reduceAdd, ksOff] at z
  refine ⟨_, by crun [zero4, ctrArgs, E.ebp, L.aW, E.perm.wW, E.perm.wR, hc, hr], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · cmems [z]
  · cregs [hc]
  · cregs [hr]
  · cregs [E.ebp]
  · cregs [E.ebp]
  · cregs []
  · cregs [E.ebp]
  · cregs [E.esp]
  all_goals cmems []

theorem xorArgs_ok {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {s : State} (E : VG.Proof.AesSiv.X86.Env C W SP s) {D : BitVec 32} {n : Nat}
    (hd : slotv s.mem W dataO = D) (hl : slotv s.mem W lenO = BitVec.ofNat 32 n) (hn : n < 2 ^ 32) :
    ∃ s', runBlock isa [.mov .ecx (slot lenO), .alu .and .ecx (imm 15), .mov .edx (.reg .ebp),
        .alu .add .edx (imm ksOff), .mov .edi (slot dataO), .alu .add .edi (slot lenO),
        .alu .sub .edi (.reg .ecx)] s = some s' ∧
      s'.gpr .ecx = BitVec.ofNat 32 (n % 16) ∧ s'.gpr .edx = W + BitVec.ofNat 32 ksOff ∧
      s'.gpr .edi = D + BitVec.ofNat 32 (16 * (n / 16)) ∧
      (∀ r, r ≠ .ecx → r ≠ .edx → r ≠ .edi → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have ha := VG.Proof.AesGcm.X86.and15 (BitVec.ofNat 32 n)
  rw [VG.Proof.AesGcm.X86.toNat_ofNat32 hn] at ha
  have hsub : D + BitVec.ofNat 32 n - BitVec.ofNat 32 (n % 16) = D + BitVec.ofNat 32 (16 * (n / 16)) := by
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg, ofNat_sub32 (Nat.mod_le _ _) hn]
    congr 2; omega
  refine ⟨_, by crun [E.ebp, L.aW, E.perm.wR, hl, hd], ?_, ?_, ?_, fun r h₁ h₂ h₃ => ?_, ?_, ?_, ?_⟩
  · cregs [hl, ha]
  · cregs [E.ebp]
  · cregs [hl, ha, hd, hsub]
  · cregs []
  all_goals cmems []

/-! ## `ctrWhole` -/

theorem rounds_le {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) : 16 * (R + 1) ≤ 240 := by omega

/-- The whole blocks of the data, from the counter `q` at `W + 96`, whose last
32 bits do not wrap around. -/
theorem ctrWhole_ok (v : Ctr32Impl) {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {s : State} (E : VG.Proof.AesSiv.X86.Env C W SP s) {D : BitVec 32} {n : Nat}
    (hD : VG.Proof.AesSiv.X86.Dat C W SP s D n) (hn : n < 2 ^ 32) (hc : slotv s.mem W ctxO = C)
    (hr : slotv s.mem W roundsO = BitVec.ofNat 32 R) (hd : slotv s.mem W dataO = D)
    (hl : slotv s.mem W lenO = BitVec.ofNat 32 n) {q : List Byte}
    (hq : bytesAt s.mem (w64 W + BitVec.ofNat 64 cbOff) 16 = q)
    (hlow : Spec.Siv.beNat q % 2 ^ 32 + n / 16 + 1 ≤ 2 ^ 32) :
    WP isa (ctrWhole v.callee) s fun s' => VG.Proof.AesSiv.X86.Env C W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame (VG.Proof.AesSiv.X86.ctrR W SP D n) s.mem s'.mem ∧
      bytesAt s'.mem (w64 D) n =
        ctrPart (Spec.Siv.ctxCiph s.mem (w64 C) R) q (bytesAt s.mem (w64 D) n) (16 * (n / 16)) ∧
      blockAt s'.mem (w64 W + BitVec.ofNat 64 cbOff) =
        Spec.Gcm.ofBytes (Spec.Siv.be128 (Spec.Siv.beNat q + n / 16)) := by
  have hql : q.length = 16 := by rw [← hq, length_bytesAt]
  have hinc := repeat_inc32 hql (k := n / 16 + 1) (by omega)
  have hcb : blockAt s.mem (w64 W + BitVec.ofNat 64 cbOff) = Spec.Gcm.ofBytes q := by
    rw [blockAt, hq]
  obtain ⟨s₁, run₁, di₁, zf₁, g₁, m₁, rd₁, wr₁⟩ := VG.Proof.AesSiv.X86.whole1_ok L E hl hn
  have E₁ : VG.Proof.AesSiv.X86.Env C W SP s₁ := ⟨by rw [g₁ _ (by decide), E.ebp], by rw [g₁ _ (by decide), E.esp], E.perm.of_eq rd₁ wr₁⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  by_cases h0 : n / 16 = 0
  · refine WP.ite true (VG.Proof.AesSiv.X86.eval_e (by rw [zf₁]; simp [h0])) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    refine ⟨E₁, rd₁, wr₁, by rw [m₁]; exact Frame.refl _ _, ?_, ?_⟩
    · rw [m₁, h0, Nat.mul_zero, ctrPart_zero]
    · rw [m₁, hcb, h0, Nat.add_zero]
      have := hinc 0 (by omega)
      rw [Nat.add_zero] at this
      exact this
  · refine WP.ite false (VG.Proof.AesSiv.X86.eval_e (by rw [zf₁]; simp [h0])) (fun h => by cases h) fun _ => ?_
    have hb : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
    obtain ⟨s₂, run₂, ax₂, cx₂, dx₂, bx₂, g₂, m₂, rd₂, wr₂⟩ := VG.Proof.AesSiv.X86.ctrArgs_ok (C := C) (R := R) (D := D) L E₁ (by rw [m₁]; exact hc)
      (by rw [m₁]; exact hr) (by rw [m₁]; exact hd)
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    have E₂ : VG.Proof.AesSiv.X86.Env C W SP s₂ := ⟨by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), E₁.ebp],
      by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), E₁.esp], E₁.perm.of_eq rd₂ wr₂⟩
    have hD₂ := hD.of_eq (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])
    have mem₂ : s₂.mem = s.mem := by rw [m₂, m₁]
    refine WP.mono (VG.Proof.AesSiv.X86.ctrCall_ok v L E₂ hR (c := cbOff) (by decide) (hD₂.dst hb (by decide)) ax₂ cx₂ dx₂ bx₂
      (by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), di₁])) fun s₃ ⟨E₃, rd₃, wr₃, _, f₃, o₃, c₃⟩ => ?_
    have hRb := VG.Proof.AesSiv.X86.rounds_le hR
    have fT : Frame (VG.Proof.AesSiv.X86.ctrR W SP D n) s.mem s₃.mem := by
      rw [← mem₂]
      exact f₃.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
        · exact ⟨⟨w64 D, n⟩, by simp, Region.sub_prefix hb⟩
        · exact ⟨_, by simp, fun _ h => h⟩
        · exact ⟨_, by simp, fun _ h => h⟩
    refine ⟨E₃, by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁], fT, ?_, ?_⟩
    · -- The whole blocks, then the rest as it was.
      have hc₃ := ctr32_ctrPart (m := s₂.mem) (m' := s₃.mem) (K := w64 C + BitVec.ofNat 64 272)
        (C := w64 W + BitVec.ofNat 64 cbOff) (D := w64 D) (R := R) (q := q) (k := n / 16)
        (fun i hi => by rw [mem₂, hcb]; exact hinc i (by omega)) o₃
      have e := Proof.Cmac.Stream.bytesAt_append s₃.mem (w64 D) (16 * (n / 16)) (n - 16 * (n / 16))
      rw [show 16 * (n / 16) + (n - 16 * (n / 16)) = n by omega] at e
      have e₀ := Proof.Cmac.Stream.bytesAt_append s.mem (w64 D) (16 * (n / 16)) (n - 16 * (n / 16))
      rw [show 16 * (n / 16) + (n - 16 * (n / 16)) = n by omega] at e₀
      have rest : bytesAt s₃.mem (w64 D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) =
          bytesAt s.mem (w64 D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) := by
        rw [← mem₂]
        refine Proof.AesGcm.X86.bytesAt_frame f₃ (fun r hr => ?_) (by have := hD.buf.lt; omega)
        have hsub : Region.Sub ⟨w64 D + BitVec.ofNat 64 (16 * (n / 16)), n - 16 * (n / 16)⟩ ⟨w64 D, n⟩ :=
          Offset.sub_base _ (by omega)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact (hD.buf.w.sub_left hsub).sub_right (Lay.wSub (by decide))
        · exact (Offset.base_disjoint (w64 D) (e := 16 * (n / 16)) (n := n - 16 * (n / 16))
            (k := 16 * (n / 16)) (by omega) (by have := hD.buf.lt; omega)).symm
        · exact (hD.buf.w.sub_left hsub).sub_right (Lay.wSub (by decide))
        · exact (hD.buf.stk.sub_right hsub).symm
      have hpa := ctrPart_append (Spec.Siv.ctxCiph s.mem (w64 C) R) q (bytesAt s.mem (w64 D) (16 * (n / 16)))
        (bytesAt s.mem (w64 D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)))
      rw [length_bytesAt] at hpa
      rw [e, hc₃, rest, e₀, hpa, mem₂]
      rfl
    · rw [c₃, mem₂, hcb]
      exact hinc (n / 16) (by omega)

/-! ## `ctrTail` -/

/-- The last bytes of the data, XORed with the keystream block of the counter
`Q + nb` that `ctrWhole` left. -/
theorem ctrTail_ok (v : Ctr32Impl) {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {s : State} (E : VG.Proof.AesSiv.X86.Env C W SP s) {D : BitVec 32} {n : Nat}
    (hD : VG.Proof.AesSiv.X86.Dat C W SP s D n) (hn : n < 2 ^ 32) (hc : slotv s.mem W ctxO = C)
    (hr : slotv s.mem W roundsO = BitVec.ofNat 32 R) (hd : slotv s.mem W dataO = D)
    (hl : slotv s.mem W lenO = BitVec.ofNat 32 n) {q x : List Byte} (hx : x.length = n)
    (hcb : blockAt s.mem (w64 W + BitVec.ofNat 64 cbOff) =
      Spec.Gcm.ofBytes (Spec.Siv.be128 (Spec.Siv.beNat q + n / 16)))
    (hdat : bytesAt s.mem (w64 D) n = ctrPart (Spec.Siv.ctxCiph s.mem (w64 C) R) q x (16 * (n / 16))) :
    WP isa (ctrTail v.callee) s fun s' => VG.Proof.AesSiv.X86.Env C W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame (VG.Proof.AesSiv.X86.ctrR W SP D n) s.mem s'.mem ∧
      bytesAt s'.mem (w64 D) n = ctrPart (Spec.Siv.ctxCiph s.mem (w64 C) R) q x n := by
  obtain ⟨s₁, run₁, cx₁, zf₁, g₁, m₁, rd₁, wr₁⟩ := VG.Proof.AesSiv.X86.tail1_ok L E hl hn
  have E₁ : VG.Proof.AesSiv.X86.Env C W SP s₁ := ⟨by rw [g₁ _ (by decide), E.ebp], by rw [g₁ _ (by decide), E.esp], E.perm.of_eq rd₁ wr₁⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  by_cases h0 : n % 16 = 0
  · refine WP.ite true (VG.Proof.AesSiv.X86.eval_e (by rw [zf₁]; simp [h0])) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    refine ⟨E₁, rd₁, wr₁, by rw [m₁]; exact Frame.refl _ _, ?_⟩
    rw [m₁, hdat, show 16 * (n / 16) = n by omega]
  · refine WP.ite false (VG.Proof.AesSiv.X86.eval_e (by rw [zf₁]; simp [h0])) (fun h => by cases h) fun _ => ?_
    obtain ⟨s₂, run₂, m₂, ax₂, cx₂, dx₂, bx₂, di₂, bp₂, sp₂, rd₂, wr₂⟩ := VG.Proof.AesSiv.X86.tailArgs_ok' (R := R) L E₁
      (by rw [m₁]; exact hc) (by rw [m₁]; exact hr)
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    have E₂ : VG.Proof.AesSiv.X86.Env C W SP s₂ := ⟨bp₂, sp₂, E₁.perm.of_eq rd₂ wr₂⟩
    refine WP.seq (WP.mono (VG.Proof.AesSiv.X86.ctrCall_ok v L E₂ hR (c := cbOff) (by decide) (n := 1)
      (VG.Proof.AesSiv.X86.dstW L E₂.perm (c := cbOff) (q := ksOff) (by decide) (by decide) (by decide)) ax₂ cx₂ dx₂ bx₂ di₂)
      fun s₃ ⟨E₃, rd₃, wr₃, _, f₃, o₃, _⟩ => ?_)
    have hRb := VG.Proof.AesSiv.X86.rounds_le hR
    have hb : 16 * (n / 16) < n := by omega
    have eK : w64 (W + BitVec.ofNat 32 ksOff) = w64 W + BitVec.ofNat 64 ksOff := L.aW (by decide)
    -- The keystream block.
    have f₂ : Frame [⟨w64 W + BitVec.ofNat 64 ksOff, 16⟩] s.mem s₂.mem := by
      rw [m₂, m₁]; exact Cmac.frame_store4 _ _ _ _ _
    have cb₂ : blockAt s₂.mem (w64 W + BitVec.ofNat 64 cbOff) =
        Spec.Gcm.ofBytes (Spec.Siv.be128 (Spec.Siv.beNat q + n / 16)) := by
      rw [blockAt, Proof.AesGcm.X86.bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by decide)) (by decide) (by decide))
        (by decide), ← blockAt, hcb]
    have sch₂ : bytesAt s₂.mem (w64 C + BitVec.ofNat 64 272) (16 * (R + 1)) =
        bytesAt s.mem (w64 C + BitVec.ofNat 64 272) (16 * (R + 1)) :=
      Proof.AesGcm.X86.bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.c_w' (by omega) (by decide)) (by omega)
    have hks : bytesAt s₃.mem (w64 W + BitVec.ofNat 64 ksOff) 16 =
        Proof.Siv.ksBlock (Spec.Siv.ctxCiph s.mem (w64 C) R) q (n / 16) := by
      rw [eK] at o₃
      have hx₃ := Proof.AesCcm.ctr32_bytes (m := s₂.mem) (m' := s₃.mem) (C := w64 W + BitVec.ofNat 64 cbOff)
        (D := w64 W + BitVec.ofNat 64 ksOff) (nb := 1) o₃
      rw [Nat.mul_one, m₂, Cmac.zero4_bytes, ← m₂, cb₂, xorKs_zeros, sch₂,
        Proof.Cmac.aesWith_bytes _ _ (length_be128 _)] at hx₃
      rw [hx₃]; rfl
    -- The arguments of the XOR.
    have f₂₃ : Frame [⟨w64 W + BitVec.ofNat 64 ksOff, 32⟩, ⟨w64 W + BitVec.ofNat 64 256, 2048⟩, below SP 56]
        s₂.mem s₃.mem := by
      rw [eK] at f₃
      exact f₃.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
        · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
        · exact ⟨_, by simp, fun _ h => h⟩
        · exact ⟨_, by simp, fun _ h => h⟩
    have f₀₃ : Frame [⟨w64 W + BitVec.ofNat 64 ksOff, 32⟩, ⟨w64 W + BitVec.ofNat 64 256, 2048⟩, below SP 56]
        s.mem s₃.mem :=
      (f₂.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩).trans f₂₃
    have sl₃ : ∀ o, 176 ≤ o → o + 4 ≤ 256 → slotv s₃.mem W o = slotv s.mem W o := fun o h₁ h₂ =>
      f₀₃.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact Lay.w_w (.inr (by simp only [ksOff]; omega)) (by omega) (by decide)
        · exact Lay.w_w (.inl h₂) (by omega) (by decide)
        · exact (L.stk_w' (by omega)).symm) (by decide)
    obtain ⟨s₄, run₄, cx₄, dx₄, di₄, g₄, m₄, rd₄, wr₄⟩ := VG.Proof.AesSiv.X86.xorArgs_ok (D := D) L E₃
      (by rw [sl₃ _ (by decide) (by decide)]; exact hd) (by rw [sl₃ _ (by decide) (by decide)]; exact hl) hn
    refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
    have rd₀₄ : s₄.rd = s.rd := by rw [rd₄, rd₃, rd₂, rd₁]
    have wr₀₄ : s₄.wr = s.wr := by rw [wr₄, wr₃, wr₂, wr₁]
    have hwD : D.toNat + n ≤ 2 ^ 32 := hD.buf.wrap
    have eD : w64 (D + BitVec.ofNat 32 (16 * (n / 16))) = w64 D + BitVec.ofNat 64 (16 * (n / 16)) :=
      Buf.ptr (by omega)
    have hsub : Region.Sub ⟨w64 D + BitVec.ofNat 64 (16 * (n / 16)), n % 16⟩ ⟨w64 D, n⟩ :=
      Offset.sub_base _ (by omega)
    have xp : XorPre s₄ (W + BitVec.ofNat 32 ksOff) (D + BitVec.ofNat 32 (16 * (n / 16))) (n % 16) := by
      refine ⟨dx₄, di₄, cx₄, by omega, by omega, by rw [L.nW (by decide)]; have := L.fw; simp only [ksOff]; omega,
        by rw [Proof.AesGcm.X86.toNat_add32 (by omega)]; omega, ?_, ?_, ?_⟩
      · rw [eK, rd₀₄, wr₀₄]; exact Proof.AesGcm.X86.covers_left (E.perm.wC (by simp only [ksOff]; omega))
      · rw [wr₀₄, eD]; exact covers_off hD.wr (by omega) (by have := hD.buf.lt; omega)
      · rw [eK, eD]; exact ((hD.buf.w.sub_left hsub).sub_right (Lay.wSub (by simp only [ksOff]; omega))).symm
    refine WP.mono (xorLoop_ok s₄ xp) fun s₅ x₅ => ?_
    have hm₅ := x₅.mem
    rw [eK, eD] at hm₅
    have hxl := length_xorBytes s₄.mem (w64 D + BitVec.ofNat 64 (16 * (n / 16)))
      (w64 W + BitVec.ofNat 64 ksOff) (n % 16)
    have fw : Frame [⟨w64 D + BitVec.ofNat 64 (16 * (n / 16)), n % 16⟩] s₄.mem s₅.mem := by
      rw [hm₅]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [hxl]; exact Region.contains_self _ _)
    refine ⟨⟨by rw [x₅.other _ (by decide) (by decide) (by decide) (by decide) (by decide),
        g₄ _ (by decide) (by decide) (by decide), E₃.ebp],
      by rw [x₅.other _ (by decide) (by decide) (by decide) (by decide) (by decide),
        g₄ _ (by decide) (by decide) (by decide), E₃.esp], E₃.perm.of_eq (x₅.rd.trans rd₄) (x₅.wr.trans wr₄)⟩,
      by rw [x₅.rd, rd₀₄], by rw [x₅.wr, wr₀₄], ?_, ?_⟩
    · refine ((f₀₃.sub fun r hr => ?_).trans (by rw [← m₄]; exact Frame.refl _ _)).trans (fw.sub fun r hr => ?_)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨⟨w64 D, n⟩, by simp, hsub⟩
    · have hcl : ∀ y, (Spec.Siv.ctxCiph s.mem (w64 C) R y).length = 16 :=
        fun y => Proof.Cmac.aesWith_length _ _ y
      have d₄ : bytesAt s₄.mem (w64 D) x.length = ctrPart (Spec.Siv.ctxCiph s.mem (w64 C) R) q x
          (16 * (n / 16)) := by
        rw [hx, m₄, Proof.AesGcm.X86.bytesAt_frame f₀₃ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact hD.buf.w.sub_right (Lay.wSub (by decide))
          · exact hD.buf.w.sub_right (Lay.wSub (by decide))
          · exact hD.buf.stk.symm) (by have := hD.buf.lt; omega), hdat]
      have st := ctrPart_step (Spec.Siv.ctxCiph s.mem (w64 C) R) hcl q x s₄.mem (w64 D)
        (i := n / 16) (n := n % 16) (by have := hD.buf.lt; omega) (by omega) (by omega) d₄
      have xb : xorBytes s₄.mem (w64 D + BitVec.ofNat 64 (16 * (n / 16))) (w64 W + BitVec.ofNat 64 ksOff) (n % 16) =
          Spec.Cmac.xor (bytesAt s₄.mem (w64 D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16))
            ((Proof.Siv.ksBlock (Spec.Siv.ctxCiph s.mem (w64 C) R) q (n / 16)).take (n % 16)) := by
        have tk := take_bytesAt s₄.mem (w64 W + BitVec.ofNat 64 ksOff) (a := n % 16) (b := 16 - n % 16)
        rw [show n % 16 + (16 - n % 16) = 16 by omega] at tk
        rw [xorBytes, ← tk, m₄, hks]
        rfl
      rw [hx] at st
      rw [hm₅, xb, st, show 16 * (n / 16) + n % 16 = n by omega]

/-! ## `ctr` -/

theorem ctxCiph_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {C : Addr}
    (hd : ∀ r ∈ rs, (⟨C, 512⟩ : Region).Disjoint r) {R : Nat} (hR : 16 * (R + 1) ≤ 240) :
    Spec.Siv.ctxCiph m' C R = Spec.Siv.ctxCiph m C R := by
  unfold Spec.Siv.ctxCiph Spec.Siv.schedCiph
  rw [Proof.AesGcm.X86.bytesAt_frame hf (p := C + 272)
    (fun r hr => (hd r hr).sub_left (Offset.sub_base C (d := 272) (n := 16 * (R + 1)) (by omega))) (by omega)]

theorem ctrR_c {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {s : State} {D : BitVec 32} {n : Nat} (hD : VG.Proof.AesSiv.X86.Dat C W SP s D n) :
    ∀ r ∈ VG.Proof.AesSiv.X86.ctrR W SP D n, (⟨w64 C, 512⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.c_w.sub_right (Lay.wSub (by decide))
  · exact L.c_w.sub_right (Lay.wSub (by decide))
  · exact L.stk_c.symm
  · exact hD.c

/-- The slots CTR keeps. -/
theorem ctrR_slot {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {s : State} {D : BitVec 32} {n : Nat}
    (hD : VG.Proof.AesSiv.X86.Dat C W SP s D n) {m m' : Mem} (hf : Frame (VG.Proof.AesSiv.X86.ctrR W SP D n) m m') {o : Nat} (h₁ : 112 ≤ o)
    (h₂ : o + 4 ≤ 256) : slotv m' W o = slotv m W o :=
  hf.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Lay.w_w (.inr (by simp only [ksOff]; omega)) (by omega) (by decide)
    · exact Lay.w_w (.inl h₂) (by omega) (by decide)
    · exact (L.stk_w' (by omega)).symm
    · exact (hD.buf.w.sub_right (Lay.wSub (d := o) (n := 4) (by omega))).symm) (by decide)

/-- `ctr`: the data XORed with CTR's keystream from the counter `q` at
`W + 96`, whose last 32 bits are below `2³¹`. -/
theorem ctr_ok (v : Ctr32Impl) {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {s : State} (E : VG.Proof.AesSiv.X86.Env C W SP s) {D : BitVec 32} {n : Nat}
    (hD : VG.Proof.AesSiv.X86.Dat C W SP s D n) (hn : n < 2 ^ 32) (hc : slotv s.mem W ctxO = C)
    (hr : slotv s.mem W roundsO = BitVec.ofNat 32 R) (hd : slotv s.mem W dataO = D)
    (hl : slotv s.mem W lenO = BitVec.ofNat 32 n) {q : List Byte}
    (hq : bytesAt s.mem (w64 W + BitVec.ofNat 64 cbOff) 16 = q) (hlow : Spec.Siv.beNat q % 2 ^ 32 < 2 ^ 31) :
    WP isa (ctr v.callee) s fun s' => VG.Proof.AesSiv.X86.Env C W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame (VG.Proof.AesSiv.X86.ctrR W SP D n) s.mem s'.mem ∧
      bytesAt s'.mem (w64 D) n = Spec.Siv.ctr (Spec.Siv.ctxCiph s.mem (w64 C) R) q (bytesAt s.mem (w64 D) n) := by
  refine WP.seq (WP.mono (VG.Proof.AesSiv.X86.ctrWhole_ok v L hR E hD hn hc hr hd hl hq (by omega))
    fun s₄ ⟨E₄, rd₄, wr₄, f₄, d₄, cb₄⟩ => ?_)
  have hRb := VG.Proof.AesSiv.X86.rounds_le hR
  have k₄ : Spec.Siv.ctxCiph s₄.mem (w64 C) R = Spec.Siv.ctxCiph s.mem (w64 C) R :=
    VG.Proof.AesSiv.X86.ctxCiph_frame f₄ (VG.Proof.AesSiv.X86.ctrR_c L hD) hRb
  have sl := fun {o : Nat} (h₁ : 112 ≤ o) (h₂ : o + 4 ≤ 256) => VG.Proof.AesSiv.X86.ctrR_slot L hD f₄ h₁ h₂
  refine WP.mono (VG.Proof.AesSiv.X86.ctrTail_ok v L hR E₄ (hD.of_eq rd₄ wr₄) hn (by rw [sl (by decide) (by decide)]; exact hc)
    (by rw [sl (by decide) (by decide)]; exact hr) (by rw [sl (by decide) (by decide)]; exact hd)
    (by rw [sl (by decide) (by decide)]; exact hl) (x := bytesAt s.mem (w64 D) n) (length_bytesAt _ _ _) cb₄
    (by rw [k₄]; exact d₄)) fun s₅ ⟨E₅, rd₅, wr₅, f₅, d₅⟩ => ⟨E₅, by rw [rd₅, rd₄], by rw [wr₅, wr₄], f₄.trans f₅, ?_⟩
  rw [d₅, k₄]
  exact ctrPart_all _ (fun y => Proof.Cmac.aesWith_length _ _ y) q _ (by rw [length_bytesAt])

end VG.Proof.AesSiv.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.X86.CtrCT`. -/
section

/-!
# AES-SIV on x86: CTR is constant time

Untrusted: everything here is checked by Lean. The branches of `ctr` are on
the length of the data, and the addresses on `ebp` and the data's address
(pinned where the XOR uses them); the calls of `vg_aes_ctr32` are constant
time by their contract.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesSiv.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4 xorLoop)
open VG.Proof.AesGcm.X86 (w64 slotv CT xorLoop_ct)

/-- What CTR starts from, but the counter: the data and its slots. -/
structure CtrPre (C W SP : BitVec 32) (R : Nat) (D : BitVec 32) (n : Nat) (s : State) : Prop where
  env : VG.Proof.AesSiv.X86.Env C W SP s
  dat : VG.Proof.AesSiv.X86.Dat C W SP s D n
  n32 : n < 2 ^ 32
  ctx : slotv s.mem W ctxO = C
  rounds : slotv s.mem W roundsO = BitVec.ofNat 32 R
  data : slotv s.mem W dataO = D
  len : slotv s.mem W lenO = BitVec.ofNat 32 n

theorem ctrWhole_ct (v : Ctr32Impl) {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {D : BitVec 32} {n : Nat} :
    CT (VG.Proof.AesSiv.X86.CtrPre C W SP R D n) (ctrWhole v.callee) := by
  refine CT.block_seq [.ebp] (VG.Proof.AesSiv.X86.pin_ebp fun s h => h.env.ebp) (by taint_decide)
    (fun s hs => VG.Proof.AesSiv.X86.whole1_ok L hs.env hs.len hs.n32) ?_
  refine CT.ite (decide (n / 16 = 0)) (fun s ⟨_, _, _, zf, _⟩ => VG.Proof.AesSiv.X86.eval_e zf) (fun _ => CT.nil) (fun _ => ?_)
  refine CT.block_seq [.ebp] (VG.Proof.AesSiv.X86.pin_ebp fun s₁ ⟨s, hs, _, _, g, _⟩ => by rw [g _ (by decide), hs.env.ebp])
    (by taint_decide) (fun s₁ ⟨s, hs, _, _, g, m, rd, wr⟩ =>
      VG.Proof.AesSiv.X86.ctrArgs_ok (C := C) (R := R) (D := D) L ⟨by rw [g _ (by decide), hs.env.ebp],
        by rw [g _ (by decide), hs.env.esp], hs.env.perm.of_eq rd wr⟩
        (by rw [m]; exact hs.ctx) (by rw [m]; exact hs.rounds) (by rw [m]; exact hs.data)) ?_
  exact VG.Proof.AesSiv.X86.ctrCall_ct v L hR (c := cbOff) (by decide) (D := D) (n := n / 16)
    fun s₂ ⟨s₁, ⟨s, hs, di₁, _, g₁, _, rd₁, wr₁⟩, ax, cx, dx, bx, g₂, _, rd₂, wr₂⟩ =>
      ⟨⟨by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), g₁ _ (by decide), hs.env.ebp],
        by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), g₁ _ (by decide), hs.env.esp],
        hs.env.perm.of_eq (rd₂.trans rd₁) (wr₂.trans wr₁)⟩,
        (hs.dat.of_eq (rd₂.trans rd₁) (wr₂.trans wr₁)).dst (Nat.mul_div_le n 16) (by decide),
        ax, cx, dx, bx, by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), di₁]⟩

theorem tailArgs_ct {W : BitVec 32} {I : State → Prop} (hI : ∀ s, I s → s.gpr .ebp = W) :
    CT I (.block (zero4 ksOff ++ ctrArgs ++ ([.mov .ebx (.reg .ebp), .alu .add .ebx (imm ksOff),
      .mov .edi (imm 1)] : List Instr))) :=
  CT.taint [.ebp] (VG.Proof.AesSiv.X86.pin_ebp hI) (by taint_decide)

theorem ctrTail_ct (v : Ctr32Impl) {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {D : BitVec 32} {n : Nat} :
    CT (VG.Proof.AesSiv.X86.CtrPre C W SP R D n) (ctrTail v.callee) := by
  refine CT.block_seq [.ebp] (VG.Proof.AesSiv.X86.pin_ebp fun s h => h.env.ebp) (by taint_decide)
    (fun s hs => VG.Proof.AesSiv.X86.tail1_ok L hs.env hs.len hs.n32) ?_
  refine CT.ite (decide (n % 16 = 0)) (fun s ⟨_, _, _, zf, _⟩ => VG.Proof.AesSiv.X86.eval_e zf) (fun _ => CT.nil) (fun _ => ?_)
  -- After the call: the data and its slots.
  have pre₁ : ∀ s₁, (∃ s, VG.Proof.AesSiv.X86.CtrPre C W SP R D n s ∧ s₁.gpr .ecx = BitVec.ofNat 32 (n % 16) ∧
      s₁.zf = some (decide (n % 16 = 0)) ∧ (∀ r, r ≠ .ecx → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr) → VG.Proof.AesSiv.X86.CtrPre C W SP R D n s₁ := fun s₁ ⟨s, hs, _, _, g, m, rd, wr⟩ =>
    ⟨⟨by rw [g _ (by decide), hs.env.ebp], by rw [g _ (by decide), hs.env.esp], hs.env.perm.of_eq rd wr⟩,
      hs.dat.of_eq rd wr, hs.n32, by rw [m]; exact hs.ctx, by rw [m]; exact hs.rounds, by rw [m]; exact hs.data,
      by rw [m]; exact hs.len⟩
  refine CT.seq (J := fun s₂ => ∃ s₁, VG.Proof.AesSiv.X86.CtrPre C W SP R D n s₁ ∧
      s₂.mem = Cmac.zero4 s₁.mem (w64 W + BitVec.ofNat 64 ksOff) ∧
      s₂.gpr .eax = C + BitVec.ofNat 32 272 ∧ s₂.gpr .ecx = BitVec.ofNat 32 R ∧
      s₂.gpr .edx = W + BitVec.ofNat 32 cbOff ∧ s₂.gpr .ebx = W + BitVec.ofNat 32 ksOff ∧
      s₂.gpr .edi = BitVec.ofNat 32 1 ∧ s₂.gpr .ebp = W ∧ s₂.gpr .esp = SP ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr)
    (VG.Proof.AesSiv.X86.tailArgs_ct fun s₁ h₁ => (pre₁ s₁ h₁).env.ebp)
    (fun s₁ h₁ => let ⟨s₂, run₂, h₂⟩ := VG.Proof.AesSiv.X86.tailArgs_ok' (R := R) L (pre₁ s₁ h₁).env (pre₁ s₁ h₁).ctx (pre₁ s₁ h₁).rounds
      WP.of_runBlock ⟨s₂, run₂, s₁, pre₁ s₁ h₁, h₂⟩) ?_
  refine CT.seq (J := fun s₃ => VG.Proof.AesSiv.X86.CtrPre C W SP R D n s₃)
    (VG.Proof.AesSiv.X86.ctrCall_ct v L hR (c := cbOff) (by decide) (D := W + BitVec.ofNat 32 ksOff) (n := 1)
      fun s₂ ⟨s₁, h₁, _, ax, cx, dx, bx, di, bp, sp, rd, wr⟩ =>
        have P₂ := h₁.env.perm.of_eq rd wr
        ⟨⟨bp, sp, P₂⟩, VG.Proof.AesSiv.X86.dstW L P₂ (by decide) (by decide) (by decide), ax, cx, dx, bx, di⟩)
    (fun s₂ ⟨s₁, h₁, m₂, ax, cx, dx, bx, di, bp, sp, rd, wr⟩ =>
      have P₂ := h₁.env.perm.of_eq rd wr
      WP.mono (VG.Proof.AesSiv.X86.ctrCall_ok v L ⟨bp, sp, P₂⟩ hR (c := cbOff) (by decide) (n := 1)
        (VG.Proof.AesSiv.X86.dstW L P₂ (by decide) (by decide) (by decide)) ax cx dx bx di) fun s₃ ⟨E₃, rd₃, wr₃, _, f₃, _⟩ => by
        have f : Frame (VG.Proof.AesSiv.X86.ctrR W SP D n) s₁.mem s₃.mem := by
          refine (show Frame (VG.Proof.AesSiv.X86.ctrR W SP D n) s₁.mem s₂.mem by
            rw [m₂]; exact (Cmac.frame_store4 _ _ _ _ _).sub fun r hr => by
              simp only [List.mem_singleton] at hr; subst hr
              exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩).trans ?_
          rw [L.aW (o := ksOff) (by decide)] at f₃
          exact f₃.sub fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl | rfl
            · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
            · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
            · exact ⟨_, by simp, fun _ h => h⟩
            · exact ⟨_, by simp, fun _ h => h⟩
        have sl := fun {o : Nat} (a : 112 ≤ o) (b : o + 4 ≤ 256) => VG.Proof.AesSiv.X86.ctrR_slot L h₁.dat f a b
        exact ⟨E₃, h₁.dat.of_eq (rd₃.trans rd) (wr₃.trans wr), h₁.n32,
          by rw [sl (by decide) (by decide)]; exact h₁.ctx, by rw [sl (by decide) (by decide)]; exact h₁.rounds,
          by rw [sl (by decide) (by decide)]; exact h₁.data, by rw [sl (by decide) (by decide)]; exact h₁.len⟩) ?_
  refine CT.block_seq [.ebp] (VG.Proof.AesSiv.X86.pin_ebp fun s h => h.env.ebp) (by taint_decide)
    (fun s hs => VG.Proof.AesSiv.X86.xorArgs_ok L hs.env hs.data hs.len hs.n32) ?_
  exact xorLoop_ct (VG.Proof.AesSiv.X86.pin3 fun s ⟨_, _, cx, dx, di, _⟩ => ⟨di, dx, cx⟩)

/-- `ctr` is constant time from the data and its slots, whatever the counter. -/
theorem ctr_ct (v : Ctr32Impl) {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {D : BitVec 32} {n : Nat} :
    CT (fun s => VG.Proof.AesSiv.X86.CtrPre C W SP R D n s ∧ Spec.Siv.beNat (bytesAt s.mem (w64 W + BitVec.ofNat 64 cbOff) 16) % 2 ^ 32 <
      2 ^ 31) (ctr v.callee) :=
  CT.seq (J := VG.Proof.AesSiv.X86.CtrPre C W SP R D n) ((VG.Proof.AesSiv.X86.ctrWhole_ct v L hR).mono fun _ h => h.1)
    (fun s ⟨h, hlow⟩ => WP.mono (VG.Proof.AesSiv.X86.ctrWhole_ok v L hR h.env h.dat h.n32 h.ctx h.rounds h.data h.len rfl (by have := h.n32; omega))
      fun s₄ ⟨E₄, rd₄, wr₄, f₄, _⟩ =>
        have sl := fun {o : Nat} (h₁ : 112 ≤ o) (h₂ : o + 4 ≤ 256) => VG.Proof.AesSiv.X86.ctrR_slot L h.dat f₄ h₁ h₂
        ⟨E₄, h.dat.of_eq rd₄ wr₄, h.n32, by rw [sl (by decide) (by decide)]; exact h.ctx,
          by rw [sl (by decide) (by decide)]; exact h.rounds, by rw [sl (by decide) (by decide)]; exact h.data,
          by rw [sl (by decide) (by decide)]; exact h.len⟩)
    (VG.Proof.AesSiv.X86.ctrTail_ct v L hR)

end VG.Proof.AesSiv.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.X86.S2v`. -/
section

/-!
# AES-SIV on x86: S2V over the associated data

Untrusted: everything here is checked by Lean. After the entry, every piece
writes only parts of `W` (`wR`), the stack below `SP` and, from counter mode
on, the data (`ext`): the slots, our caller's registers saved in `W`, and
everything outside those keep their values (`Kept`). S2V starts with
`D = AES-CMAC(K1, <zero>)` (`start_ok`); then, for each component `S` a
descriptor at `A` lists (`compA`, `compL`), `D = dbl(D) ⊕ AES-CMAC(K1, S)`
(`adBody_ok`), until none is left (`s2vAds_ok`, with the invariant `AInv`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesSiv.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4)
open VG.Proof.AesGcm.X86 (w64 toNat_ofNat32 toNat_add32 slotv zero4_fold length_bytesAt ofNat_sub32
  readW_writeW_off SavedAt savedR CT covers_left)

/-! ## The components of associated data -/

/-- The address of the `i`-th component, from its descriptor at `A + 8 i`. -/
abbrev compA (m : Mem) (A : BitVec 32) (i : Nat) : BitVec 32 := m.readW (w64 A + BitVec.ofNat 64 (8 * i)) 32

/-- The length of the `i`-th component. -/
abbrev compL (m : Mem) (A : BitVec 32) (i : Nat) : Nat := (m.readW (w64 A + BitVec.ofNat 64 (8 * i + 4)) 32).toNat

theorem listed_getElem (m : Mem) (A : BitVec 32) {N i : Nat} (hi : i < N) :
    (Sig.listed 32 m .u8 (w64 A) N)[i]'(by simp [Sig.listed, hi]) = ⟨w64 (VG.Proof.AesSiv.X86.compA m A i), VG.Proof.AesSiv.X86.compL m A i⟩ := by
  simp only [Sig.listed, List.getElem_map, List.getElem_range, Elem.size, Nat.mul_one, VG.Proof.AesSiv.X86.compA, VG.Proof.AesSiv.X86.compL,
    VG.Proof.AesSiv.X86.add_ofNat_assoc]
  rw [Nat.mul_comm i 8]

theorem comp_mem (m : Mem) (A : BitVec 32) {N i : Nat} (hi : i < N) :
    (⟨w64 (VG.Proof.AesSiv.X86.compA m A i), VG.Proof.AesSiv.X86.compL m A i⟩ : Region) ∈ Sig.listed 32 m .u8 (w64 A) N := by
  rw [← VG.Proof.AesSiv.X86.listed_getElem m A hi]; exact List.getElem_mem _

theorem components_take_succ (m : Mem) (A : BitVec 32) {N i : Nat} (hi : i < N) :
    (Spec.Siv.components 32 m (w64 A) N).take (i + 1) =
      (Spec.Siv.components 32 m (w64 A) N).take i ++ [bytesAt m (w64 (VG.Proof.AesSiv.X86.compA m A i)) (VG.Proof.AesSiv.X86.compL m A i)] := by
  have hl : i < (Spec.Siv.components 32 m (w64 A) N).length := by simp [Spec.Siv.components, Sig.listed, hi]
  rw [List.take_add_one, List.getElem?_eq_getElem hl, Option.toList_some]
  simp only [Spec.Siv.components, List.getElem_map, VG.Proof.AesSiv.X86.listed_getElem m A hi]

theorem components_take_all (m : Mem) (A : BitVec 32) (N : Nat) :
    (Spec.Siv.components 32 m (w64 A) N).take N = Spec.Siv.components 32 m (w64 A) N :=
  List.take_of_length_le (by simp [Spec.Siv.components, Sig.listed])

theorem s2vAcc_snoc (mac : List Byte → List Byte) (xs : List (List Byte)) (x : List Byte) :
    Spec.Siv.s2vAcc mac (xs ++ [x]) = Spec.Siv.s2vStep mac (Spec.Siv.s2vAcc mac xs) x := by
  simp [Spec.Siv.s2vAcc, List.foldl_append]

/-! ## What the pieces keep -/

/-- The parts of `W` the pieces write, and the stack below `SP`. -/
abbrev wR (W SP : BitVec 32) : List Region := [VG.Proof.AesSiv.X86.wA W, VG.Proof.AesSiv.X86.wB W, VG.Proof.AesSiv.X86.wV W, VG.Proof.AesSiv.X86.wS W, VG.Proof.AesSiv.X86.wC W, below SP 56]

/-- Since the entry from `s₀`: the environment, the slots and our caller's
registers in `W`, and the memory outside `W`, the stack below `SP` and the
regions `ext` as on entry. -/
structure Kept (s₀ : State) (C W SP : BitVec 32) (R : Nat) (D : BitVec 32) (n : Nat) (ext : List Region)
    (s : State) : Prop where
  env : VG.Proof.AesSiv.X86.Env C W SP s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  slots : VG.Proof.AesSiv.X86.Slots W C R D n s.mem
  saved : SavedAt s.mem W s₀
  big : Frame ([⟨w64 W + BitVec.ofNat 64 16, 2560⟩, below SP 56] ++ ext) s₀.mem s.mem

/-- A piece that writes parts of `W` the pieces write, the stack below `SP`,
or the regions `ext` (apart from `W`) keeps `Kept`. -/
theorem Kept.step {s₀ : State} {C W SP : BitVec 32} {R : Nat} {D : BitVec 32} {n : Nat} {ext : List Region}
    (L : VG.Proof.AesSiv.X86.Lay C W SP) (hext : ∀ r ∈ ext, r.Disjoint ⟨w64 W + BitVec.ofNat 64 128, 2448⟩) {s s' : State}
    (h : VG.Proof.AesSiv.X86.Kept s₀ C W SP R D n ext s) (E : VG.Proof.AesSiv.X86.Env C W SP s') (rd : s'.rd = s.rd) (wr : s'.wr = s.wr)
    {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hs : ∀ r ∈ rs, (∃ r' ∈ VG.Proof.AesSiv.X86.wR W SP, Region.Sub r r') ∨ ∃ r' ∈ ext, Region.Sub r r') :
    VG.Proof.AesSiv.X86.Kept s₀ C W SP R D n ext s' := by
  have kept : ∀ {d k : Nat}, (128 ≤ d ∧ d + k ≤ 144 ∨ 176 ≤ d ∧ d + k ≤ 184 ∨ 192 ≤ d ∧ d + k ≤ 200) →
      ∀ r ∈ rs, (⟨w64 W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun {d k} hd r hr => by
    rcases hs r hr with ⟨r', hr', hsub⟩ | ⟨r', hr', hsub⟩
    · refine Region.Disjoint.sub_right ?_ hsub
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl
      · exact Lay.w_w (.inr (by omega)) (by omega) (by decide)
      · exact Lay.w_w (by omega) (by omega) (by decide)
      · exact Lay.w_w (by omega) (by omega) (by decide)
      · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
      · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
      · exact (L.stk_w' (by omega)).symm
    · exact ((hext r' hr').sub_right (Offset.sub _ (by omega) (by omega))).symm.sub_right hsub
  have k : ∀ o, (128 ≤ o ∧ o + 4 ≤ 144 ∨ 176 ≤ o ∧ o + 4 ≤ 184 ∨ 192 ≤ o ∧ o + 4 ≤ 200) →
      slotv s'.mem W o = slotv s.mem W o := fun o ho =>
    hf.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (kept ho) (by decide)
  refine ⟨E, by rw [rd, h.rd], by rw [wr, h.wr], ⟨?_, ?_, ?_, ?_⟩, ?_, h.big.trans (hf.sub fun r hr => ?_)⟩
  · rw [k _ (by decide)]; exact h.slots.ctx
  · rw [k _ (by decide)]; exact h.slots.rounds
  · rw [k _ (by decide)]; exact h.slots.data
  · rw [k _ (by decide)]; exact h.slots.len
  · exact h.saved.frame hf fun r hr => kept (.inl ⟨Nat.le_refl _, Nat.le_refl _⟩) r hr
  · rcases hs r hr with ⟨r', hr', hsub⟩ | ⟨r', hr', hsub⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨⟨w64 W + BitVec.ofNat 64 16, 2560⟩, by simp, fun _ h => Region.sub_prefix (by decide) _ (hsub _ h)⟩
      · exact ⟨⟨w64 W + BitVec.ofNat 64 16, 2560⟩, by simp, fun _ h => Offset.sub _ (by decide) (by decide) _ (hsub _ h)⟩
      · exact ⟨⟨w64 W + BitVec.ofNat 64 16, 2560⟩, by simp, fun _ h => Offset.sub _ (by decide) (by decide) _ (hsub _ h)⟩
      · exact ⟨⟨w64 W + BitVec.ofNat 64 16, 2560⟩, by simp, fun _ h => Offset.sub _ (by decide) (by decide) _ (hsub _ h)⟩
      · exact ⟨⟨w64 W + BitVec.ofNat 64 16, 2560⟩, by simp, fun _ h => Offset.sub _ (by decide) (by decide) _ (hsub _ h)⟩
      · exact ⟨_, by simp, hsub⟩
    · exact ⟨r', List.mem_append_right _ hr', hsub⟩

/-- The bytes of a region apart from `W`, the stack below `SP` and `ext` are
as on entry. -/
theorem Kept.bytes {s₀ : State} {C W SP : BitVec 32} {R : Nat} {D : BitVec 32} {n : Nat} {ext : List Region}
    {s : State} (h : VG.Proof.AesSiv.X86.Kept s₀ C W SP R D n ext s) {p : Addr} {k : Nat}
    (hw : (⟨p, k⟩ : Region).Disjoint ⟨w64 W, 2576⟩) (hs : (below SP 56).Disjoint ⟨p, k⟩)
    (he : ∀ r ∈ ext, (⟨p, k⟩ : Region).Disjoint r) (hk : k ≤ 2 ^ 64) : bytesAt s.mem p k = bytesAt s₀.mem p k :=
  Proof.AesGcm.X86.bytesAt_frame h.big (fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons] at hr
    rcases hr with rfl | rfl | hr
    · exact hw.sub_right (Lay.wSub (by decide))
    · exact hs.symm
    · exact he r hr) hk

/-- The context's PRF, after code that writes apart from its 512 bytes. -/
theorem ctxMac_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {C : Addr}
    (hd : ∀ r ∈ rs, (⟨C, 512⟩ : Region).Disjoint r) {R : Nat} (hR : R ≤ 14) :
    Spec.Siv.ctxMac m' C R = Spec.Siv.ctxMac m C R := by
  have e : ∀ {d k : Nat}, d + k ≤ 512 → bytesAt m' (C + BitVec.ofNat 64 d) k = bytesAt m (C + BitVec.ofNat 64 d) k :=
    fun hk => Proof.AesGcm.X86.bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Offset.sub_base _ hk)) (by omega)
  have s0 := e (d := 0) (k := 16 * (R + 1)) (by omega)
  rw [BitVec.add_zero] at s0
  simp only [Spec.Siv.ctxMac, Spec.Siv.schedCiph, s0]
  rw [show (240 : Addr) = BitVec.ofNat 64 240 from rfl, show (256 : Addr) = BitVec.ofNat 64 256 from rfl,
    e (by decide), e (by decide)]

/-! ## S2V's first state -/

/-- What S2V of the associated data needs of the entry state `s₀`: the `N`
descriptors at `A` and the components they list, readable, apart from `W`
and the stack below `SP`. -/
structure AdCtx (s₀ : State) (C W SP A : BitVec 32) (R N : Nat) : Prop where
  lay : VG.Proof.AesSiv.X86.Lay C W SP
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  desc : VG.Proof.AesSiv.X86.Buf W SP s₀ A (8 * N)
  comps : ∀ i < N, VG.Proof.AesSiv.X86.Buf W SP s₀ (VG.Proof.AesSiv.X86.compA s₀.mem A i) (VG.Proof.AesSiv.X86.compL s₀.mem A i)
  N32 : N < 2 ^ 32

/-- The context's PRF while `Kept` holds. -/
theorem Kept.mac {s₀ : State} {C W SP : BitVec 32} {R : Nat} {D : BitVec 32} {n : Nat} {ext : List Region}
    {s : State} (L : VG.Proof.AesSiv.X86.Lay C W SP) (hR : R = 10 ∨ R = 12 ∨ R = 14) (h : VG.Proof.AesSiv.X86.Kept s₀ C W SP R D n ext s)
    (he : ∀ r ∈ ext, (⟨w64 C, 512⟩ : Region).Disjoint r) :
    Spec.Siv.ctxMac s.mem (w64 C) R = Spec.Siv.ctxMac s₀.mem (w64 C) R :=
  VG.Proof.AesSiv.X86.ctxMac_frame h.big (fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons] at hr
    rcases hr with rfl | rfl | hr
    · exact L.c_w.sub_right (Lay.wSub (by decide))
    · exact L.stk_c.symm
    · exact he r hr) (by omega)

theorem zero_eq : Spec.Siv.zero = Spec.Cmac.zeros 16 := rfl

/-- The CMAC of the zero block from the context's subkeys. -/
theorem ctxMac_zero (m : Mem) (C : Addr) (R : Nat) :
    Spec.Siv.ctxMac m C R Spec.Siv.zero = Spec.Cmac.aesWith R (bytesAt m C (16 * (R + 1)))
      (Spec.Cmac.xor (Spec.Cmac.lastBlock 16 (bytesAt m (C + BitVec.ofNat 64 240) 16)
        (bytesAt m (C + BitVec.ofNat 64 256) 16) (Spec.Cmac.zeros 16)) (Spec.Cmac.zeros 16)) := by
  have := Siv.cmacWith_split (Spec.Siv.schedCiph m C R) (bytesAt m (C + 240) 16) (bytesAt m (C + 256) 16)
    (msg := []) (last := Spec.Cmac.zeros 16) (by decide) (by decide) (.inl rfl)
  simp only [List.nil_append] at this
  rw [Spec.Siv.ctxMac, VG.Proof.AesSiv.X86.zero_eq, this, Proof.Cmac.xor_comm]
  rfl

/-- The registers and memory after the block before `start`'s call. -/
theorem startPre_ok {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {R : Nat} {s : State} (E : VG.Proof.AesSiv.X86.Env C W SP s)
    (hc : slotv s.mem W ctxO = C) (hr : slotv s.mem W roundsO = BitVec.ofNat 32 R) :
    ∃ s', runBlock isa (zero4 zOff ++ zero4 dOff ++ macArgs dOff ++
        ([.mov .ebx (.reg .ebp), .alu .add .ebx (imm zOff), .mov .esi (imm 16)] : List Instr)) s = some s' ∧
      s'.mem = Cmac.zero4 (Cmac.zero4 s.mem (w64 W + BitVec.ofNat 64 zOff)) (w64 W + BitVec.ofNat 64 dOff) ∧
      s'.gpr .eax = C ∧ s'.gpr .ecx = BitVec.ofNat 32 R ∧ s'.gpr .edx = W + BitVec.ofNat 32 2560 ∧
      s'.gpr .ebx = W + BitVec.ofNat 32 16 ∧ s'.gpr .esi = BitVec.ofNat 32 16 ∧
      s'.gpr .edi = W + BitVec.ofNat 32 256 ∧ s'.gpr .ebp = W ∧ s'.gpr .esp = SP ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have z₁ := zero4_fold s.mem W zOff
  have z₂ := zero4_fold (Cmac.zero4 s.mem (w64 W + BitVec.ofNat 64 zOff)) W dOff
  simp only [Nat.reduceAdd, zOff, dOff] at z₁ z₂
  refine ⟨_, by crun [zero4, macArgs, E.ebp, L.aW, E.perm.wW, E.perm.wR, hc, hr], ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · cmems [z₁, z₂]
  · cregs [hc]
  · cregs [hr]
  · cregs [E.ebp]
  · cregs [E.ebp]
  · cregs []
  · cregs [E.ebp]
  · cregs [E.ebp]
  · cregs [E.esp]
  all_goals cmems []

/-- What `start` writes: the zero block, `D` and the working space of the
function it calls, and the stack below `SP`. -/
abbrev startR (W SP : BitVec 32) : List Region :=
  [⟨w64 W + BitVec.ofNat 64 16, 16⟩, ⟨w64 W + BitVec.ofNat 64 256, 2320⟩, below SP 56]

/-- `start`: `D = AES-CMAC(K1, <zero>)`, S2V's first state. -/
theorem start_ok (v : Ctr32Impl) {s₀ : State} {C W SP : BitVec 32} {R : Nat} {D : BitVec 32} {n : Nat}
    (L : VG.Proof.AesSiv.X86.Lay C W SP) (hR : R = 10 ∨ R = 12 ∨ R = 14) {s : State} (h : VG.Proof.AesSiv.X86.Kept s₀ C W SP R D n [] s) :
    WP isa (start v.callee v.suffix) s fun s' => VG.Proof.AesSiv.X86.Kept s₀ C W SP R D n [] s' ∧
      Frame (VG.Proof.AesSiv.X86.startR W SP) s.mem s'.mem ∧
      bytesAt s'.mem (w64 W + BitVec.ofNat 64 dOff) 16 = Spec.Siv.s2vStart (Spec.Siv.ctxMac s₀.mem (w64 C) R) := by
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with h | h | h <;> omega
  obtain ⟨s₁, run₁, m₁, ax₁, cx₁, dx₁, bx₁, si₁, di₁, bp₁, sp₁, rd₁, wr₁⟩ :=
    VG.Proof.AesSiv.X86.startPre_ok L h.env h.slots.ctx h.slots.rounds
  have E₁ : VG.Proof.AesSiv.X86.Env C W SP s₁ := ⟨bp₁, sp₁, h.env.perm.of_eq rd₁ wr₁⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have f₁ : Frame [⟨w64 W + BitVec.ofNat 64 zOff, 16⟩, ⟨w64 W + BitVec.ofNat 64 dOff, 16⟩] s.mem s₁.mem := by
    rw [m₁]
    exact ((Cmac.frame_store4 _ _ _ _ _).sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩).trans
      ((Cmac.frame_store4 _ _ _ _ _).sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩)
  refine WP.mono (VG.Proof.AesSiv.X86.finCall_ok v L E₁ hR (y := 2560) (.inr ⟨by decide, by decide⟩) (P := W + BitVec.ofNat 32 16)
    (l := 16) (Nat.le_refl _) (VG.Proof.AesSiv.X86.srcW L E₁.perm (t := 16) (k := 16) (by decide))
    (by rw [L.aW (o := 16) (by decide)]; exact Lay.w_w (.inl (by decide)) (by decide) (by decide))
    ax₁ cx₁ dx₁ bx₁ si₁ di₁) fun s₂ ⟨E₂, rd₂, wr₂, _, f₂, o₂⟩ => ?_
  have f₁₂ : Frame (VG.Proof.AesSiv.X86.startR W SP) s.mem s₂.mem := by
    refine (f₁.sub fun r hr => ?_).trans (f₂.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨⟨w64 W + BitVec.ofNat 64 256, 2320⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨⟨w64 W + BitVec.ofNat 64 256, 2320⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨⟨w64 W + BitVec.ofNat 64 256, 2320⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨below SP 56, by simp, fun _ h => h⟩
  refine ⟨h.step L (by simp) E₂ (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]) f₁₂ fun r hr => .inl ?_, f₁₂, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨VG.Proof.AesSiv.X86.wA W, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨VG.Proof.AesSiv.X86.wC W, by simp, fun _ h => h⟩
    · exact ⟨below SP 56, by simp, fun _ h => h⟩
  simp only [zOff, dOff] at m₁
  have fz : Frame [⟨w64 W + BitVec.ofNat 64 2560, 16⟩] (Cmac.zero4 s.mem (w64 W + BitVec.ofNat 64 16))
      s₁.mem := by rw [m₁]; exact Cmac.frame_store4 _ _ _ _ _
  have hz16 : bytesAt s₁.mem (w64 W + BitVec.ofNat 64 16) 16 = Spec.Cmac.zeros 16 := by
    rw [Proof.AesGcm.X86.bytesAt_frame fz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide))
      (by decide)]
    exact Cmac.zero4_bytes _ _
  have hz : bytesAt s₁.mem (w64 W + BitVec.ofNat 64 2560) 16 = Spec.Cmac.zeros 16 := by
    rw [m₁]; exact Cmac.zero4_bytes _ _
  have hc₁ : Spec.Siv.ctxMac s₁.mem (w64 C) R = Spec.Siv.ctxMac s.mem (w64 C) R :=
    VG.Proof.AesSiv.X86.ctxMac_frame f₁ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact L.c_w.sub_right (Lay.wSub (by decide))) (by omega)
  simp only [dOff] at o₂ ⊢
  rw [o₂, Spec.Siv.s2vStart, ← h.mac L hR (by simp), ← hc₁, VG.Proof.AesSiv.X86.ctxMac_zero, L.aW (o := 16) (by decide), hz16, hz]

/-! ## `dbl` in place -/

/-- `dblAt o`: the block at `W + o` doubled in place; `ebp` is `W` again
after it. -/
theorem dblAt_wp {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {s : State} (E : VG.Proof.AesSiv.X86.Env C W SP s) {o : Nat}
    (ho : o + 16 ≤ 2576) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.gpr .ebp = W → s'.gpr .esp = SP →
      s'.mem = Proof.CmacAes.X86.dblMem s.mem (w64 W + BitVec.ofNat 64 o) 0 0 → s'.rd = s.rd → s'.wr = s.wr →
      WP isa (.block is) s' Q) :
    WP isa (.block (dblAt o ++ is)) s Q := by
  have hW := L.fw
  rw [dblAt, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.of_runBlock ⟨_, by crun [E.ebp], ?_⟩
  have aW : (W + BitVec.ofNat 32 o).setWidth 64 = w64 W + BitVec.ofNat 64 o := L.sW (by omega)
  refine Proof.CmacAes.X86.dbl_wp (K := W + BitVec.ofNat 32 o) (src := 0) (dst := 0) (by cregs [E.ebp])
    (by rw [L.nW (by omega)]; omega) (by rw [L.nW (by omega)]; omega)
    (by cmems []; rw [aW, BitVec.add_zero]; exact covers_left (E.perm.wC ho))
    (by cmems []; rw [aW, BitVec.add_zero]; exact E.perm.wC ho) fun s₁ g₁ m₁ rd₁ wr₁ => ?_
  rw [WP.block_append_iff]
  have bx₁ : s₁.gpr .ebx = W + BitVec.ofNat 32 o := by
    rw [g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    cregs [E.ebp]
  have sp₁ : s₁.gpr .esp = SP := by
    rw [g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    cregs [E.esp]
  refine WP.of_runBlock ⟨_, by crun [bx₁], k _ (by cregs [bx₁]; exact BitVec.add_sub_cancel _ _) (by cregs [sp₁])
    (by cmems [m₁, aW]) (by cmems [rd₁]) (by cmems [wr₁])⟩

/-! ## A step of S2V -/

theorem add32_assoc (x : BitVec 32) (a b : Nat) :
    x + BitVec.ofNat 32 a + BitVec.ofNat 32 b = x + BitVec.ofNat 32 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- After `dbl`: the CMAC state XORed into `D`, then the next descriptor and
one fewer left. -/
theorem adTail_ok {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {s : State} (E : VG.Proof.AesSiv.X86.Env C W SP s) {a b : BitVec 32}
    (ha : slotv s.mem W adsO = a) (hb : slotv s.mem W leftO = b) :
    ∃ s', runBlock isa (([.mov .edx (.reg .ebp), .alu .add .edx (imm dOff)] : List Instr) ++ (xorInto stOff 0 ++
        ([.mov .eax (slot adsO), .alu .add .eax (imm 8), .store (at_ .ebp adsO) .eax,
          .mov .eax (slot leftO), .alu .sub .eax (imm 1), .store (at_ .ebp leftO) .eax] : List Instr))) s = some s' ∧
      s'.mem = ((Cmac.xor4Mem s.mem (w64 W + BitVec.ofNat 64 dOff) (w64 W + BitVec.ofNat 64 stOff)
        (w64 W + BitVec.ofNat 64 dOff)).writeW (w64 W + BitVec.ofNat 64 adsO) (a + BitVec.ofNat 32 8)).writeW
        (w64 W + BitVec.ofNat 64 leftO) (b - BitVec.ofNat 32 1) ∧
      s'.zf = some (b - BitVec.ofNat 32 1 == 0) ∧ s'.gpr .ebp = W ∧ s'.gpr .esp = SP ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  refine ⟨_, by crun [xorInto, E.ebp, L.aW, E.perm.wW, E.perm.wR, ha, hb, VG.Proof.AesSiv.X86.add32_assoc,
    Proof.AesGcm.X86.add_zero32], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cmems [ha, hb, Cmac.xor4Mem, VG.Proof.AesSiv.X86.add_ofNat_assoc]
  · cmems [ha, hb]
  · cregs [E.ebp]
  · cregs [E.esp]
  all_goals cmems []

/-- `adStep`: `D = dbl(D) ⊕` the CMAC state, the next descriptor and one
fewer left. -/
theorem adStep_wp {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {s : State} (E : VG.Proof.AesSiv.X86.Env C W SP s) {A : BitVec 32} {N i : Nat}
    (hiN : i < N) (hN : N < 2 ^ 32) (hads : slotv s.mem W adsO = A + BitVec.ofNat 32 (8 * i))
    (hleft : slotv s.mem W leftO = BitVec.ofNat 32 (N - i)) :
    WP isa (.block adStep) s fun s' => VG.Proof.AesSiv.X86.Env C W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨w64 W + BitVec.ofNat 64 dOff, 16⟩, VG.Proof.AesSiv.X86.wV W] s.mem s'.mem ∧
      bytesAt s'.mem (w64 W + BitVec.ofNat 64 dOff) 16 =
        Spec.Cmac.xor (bytesAt s.mem (w64 W + BitVec.ofNat 64 stOff) 16)
          (Spec.Cmac.dbl 16 (bytesAt s.mem (w64 W + BitVec.ofNat 64 dOff) 16)) ∧
      slotv s'.mem W adsO = A + BitVec.ofNat 32 (8 * (i + 1)) ∧
      slotv s'.mem W leftO = BitVec.ofNat 32 (N - (i + 1)) ∧ s'.zf = some (decide (i + 1 = N)) := by
  have e : adStep = dblAt dOff ++ (([.mov .edx (.reg .ebp), .alu .add .edx (imm dOff)] : List Instr) ++
      (xorInto stOff 0 ++ ([.mov .eax (slot adsO), .alu .add .eax (imm 8), .store (at_ .ebp adsO) .eax,
        .mov .eax (slot leftO), .alu .sub .eax (imm 1), .store (at_ .ebp leftO) .eax] : List Instr))) := by
    simp only [adStep, List.append_assoc]
  rw [e]
  refine VG.Proof.AesSiv.X86.dblAt_wp L E (o := dOff) (by decide) fun s₁ bp₁ sp₁ m₁ rd₁ wr₁ => ?_
  have E₁ : VG.Proof.AesSiv.X86.Env C W SP s₁ := ⟨bp₁, sp₁, E.perm.of_eq rd₁ wr₁⟩
  have fD : Frame [⟨w64 W + BitVec.ofNat 64 dOff, 16⟩] s.mem s₁.mem := by
    rw [m₁]
    have := Proof.CmacAes.X86.dblMem_frame s.mem (w64 W + BitVec.ofNat 64 dOff) 0 0
    rwa [BitVec.add_zero] at this
  have kD : ∀ o, o + 4 ≤ 2560 → slotv s₁.mem W o = slotv s.mem W o := fun o ho =>
    fD.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by simp only [dOff]; omega)) (by omega)
        (by decide)) (by decide)
  obtain ⟨s₂, run₂, m₂, zf₂, bp₂, sp₂, rd₂, wr₂⟩ := VG.Proof.AesSiv.X86.adTail_ok L E₁ (a := A + BitVec.ofNat 32 (8 * i))
    (b := BitVec.ofNat 32 (N - i)) (by rw [kD _ (by decide)]; exact hads) (by rw [kD _ (by decide)]; exact hleft)
  refine WP.of_runBlock ⟨s₂, run₂, ⟨bp₂, sp₂, E₁.perm.of_eq rd₂ wr₂⟩, by rw [rd₂, rd₁], by rw [wr₂, wr₁], ?_, ?_,
    ?_, ?_, ?_⟩
  · -- What the step writes.
    have fX : Frame [⟨w64 W + BitVec.ofNat 64 dOff, 16⟩, VG.Proof.AesSiv.X86.wV W] s₁.mem s₂.mem := by
      rw [m₂]
      exact (((Cmac.xor4Mem_frame _ _ _ _).sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩).writeW (r := VG.Proof.AesSiv.X86.wV W)
        (by simp) _ (Offset.contains _ (by decide) (by decide) (by decide))).writeW (r := VG.Proof.AesSiv.X86.wV W) (by simp) _
        (Offset.contains _ (by decide) (by decide) (by decide))
    exact (fD.sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩).trans fX
  · -- `D`.
    have fC : Frame [VG.Proof.AesSiv.X86.wV W] (Cmac.xor4Mem s₁.mem (w64 W + BitVec.ofNat 64 dOff) (w64 W + BitVec.ofNat 64 stOff)
        (w64 W + BitVec.ofNat 64 dOff)) s₂.mem := by
      rw [m₂]
      exact ((Frame.refl _ _).writeW (r := VG.Proof.AesSiv.X86.wV W) (by simp) _
        (Offset.contains _ (by decide) (by decide) (by decide))).writeW (r := VG.Proof.AesSiv.X86.wV W) (by simp) _
        (Offset.contains _ (by decide) (by decide) (by decide))
    rw [Proof.AesGcm.X86.bytesAt_frame fC (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by decide)) (by decide) (by decide))
        (by decide),
      Cmac.xor4Mem_bytes _ (Cmac.Sep4.of_disjoint (Lay.w_w (.inr (by decide)) (by decide) (by decide)))
        (Cmac.Sep4.self _),
      Proof.AesGcm.X86.bytesAt_frame fD (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide))
        (by decide), m₁]
    have := Proof.CmacAes.X86.dblMem_bytes s.mem (w64 W + BitVec.ofNat 64 dOff) 0 0
    rw [BitVec.add_zero] at this
    rw [this]
  · rw [m₂, slotv, readW_writeW_off _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32, VG.Proof.AesSiv.X86.add32_assoc]
    congr 2
  · rw [m₂]
    exact (Mem.readW_writeW_self32 _ _ _).trans (Proof.AesGcm.X86.pred_count hiN hN)
  · rw [zf₂, Proof.AesGcm.X86.pred_beq hiN hN]

/-! ## The loop over the components -/

/-- The next descriptor's address and length into `W + strO` and
`W + slenO`. -/
theorem adNext_ok {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {s : State} (E : VG.Proof.AesSiv.X86.Env C W SP s) {A : BitVec 32} {j : Nat}
    (hads : slotv s.mem W adsO = A + BitVec.ofNat 32 j) (hfit : A.toNat + j + 8 ≤ 2 ^ 32)
    (rD : Covers [⟨w64 A + BitVec.ofNat 64 j, 8⟩] (s.rd ++ s.wr))
    (dW : (⟨w64 A + BitVec.ofNat 64 j, 8⟩ : Region).Disjoint ⟨w64 W, 2576⟩) :
    ∃ s', runBlock isa adNext s = some s' ∧
      s'.mem = (s.mem.writeW (w64 W + BitVec.ofNat 64 strO) (s.mem.readW (w64 A + BitVec.ofNat 64 j) 32)).writeW
        (w64 W + BitVec.ofNat 64 slenO) (s.mem.readW (w64 A + BitVec.ofNat 64 (j + 4)) 32) ∧
      s'.gpr .ebp = W ∧ s'.gpr .esp = SP ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have p0 : (A + BitVec.ofNat 32 j + BitVec.ofNat 32 0).setWidth 64 = w64 A + BitVec.ofNat 64 j := by
    rw [Proof.AesGcm.X86.add_zero32]; exact Buf.ptr (by omega)
  have p4 : (A + BitVec.ofNat 32 j + BitVec.ofNat 32 4).setWidth 64 = w64 A + BitVec.ofNat 64 (j + 4) := by
    rw [VG.Proof.AesSiv.X86.add32_assoc]; exact Buf.ptr (by omega)
  have i0 : InRegions (s.rd ++ s.wr) (w64 A + BitVec.ofNat 64 j) 4 := by
    have := Proof.AesGcm.X86.in_off (p := w64 A + BitVec.ofNat 64 j) rD (d := 0) (n := 4) (by decide) (by decide)
    rwa [BitVec.add_zero] at this
  have i4 : InRegions (s.rd ++ s.wr) (w64 A + BitVec.ofNat 64 (j + 4)) 4 := by
    have := Proof.AesGcm.X86.in_off (p := w64 A + BitVec.ofNat 64 j) rD (d := 4) (n := 4) (by decide) (by decide)
    rwa [VG.Proof.AesSiv.X86.add_ofNat_assoc] at this
  have r4 : (s.mem.writeW (w64 W + BitVec.ofNat 64 strO) (s.mem.readW (w64 A + BitVec.ofNat 64 j) 32)).readW
      (w64 A + BitVec.ofNat 64 (j + 4)) 32 = s.mem.readW (w64 A + BitVec.ofNat 64 (j + 4)) 32 :=
    Cmac.readW_writeW_disj _ (((dW.sub_left (by
      rw [← VG.Proof.AesSiv.X86.add_ofNat_assoc]; exact Offset.sub_base _ (by decide))).sub_right (Lay.wSub (by decide))).symm)
  refine ⟨_, by crun [adNext, E.ebp, L.aW, E.perm.wW, E.perm.wR, hads, p0, p4, i0, i4], ?_, ?_, ?_, ?_, ?_⟩
  · cmems [hads, p0, p4, r4]
  · cregs [E.ebp]
  · cregs [E.esp]
  all_goals cmems []

/-- Before the `i`-th component (and, for `i = N`, after the last): `D` is
S2V's state of the first `i`, with the next descriptor's address and how
many are left in their slots. -/
structure AInv (s₀ : State) (C W SP A : BitVec 32) (R N : Nat) (D : BitVec 32) (n i : Nat) (s : State) :
    Prop where
  kept : VG.Proof.AesSiv.X86.Kept s₀ C W SP R D n [] s
  le : i ≤ N
  ads : slotv s.mem W adsO = A + BitVec.ofNat 32 (8 * i)
  left : slotv s.mem W leftO = BitVec.ofNat 32 (N - i)
  acc : bytesAt s.mem (w64 W + BitVec.ofNat 64 dOff) 16 =
    Spec.Siv.s2vAcc (Spec.Siv.ctxMac s₀.mem (w64 C) R) ((Spec.Siv.components 32 s₀.mem (w64 A) N).take i)

theorem sub_wS {W : BitVec 32} {d k : Nat} (h₁ : 200 ≤ d) (h₂ : d + k ≤ 256) :
    Region.Sub ⟨w64 W + BitVec.ofNat 64 d, k⟩ (VG.Proof.AesSiv.X86.wS W) := Offset.sub _ h₁ (by omega)

/-- The `i`-th descriptor read: what the component's CMAC starts from. -/
theorem adNext_wp {s₀ : State} {C W SP A : BitVec 32} {R N : Nat} {D : BitVec 32} {n i : Nat}
    (hA : VG.Proof.AesSiv.X86.AdCtx s₀ C W SP A R N) (hiN : i < N) {s : State} (h : VG.Proof.AesSiv.X86.AInv s₀ C W SP A R N D n i s) :
    WP isa (.block adNext) s fun s₁ => VG.Proof.AesSiv.X86.CmacPre C W SP R (VG.Proof.AesSiv.X86.compA s₀.mem A i) (VG.Proof.AesSiv.X86.compL s₀.mem A i) s₁ ∧
      VG.Proof.AesSiv.X86.Kept s₀ C W SP R D n [] s₁ ∧ Frame [⟨w64 W + BitVec.ofNat 64 strO, 8⟩] s.mem s₁.mem := by
  have L := hA.lay
  have K := h.kept
  have hRb : R ≤ 14 := by rcases hA.rounds with h | h | h <;> omega
  have hfA := hA.desc.wrap
  -- The descriptor, as on entry.
  have dW : (⟨w64 A + BitVec.ofNat 64 (8 * i), 8⟩ : Region).Disjoint ⟨w64 W, 2576⟩ :=
    hA.desc.w.sub_left (Offset.sub_base _ (by omega))
  have dS : (below SP 56).Disjoint ⟨w64 A + BitVec.ofNat 64 (8 * i), 8⟩ :=
    hA.desc.stk.sub_right (Offset.sub_base _ (by omega))
  have rD : Covers [⟨w64 A + BitVec.ofNat 64 (8 * i), 8⟩] (s.rd ++ s.wr) := by
    rw [K.rd, K.wr]; exact Proof.AesGcm.X86.covers_off hA.desc.rd (by omega) (by have := hA.desc.lt; omega)
  have wd : ∀ {d : Nat}, d + 4 ≤ 8 → s.mem.readW (w64 A + BitVec.ofNat 64 (8 * i + d)) 32 =
      s₀.mem.readW (w64 A + BitVec.ofNat 64 (8 * i + d)) 32 := fun hd =>
    K.big.readW (r := ⟨w64 A + BitVec.ofNat 64 (8 * i), 8⟩)
      (by rw [← VG.Proof.AesSiv.X86.add_ofNat_assoc]; exact Offset.contains_base _ hd (by omega)) (fun r hr => by
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact dW.sub_right (Lay.wSub (by decide))
        · exact dS.symm) (by decide)
  have w0 := wd (d := 0) (by decide)
  have w4 := wd (d := 4) (by decide)
  rw [Nat.add_zero] at w0
  obtain ⟨s₁, run₁, m₁, bp₁, sp₁, rd₁, wr₁⟩ := VG.Proof.AesSiv.X86.adNext_ok L K.env h.ads (by omega) rD dW
  have E₁ : VG.Proof.AesSiv.X86.Env C W SP s₁ := ⟨bp₁, sp₁, K.env.perm.of_eq rd₁ wr₁⟩
  have f₁ : Frame [⟨w64 W + BitVec.ofNat 64 strO, 8⟩] s.mem s₁.mem := by
    rw [m₁]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains (w64 W) (d := 200) (n := 4) (e := 200) (k := 8) (by decide) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _
      (Offset.contains (w64 W) (d := 204) (n := 4) (e := 200) (k := 8) (by decide) (by decide) (by decide))
  have K₁ := K.step L (by simp) E₁ rd₁ wr₁ f₁ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact .inl ⟨VG.Proof.AesSiv.X86.wS W, by simp, VG.Proof.AesSiv.X86.sub_wS (by decide) (by decide)⟩
  have hc₁ := hA.comps i hiN
  refine WP.of_runBlock ⟨s₁, run₁, ?_, K₁, f₁⟩
  exact
    ⟨E₁, K₁.slots.ctx, K₁.slots.rounds,
      by rw [m₁, slotv, readW_writeW_off _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32, w0],
      by rw [m₁, slotv, Mem.readW_writeW_self32, w4]; exact (Proof.AesGcm.X86.ofNat_toNat32 _).symm,
      BitVec.isLt _, hc₁.of_eq K₁.rd K₁.wr⟩

/-- One component: its descriptor read (`adNext_wp`), its CMAC into the
working space (`cmacOf_ok`) and the step of S2V (`adStep_wp`). -/
theorem adBody_ok (v : Ctr32Impl) {s₀ : State} {C W SP A : BitVec 32} {R N : Nat} {D : BitVec 32} {n i : Nat}
    (hA : VG.Proof.AesSiv.X86.AdCtx s₀ C W SP A R N) (hiN : i < N) {s : State} (h : VG.Proof.AesSiv.X86.AInv s₀ C W SP A R N D n i s) :
    WP isa (.seq (.block adNext) (.seq (cmacOf v.callee v.suffix stOff) (.block adStep))) s
      fun s' => VG.Proof.AesSiv.X86.AInv s₀ C W SP A R N D n (i + 1) s' ∧ s'.zf = some (decide (i + 1 = N)) := by
  have L := hA.lay
  have hc₁ := hA.comps i hiN
  refine WP.seq (WP.mono (VG.Proof.AesSiv.X86.adNext_wp hA hiN h) fun s₁ ⟨P₁, K₁, f₁⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.AesSiv.X86.cmacOf_ok v L hA.rounds P₁) fun s₂ M => ?_)
  have K₂ := K₁.step L (by simp) M.env M.rd M.wr M.frame fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact .inl ⟨VG.Proof.AesSiv.X86.wB W, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact .inl ⟨VG.Proof.AesSiv.X86.wS W, by simp, VG.Proof.AesSiv.X86.sub_wS (by decide) (by decide)⟩
    · exact .inl ⟨VG.Proof.AesSiv.X86.wC W, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact .inl ⟨below SP 56, by simp, fun _ h => h⟩
  -- The slots `adStep` reads.
  have kS : ∀ o, (176 ≤ o ∧ o + 4 ≤ 200) → slotv s₂.mem W o = slotv s.mem W o := fun o ho => by
    rw [VG.Proof.AesSiv.X86.cmacR_slot L M.frame (by omega) (by omega)]
    exact f₁.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by simp only [strO]; omega)) (by omega)
        (by decide)) (by decide)
  refine WP.mono (VG.Proof.AesSiv.X86.adStep_wp L M.env hiN hA.N32 (by rw [kS _ (by decide)]; exact h.ads)
    (by rw [kS _ (by decide)]; exact h.left)) fun s₃ ⟨E₃, rd₃, wr₃, f₃, o₃, a₃, l₃, z₃⟩ => ⟨⟨?_, hiN, a₃, l₃, ?_⟩, z₃⟩
  · exact K₂.step L (by simp) E₃ rd₃ wr₃ f₃ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inl ⟨VG.Proof.AesSiv.X86.wC W, by simp, Offset.sub _ (by decide) (by decide)⟩
      · exact .inl ⟨VG.Proof.AesSiv.X86.wV W, by simp, fun _ h => h⟩
  · -- `D = dbl(D) ⊕ AES-CMAC(K1, S)`.
    have hD₂ : bytesAt s₂.mem (w64 W + BitVec.ofNat 64 dOff) 16 = bytesAt s.mem (w64 W + BitVec.ofNat 64 dOff) 16 := by
      rw [Proof.AesGcm.X86.bytesAt_frame M.frame (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
          · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
          · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
          · exact (L.stk_w' (by decide)).symm) (by decide),
        Proof.AesGcm.X86.bytesAt_frame f₁ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by decide)) (by decide) (by decide))
          (by decide)]
    have hS : bytesAt s₁.mem (w64 (VG.Proof.AesSiv.X86.compA s₀.mem A i)) (VG.Proof.AesSiv.X86.compL s₀.mem A i) =
        bytesAt s₀.mem (w64 (VG.Proof.AesSiv.X86.compA s₀.mem A i)) (VG.Proof.AesSiv.X86.compL s₀.mem A i) :=
      K₁.bytes hc₁.w hc₁.stk (by simp) (by have := hc₁.lt; omega)
    rw [o₃, M.out, hD₂, h.acc, K₁.mac L hA.rounds (by simp), hS, VG.Proof.AesSiv.X86.components_take_succ _ _ hiN, VG.Proof.AesSiv.X86.s2vAcc_snoc,
      Spec.Siv.s2vStep, Siv.xor_eq, Proof.Cmac.xor_comm]
    rfl

theorem leftTest_ok {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {s : State} (E : VG.Proof.AesSiv.X86.Env C W SP s) {N : Nat}
    (hN : N < 2 ^ 32) (hl : slotv s.mem W leftO = BitVec.ofNat 32 N) :
    ∃ s', runBlock isa [.mov .eax (slot leftO), .alu .test .eax (.reg .eax)] s = some s' ∧ s'.mem = s.mem ∧
      s'.zf = some (decide (N = 0)) ∧ s'.gpr .ebp = W ∧ s'.gpr .esp = SP ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [E.ebp, L.aW, E.perm.wR, hl], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · cmems [hl]; rw [Proof.AesGcm.X86.and_self_beq32 hN]
  · cregs [E.ebp]
  · cregs [E.esp]
  all_goals rfl

theorem AInv.keep {s₀ : State} {C W SP A : BitVec 32} {R N : Nat} {D : BitVec 32} {n i : Nat} {s s' : State}
    (L : VG.Proof.AesSiv.X86.Lay C W SP) (h : VG.Proof.AesSiv.X86.AInv s₀ C W SP A R N D n i s) (hm : s'.mem = s.mem) (hbp : s'.gpr .ebp = W)
    (hsp : s'.gpr .esp = SP) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesSiv.X86.AInv s₀ C W SP A R N D n i s' :=
  ⟨h.kept.step L (by simp) ⟨hbp, hsp, h.kept.env.perm.of_eq hrd hwr⟩ hrd hwr (rs := [])
    (by rw [hm]; exact Frame.refl _ _)
    (fun r hr => by simp at hr), h.le, by rw [hm]; exact h.ads, by rw [hm]; exact h.left, by rw [hm]; exact h.acc⟩

/-- `s2vAds`: S2V over every component. -/
theorem s2vAds_ok (v : Ctr32Impl) {s₀ : State} {C W SP A : BitVec 32} {R N : Nat} {D : BitVec 32} {n : Nat}
    (hA : VG.Proof.AesSiv.X86.AdCtx s₀ C W SP A R N) {s : State} (h : VG.Proof.AesSiv.X86.AInv s₀ C W SP A R N D n 0 s) :
    WP isa (s2vAds v.callee v.suffix) s (VG.Proof.AesSiv.X86.AInv s₀ C W SP A R N D n N) := by
  have L := hA.lay
  have l₀ := h.left
  rw [Nat.sub_zero] at l₀
  obtain ⟨s₁, run₁, m₁, zf₁, bp₁, sp₁, rd₁, wr₁⟩ := VG.Proof.AesSiv.X86.leftTest_ok L h.kept.env hA.N32 l₀
  have h₁ := h.keep L m₁ bp₁ sp₁ rd₁ wr₁
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (N = 0)) (VG.Proof.AesSiv.X86.eval_e zf₁) (fun hz => ?_) (fun hz => ?_)
  · have hN : N = 0 := of_decide_eq_true hz
    subst hN
    exact WP.block_nil h₁
  · have hN : N ≠ 0 := of_decide_eq_false hz
    refine WP.loop (fun (k : Nat) (t : State) => ∃ i, k = N - i ∧ i < N ∧ VG.Proof.AesSiv.X86.AInv s₀ C W SP A R N D n i t)
      (fun k t ⟨i, hk, hi, ht⟩ => ?_) (N - 0) s₁ ⟨0, rfl, by omega, h₁⟩
    refine WP.mono (VG.Proof.AesSiv.X86.adBody_ok v hA hi ht) fun t' ⟨ht', hz'⟩ => ?_
    by_cases he : i + 1 = N
    · left
      refine ⟨by rw [VG.Proof.AesSiv.X86.eval_ne hz']; simp [he], ?_⟩
      exact (congrArg (fun j => VG.Proof.AesSiv.X86.AInv s₀ C W SP A R N D n j t') he).mp ht'
    · right
      refine ⟨by rw [VG.Proof.AesSiv.X86.eval_ne hz']; simp [he], N - (i + 1), by omega, i + 1, rfl, by omega, ht'⟩

/-! ## Constant time -/

/-- `start` is constant time from the environment and the slots it reads. -/
theorem start_ct (v : Ctr32Impl) {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    CT (fun s => VG.Proof.AesSiv.X86.Env C W SP s ∧ slotv s.mem W ctxO = C ∧ slotv s.mem W roundsO = BitVec.ofNat 32 R)
      (start v.callee v.suffix) := by
  refine CT.block_seq [.ebp] (VG.Proof.AesSiv.X86.pin_ebp fun s h => h.1.ebp) (by taint_decide) (fun s hs => VG.Proof.AesSiv.X86.startPre_ok L hs.1 hs.2.1
    hs.2.2) ?_
  refine VG.Proof.AesSiv.X86.finCall_ct v L hR (y := 2560) (.inr ⟨by decide, by decide⟩) (P := W + BitVec.ofNat 32 16) (l := 16)
    (Nat.le_refl _) fun s₁ ⟨s, hs, _, ax, cx, dx, bx, si, di, bp, sp, rd, wr⟩ => ?_
  have E₁ : VG.Proof.AesSiv.X86.Env C W SP s₁ := ⟨bp, sp, hs.1.perm.of_eq rd wr⟩
  exact ⟨E₁, VG.Proof.AesSiv.X86.srcW L E₁.perm (t := 16) (k := 16) (by decide),
    by rw [L.aW (o := 16) (by decide)]; exact Lay.w_w (.inl (by decide)) (by decide) (by decide), ax, cx, dx, bx, si,
    di⟩

theorem CT.of_empty {I : State → Prop} {c : Prog isa} (h : ∀ s, ¬ I s) : CT I c :=
  RelCT.of_false fun s₁ _ hp => h s₁ hp.1

/-- `AInv` from some entry state whose descriptors list the public
components `ca`, `cl`. -/
def ACT (C W SP A : BitVec 32) (R N : Nat) (ca : Nat → BitVec 32) (cl : Nat → Nat) (i : Nat) (s : State) : Prop :=
  ∃ s₀ D n, VG.Proof.AesSiv.X86.AdCtx s₀ C W SP A R N ∧ (∀ j < N, VG.Proof.AesSiv.X86.compA s₀.mem A j = ca j ∧ VG.Proof.AesSiv.X86.compL s₀.mem A j = cl j) ∧
    VG.Proof.AesSiv.X86.AInv s₀ C W SP A R N D n i s

/-- `adNext`, from the descriptor's address the slot holds. -/
theorem adNext_ct {C W SP A : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {R N : Nat} {ca : Nat → BitVec 32} {cl : Nat → Nat}
    {i : Nat} : CT (VG.Proof.AesSiv.X86.ACT C W SP A R N ca cl i) (.block adNext) := by
  have e : adNext = ([.mov .eax (slot adsO)] : List Instr) ++ [.mov .ecx (.mem (at_ .eax 0)),
      .store (at_ .ebp strO) .ecx, .mov .ecx (.mem (at_ .eax 4)), .store (at_ .ebp slenO) .ecx] := rfl
  rw [e]
  refine RelCT.block_append (CT.seq (J := fun s => s.gpr .ebp = W ∧ s.gpr .eax = A + BitVec.ofNat 32 (8 * i))
    (CT.taint [.ebp] (VG.Proof.AesSiv.X86.pin_ebp fun s ⟨_, _, _, _, _, h⟩ => h.kept.env.ebp) (by taint_decide))
    (fun s ⟨_, _, _, _, _, h⟩ => WP.of_runBlock ⟨_, by crun [h.kept.env.ebp, L.aW, h.kept.env.perm.wR],
      by cregs [h.kept.env.ebp], by cregs [h.ads]⟩)
    (CT.taint [.ebp, .eax] (VG.Proof.AesSiv.X86.pin2 fun _ h => h) (by taint_decide)))

theorem adBody_ct (v : Ctr32Impl) {C W SP A : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {R N : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {ca : Nat → BitVec 32} {cl : Nat → Nat} {i : Nat} (hiN : i < N)
    (hcl : cl i < 2 ^ 32) :
    CT (VG.Proof.AesSiv.X86.ACT C W SP A R N ca cl i) (.seq (.block adNext) (.seq (cmacOf v.callee v.suffix stOff) (.block adStep))) := by
  refine CT.seq (J := VG.Proof.AesSiv.X86.CmacPre C W SP R (ca i) (cl i)) (VG.Proof.AesSiv.X86.adNext_ct L)
    (fun s ⟨s₀, D, n, hA, hc, h⟩ => WP.mono (VG.Proof.AesSiv.X86.adNext_wp hA hiN h) fun s₁ ⟨P₁, _⟩ => by
      rw [(hc i hiN).1, (hc i hiN).2] at P₁; exact P₁) ?_
  exact CT.seq (J := fun s => s.gpr .ebp = W) (VG.Proof.AesSiv.X86.cmacOf_ct v L hR hcl)
    (fun s hs => WP.mono (VG.Proof.AesSiv.X86.cmacOf_ok v L hR hs) fun s' M => M.env.ebp)
    (CT.taint [.ebp] (VG.Proof.AesSiv.X86.pin_ebp fun _ h => h) (by taint_decide))

/-- The loop over the components is constant time. -/
theorem s2vLoop_ct (v : Ctr32Impl) {C W SP A : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {R N : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {ca : Nat → BitVec 32} {cl : Nat → Nat} (hcl : ∀ j < N, cl j < 2 ^ 32) (k : Nat) :
    CT (fun s => ∃ i, k = N - i ∧ i < N ∧ VG.Proof.AesSiv.X86.ACT C W SP A R N ca cl i s)
      (.loop (.seq (.block adNext) (.seq (cmacOf v.callee v.suffix stOff) (.block adStep))) .ne) := by
  refine CT.loopN (fun k s => ∃ i, k = N - i ∧ i < N ∧ VG.Proof.AesSiv.X86.ACT C W SP A R N ca cl i s) (fun k => ?_)
    (fun k s ⟨i, hk, hi, s₀, D, n, hA, hc, h⟩ => ?_) k
  · by_cases hk : 0 < k ∧ k ≤ N
    · exact (VG.Proof.AesSiv.X86.adBody_ct v L hR (A := A) (N := N) (ca := ca) (cl := cl) (i := N - k) (by omega) (hcl (N - k) (by omega))).mono fun s ⟨i, hk', hi, h⟩ => by
        rw [show N - k = i by omega]; exact h
    · exact CT.of_empty fun s ⟨i, hk', hi, _⟩ => hk ⟨by omega, by omega⟩
  · refine WP.mono (VG.Proof.AesSiv.X86.adBody_ok v hA hi h) fun s' ⟨h', hz⟩ => ⟨by omega, by rw [VG.Proof.AesSiv.X86.eval_ne hz]; simp; omega,
      fun hk1 => ⟨i + 1, by omega, by omega, s₀, D, n, hA, hc, h'⟩⟩

/-- `s2vAds` is constant time. -/
theorem s2vAds_ct (v : Ctr32Impl) {C W SP A : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {R N : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hN : N < 2 ^ 32) {ca : Nat → BitVec 32} {cl : Nat → Nat}
    (hcl : ∀ j < N, cl j < 2 ^ 32) :
    CT (VG.Proof.AesSiv.X86.ACT C W SP A R N ca cl 0) (s2vAds v.callee v.suffix) := by
  refine CT.seq (J := fun s => VG.Proof.AesSiv.X86.ACT C W SP A R N ca cl 0 s ∧ s.zf = some (decide (N = 0)))
    (CT.taint [.ebp] (VG.Proof.AesSiv.X86.pin_ebp fun s ⟨_, _, _, _, _, h⟩ => h.kept.env.ebp) (by taint_decide))
    (fun s ⟨s₀, D, n, hA, hc, h⟩ => ?_) ?_
  · have l₀ := h.left
    rw [Nat.sub_zero] at l₀
    obtain ⟨s₁, run₁, m₁, zf₁, bp₁, sp₁, rd₁, wr₁⟩ := VG.Proof.AesSiv.X86.leftTest_ok L h.kept.env hN l₀
    exact WP.of_runBlock ⟨s₁, run₁, ⟨s₀, D, n, hA, hc, h.keep L m₁ bp₁ sp₁ rd₁ wr₁⟩, zf₁⟩
  refine CT.ite (decide (N = 0)) (fun s h => VG.Proof.AesSiv.X86.eval_e h.2) (fun _ => CT.nil) fun hz => ?_
  have hN0 : N ≠ 0 := of_decide_eq_false hz
  exact (VG.Proof.AesSiv.X86.s2vLoop_ct v L hR hcl N).mono fun s ⟨h, _⟩ => ⟨0, by omega, by omega, h⟩

end VG.Proof.AesSiv.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.X86.FinishShort`. -/
section

/-!
# AES-SIV on x86: finishing S2V with a short string

Untrusted: everything here is checked by Lean. For a last string `P` of
`L < 16` bytes, the tail at `W + 32` becomes `pad(P) ⊕ dbl(D)`
(`shortTail_ok`): it is zeroed, `P` copied onto it (`copyN_ok`) and `0x80`
appended; `D` is copied to `W + 160` and doubled there (`dblAt_wp`), and
XORed into the tail. Its CMAC, one complete block, from a zero state
(`shortMac_ok`), is S2V's result (`Siv.s2vFinish_short`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesSiv.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4 copyLoop)
open VG.Proof.AesGcm.X86 (w64 toNat_ofNat32 toNat_add32 slotv zero4_fold length_bytesAt readW_writeW_off
  covers_left LoopPre CopyPost copyLoop_ok CT)

/-- A block copied, a word at a time, has the bytes of the original. -/
theorem copy4_bytes (m' m : Mem) (c p : Addr) :
    bytesAt (Cmac.store4 m' c (m.readW p 32) (m.readW (p + BitVec.ofNat 64 4) 32) (m.readW (p + BitVec.ofNat 64 8) 32)
      (m.readW (p + BitVec.ofNat 64 12) 32)) c 16 = bytesAt m p 16 := by
  rw [Cmac.bytesAt_store4, Cmac.le4_readW, Cmac.le4_readW, Cmac.le4_readW, Cmac.le4_readW, Cmac.bytesAt_split4]

/-! ## The tail zeroed, and the string copied onto it -/

theorem shortA_ok {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {s : State} (E : VG.Proof.AesSiv.X86.Env C W SP s) {P : BitVec 32} {k : Nat}
    (hp : slotv s.mem W strO = P) (hk : slotv s.mem W slenO = BitVec.ofNat 32 k) :
    ∃ s', runBlock isa (zero4 tailOff ++ zero4 (tailOff + 16) ++
        ([.mov .edi (slot strO), .mov .edx (.reg .ebp), .alu .add .edx (imm tailOff), .mov .ecx (slot slenO)] :
          List Instr)) s = some s' ∧
      s'.mem = Cmac.zero4 (Cmac.zero4 s.mem (w64 W + BitVec.ofNat 64 32)) (w64 W + BitVec.ofNat 64 48) ∧
      s'.gpr .edi = P ∧ s'.gpr .edx = W + BitVec.ofNat 32 32 ∧ s'.gpr .ecx = BitVec.ofNat 32 k ∧
      s'.gpr .ebp = W ∧ s'.gpr .esp = SP ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have z₁ := zero4_fold s.mem W tailOff
  have z₂ := zero4_fold (Cmac.zero4 s.mem (w64 W + BitVec.ofNat 64 tailOff)) W (tailOff + 16)
  simp only [Nat.reduceAdd, tailOff] at z₁ z₂
  refine ⟨_, by crun [zero4, E.ebp, L.aW, E.perm.wW, E.perm.wR, hp, hk], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cmems [z₁, z₂]
  · cregs [hp]
  · cregs [E.ebp]
  · cregs [hk]
  · cregs [E.ebp]
  · cregs [E.esp]
  all_goals cmems []

/-- `copyN`: the `k` bytes at `P` copied to `Q` (none if `k = 0`). -/
theorem copyN_ok {s : State} {P Q : BitVec 32} {k : Nat} (hdi : s.gpr .edi = P) (hdx : s.gpr .edx = Q)
    (hcx : s.gpr .ecx = BitVec.ofNat 32 k) (hk : k < 2 ^ 32) (fP : P.toNat + k ≤ 2 ^ 32) (fQ : Q.toNat + k ≤ 2 ^ 32)
    (rP : Covers [⟨w64 P, k⟩] (s.rd ++ s.wr)) (wQ : Covers [⟨w64 Q, k⟩] s.wr)
    (d : (⟨w64 P, k⟩ : Region).Disjoint ⟨w64 Q, k⟩) :
    WP isa copyN s fun s' => s'.mem = VG.WriteBytes.writeBytes s.mem (w64 Q) (bytesAt s.mem (w64 P) k) ∧
      (∀ r, r ≠ .eax → r ≠ .edi → r ≠ .edx → r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.seq (WP.of_runBlock ⟨_, by crun [hcx], ?_⟩)
  refine WP.ite (decide (k = 0)) (VG.Proof.AesSiv.X86.eval_e (by cmems [hcx]; rw [Proof.AesGcm.X86.and_self_beq32 hk]))
    (fun hz => ?_) (fun hz => ?_)
  · have h0 : k = 0 := of_decide_eq_true hz
    subst h0
    refine WP.block_nil ⟨?_, fun r _ _ _ _ => ?_, ?_, ?_⟩
    · cmems []; simp only [Spec.Aes.bytesAt, List.range_zero, List.map_nil, VG.WriteBytes.writeBytes_nil]
    all_goals cmems []
  · have h0 : k ≠ 0 := of_decide_eq_false hz
    refine WP.mono (copyLoop_ok _ ⟨by cregs [hdi], by cregs [hdx], by cregs [hcx], by omega, hk, fP, fQ,
      by cmems []; exact rP, by cmems []; exact wQ, d⟩) fun s' c => ⟨?_, fun r h₁ h₂ h₃ h₄ => ?_, ?_, ?_⟩
    · rw [c.mem]; cmems []
    · rw [c.other r h₁ h₂ h₃ h₄]; cregs []
    · rw [c.rd]; cmems []
    · rw [c.wr]; cmems []

/-! ## `0x80` appended, and `D` copied to `W + 160` -/

theorem b80 : (BitVec.ofNat 32 128).setWidth 8 = (0x80 : Byte) := by decide

/-- The memory after appending `0x80` to the `k` bytes at `W + 32` and
copying `D` to `W + 160`. -/
abbrev padMem (m : Mem) (W : BitVec 32) (k : Nat) : Mem :=
  let p := w64 W + BitVec.ofNat 64 dOff
  Cmac.store4 (m.writeW (w64 W + BitVec.ofNat 64 32 + BitVec.ofNat 64 k) (0x80 : Byte))
    (w64 W + BitVec.ofNat 64 dbOff) (m.readW p 32) (m.readW (p + BitVec.ofNat 64 4) 32)
    (m.readW (p + BitVec.ofNat 64 8) 32) (m.readW (p + BitVec.ofNat 64 12) 32)

theorem shortB_ok {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {s : State} (E : VG.Proof.AesSiv.X86.Env C W SP s) {k : Nat}
    (hk : slotv s.mem W slenO = BitVec.ofNat 32 k) (hk16 : k < 16) :
    ∃ s', runBlock isa [.mov .edx (.reg .ebp), .alu .add .edx (slot slenO), .mov .eax (imm 0x80),
        .store8 (at_ .edx tailOff) .al,
        .mov .eax (slot dOff), .store (at_ .ebp dbOff) .eax, .mov .eax (slot (dOff + 4)),
        .store (at_ .ebp (dbOff + 4)) .eax, .mov .eax (slot (dOff + 8)), .store (at_ .ebp (dbOff + 8)) .eax,
        .mov .eax (slot (dOff + 12)), .store (at_ .ebp (dbOff + 12)) .eax] s = some s' ∧
      s'.mem = VG.Proof.AesSiv.X86.padMem s.mem W k ∧ s'.gpr .ebp = W ∧ s'.gpr .esp = SP ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have pB : (W + BitVec.ofNat 32 k + BitVec.ofNat 32 tailOff).setWidth 64 =
      w64 W + BitVec.ofNat 64 32 + BitVec.ofNat 64 k := by
    rw [VG.Proof.AesSiv.X86.add32_assoc, VG.Proof.AesSiv.X86.add_ofNat_assoc, Nat.add_comm]; exact L.aW (by simp only [tailOff]; omega)
  have wB : InRegions s.wr (w64 W + BitVec.ofNat 64 32 + BitVec.ofNat 64 k) 1 := by
    rw [VG.Proof.AesSiv.X86.add_ofNat_assoc]; exact E.perm.wW (by omega)
  refine ⟨_, by crun [E.ebp, L.aW, E.perm.wW, E.perm.wR, hk, pB, wB, VG.Proof.AesSiv.X86.b80], ?_, ?_, ?_, ?_, ?_⟩
  · cmems [hk, pB, VG.Proof.AesSiv.X86.b80, VG.Proof.AesSiv.X86.padMem, Cmac.store4, VG.Proof.AesSiv.X86.add_ofNat_assoc]
  · cregs [E.ebp]
  · cregs [E.esp]
  all_goals cmems []

/-! ## The tail -/

theorem xorTail_ok {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {s : State} (E : VG.Proof.AesSiv.X86.Env C W SP s) :
    ∃ s', runBlock isa (([.mov .edx (.reg .ebp)] : List Instr) ++ xorInto dbOff tailOff) s = some s' ∧
      s'.mem = Cmac.xor4Mem s.mem (w64 W + BitVec.ofNat 64 tailOff) (w64 W + BitVec.ofNat 64 dbOff)
        (w64 W + BitVec.ofNat 64 tailOff) ∧
      s'.gpr .ebp = W ∧ s'.gpr .esp = SP ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [xorInto, E.ebp, L.aW, E.perm.wW, E.perm.wR], ?_, ?_, ?_, ?_, ?_⟩
  · cmems [Cmac.xor4Mem, VG.Proof.AesSiv.X86.add_ofNat_assoc]
  · cregs [E.ebp]
  · cregs [E.esp]
  all_goals cmems []

/-- `shortTail`: the tail at `W + 32` is `dbl(D) ⊕ pad(P)`. -/
theorem shortTail_ok {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {R : Nat} {P : BitVec 32} {k : Nat} {s : State}
    (h : VG.Proof.AesSiv.X86.CmacPre C W SP R P k s) (hk16 : k < 16) :
    WP isa shortTail s fun s' => VG.Proof.AesSiv.X86.Env C W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨w64 W + BitVec.ofNat 64 32, 32⟩, ⟨w64 W + BitVec.ofNat 64 144, 32⟩] s.mem s'.mem ∧
      bytesAt s'.mem (w64 W + BitVec.ofNat 64 32) 16 =
        Spec.Siv.xor (Spec.Siv.dbl (bytesAt s.mem (w64 W + BitVec.ofNat 64 dOff) 16))
          (Spec.Siv.pad (bytesAt s.mem (w64 P) k)) := by
  have E := h.env
  have B := h.buf
  obtain ⟨s₁, run₁, m₁, di₁, dx₁, cx₁, bp₁, sp₁, rd₁, wr₁⟩ := VG.Proof.AesSiv.X86.shortA_ok L E h.str h.slen
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have E₁ : VG.Proof.AesSiv.X86.Env C W SP s₁ := ⟨bp₁, sp₁, E.perm.of_eq rd₁ wr₁⟩
  have hw := L.fw
  refine WP.seq (WP.mono (VG.Proof.AesSiv.X86.copyN_ok di₁ dx₁ cx₁ h.k32 B.wrap (by rw [L.nW (by decide)]; omega)
    (by rw [rd₁, wr₁]; exact B.rd) (by rw [L.aW (by decide)]; exact E₁.perm.wC (by omega))
    (by rw [L.aW (by decide)]; exact B.w.sub_right (Lay.wSub (by omega)))) fun s₂ ⟨m₂, g₂, rd₂, wr₂⟩ => ?_)
  have E₂ : VG.Proof.AesSiv.X86.Env C W SP s₂ := ⟨by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), bp₁],
    by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), sp₁], E₁.perm.of_eq rd₂ wr₂⟩
  -- The length's slot, still.
  have f₁ : Frame [⟨w64 W + BitVec.ofNat 64 32, 32⟩] s.mem s₁.mem := by
    rw [m₁]
    exact ((Cmac.frame_store4 _ _ _ _ _).sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by decide) (by decide)⟩).trans
      ((Cmac.frame_store4 _ _ _ _ _).sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by decide) (by decide)⟩)
  have hlen : (bytesAt s₁.mem (w64 P) k).length = k := length_bytesAt _ _ _
  have f₂ : Frame [⟨w64 W + BitVec.ofNat 64 32, 32⟩] s₁.mem s₂.mem := by
    rw [m₂, L.aW (by decide)]
    exact VG.WriteBytes.writeBytes_frame _ _ _ (by
      rw [hlen]; exact Offset.contains (w64 W) (d := 32) (n := k) (e := 32) (k := 32) (by omega) (by omega)
        (by omega))
  have f₁₂ := f₁.trans f₂
  have k₂ : slotv s₂.mem W slenO = BitVec.ofNat 32 k :=
    (f₁₂.readW (w := 32) (r := ⟨w64 W + BitVec.ofNat 64 slenO, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by decide)) (by decide) (by decide))
      (by decide)).trans h.slen
  -- `0x80`, `D` copied and doubled, and the XOR.
  obtain ⟨s₃, run₃, m₃, bp₃, sp₃, rd₃, wr₃⟩ := VG.Proof.AesSiv.X86.shortB_ok L E₂ k₂ hk16
  have E₃ : VG.Proof.AesSiv.X86.Env C W SP s₃ := ⟨bp₃, sp₃, E₂.perm.of_eq rd₃ wr₃⟩
  have e : (([.mov .edx (.reg .ebp), .alu .add .edx (slot slenO), .mov .eax (imm 0x80),
        .store8 (at_ .edx tailOff) .al,
        .mov .eax (slot dOff), .store (at_ .ebp dbOff) .eax, .mov .eax (slot (dOff + 4)),
        .store (at_ .ebp (dbOff + 4)) .eax, .mov .eax (slot (dOff + 8)), .store (at_ .ebp (dbOff + 8)) .eax,
        .mov .eax (slot (dOff + 12)), .store (at_ .ebp (dbOff + 12)) .eax] : List Instr) ++ dblAt dbOff ++
        ([.mov .edx (.reg .ebp)] : List Instr) ++ xorInto dbOff tailOff) =
      [.mov .edx (.reg .ebp), .alu .add .edx (slot slenO), .mov .eax (imm 0x80),
        .store8 (at_ .edx tailOff) .al,
        .mov .eax (slot dOff), .store (at_ .ebp dbOff) .eax, .mov .eax (slot (dOff + 4)),
        .store (at_ .ebp (dbOff + 4)) .eax, .mov .eax (slot (dOff + 8)), .store (at_ .ebp (dbOff + 8)) .eax,
        .mov .eax (slot (dOff + 12)), .store (at_ .ebp (dbOff + 12)) .eax] ++
      (dblAt dbOff ++ (([.mov .edx (.reg .ebp)] : List Instr) ++ xorInto dbOff tailOff)) := by
    simp only [List.append_assoc]
  rw [e, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  refine VG.Proof.AesSiv.X86.dblAt_wp L E₃ (o := dbOff) (by decide) fun s₄ bp₄ sp₄ m₄ rd₄ wr₄ => ?_
  have E₄ : VG.Proof.AesSiv.X86.Env C W SP s₄ := ⟨bp₄, sp₄, E₃.perm.of_eq rd₄ wr₄⟩
  obtain ⟨s₅, run₅, m₅, bp₅, sp₅, rd₅, wr₅⟩ := VG.Proof.AesSiv.X86.xorTail_ok L E₄
  refine WP.of_runBlock ⟨s₅, run₅, ⟨bp₅, sp₅, E₄.perm.of_eq rd₅ wr₅⟩, by rw [rd₅, rd₄, rd₃, rd₂, rd₁],
    by rw [wr₅, wr₄, wr₃, wr₂, wr₁], ?_, ?_⟩
  · -- What it writes.
    have f₃ : Frame [⟨w64 W + BitVec.ofNat 64 32, 32⟩, ⟨w64 W + BitVec.ofNat 64 144, 32⟩] s₂.mem s₃.mem := by
      rw [m₃, VG.Proof.AesSiv.X86.padMem]
      exact ((Frame.refl _ _).writeW (List.mem_cons_self) _ (by
        rw [VG.Proof.AesSiv.X86.add_ofNat_assoc]; exact Offset.contains (w64 W) (d := 32 + k) (n := 1) (e := 32) (k := 32) (by omega)
          (by omega) (by omega))).trans ((Cmac.frame_store4 _ _ _ _ _).sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨⟨w64 W + BitVec.ofNat 64 144, 32⟩, by simp, Offset.sub (d := dbOff) (n := 16) (e := 144) (k := 32) _
          (by decide) (by decide)⟩)
    have f₄ : Frame [⟨w64 W + BitVec.ofNat 64 144, 32⟩] s₃.mem s₄.mem := by
      rw [m₄]
      exact (Proof.CmacAes.X86.dblMem_frame _ _ _ _).sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, by rw [BitVec.add_zero]; exact Offset.sub _ (by decide) (by decide)⟩
    have f₅ : Frame [⟨w64 W + BitVec.ofNat 64 32, 32⟩] s₄.mem s₅.mem := by
      rw [m₅]
      exact (Cmac.xor4Mem_frame _ _ _ _).sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
    exact ((f₁₂.sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩).trans f₃).trans
      ((f₄.sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩).trans (f₅.sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩))
  · -- `dbl(D) ⊕ pad(P)`.
    have d32 : (⟨w64 W + BitVec.ofNat 64 32, 16⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 160, 16⟩ :=
      Lay.w_w (.inl (by decide)) (by decide) (by decide)
    rw [m₅, show tailOff = 32 from rfl, show dbOff = 160 from rfl,
      Cmac.xor4Mem_bytes _ (Cmac.Sep4.of_disjoint d32) (Cmac.Sep4.self _)]
    have t₄ : bytesAt s₄.mem (w64 W + BitVec.ofNat 64 32) 16 = bytesAt s₃.mem (w64 W + BitVec.ofNat 64 32) 16 :=
      Proof.AesGcm.X86.bytesAt_frame (rs := [⟨w64 W + BitVec.ofNat 64 160 + BitVec.ofNat 64 0, 16⟩])
        (by rw [m₄]; exact Proof.CmacAes.X86.dblMem_frame _ _ _ _)
        (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [BitVec.add_zero]; exact d32) (by decide)
    have q₄ : bytesAt s₄.mem (w64 W + BitVec.ofNat 64 160) 16 =
        Spec.Cmac.dbl 16 (bytesAt s₃.mem (w64 W + BitVec.ofNat 64 160) 16) := by
      have := Proof.CmacAes.X86.dblMem_bytes s₃.mem (w64 W + BitVec.ofNat 64 160) 0 0
      rw [BitVec.add_zero] at this
      rw [m₄]; exact this
    have q₃ : bytesAt s₃.mem (w64 W + BitVec.ofNat 64 160) 16 = bytesAt s₂.mem (w64 W + BitVec.ofNat 64 2560) 16 := by
      rw [m₃]; exact VG.Proof.AesSiv.X86.copy4_bytes _ _ _ _
    have t₃ : bytesAt s₃.mem (w64 W + BitVec.ofNat 64 32) 16 = bytesAt (s₂.mem.writeW
        (w64 W + BitVec.ofNat 64 32 + BitVec.ofNat 64 k) (0x80 : Byte)) (w64 W + BitVec.ofNat 64 32) 16 := by
      rw [m₃]
      exact Proof.AesGcm.X86.bytesAt_frame (Cmac.frame_store4 _ _ _ _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact d32) (by decide)
    have hz : bytesAt s₁.mem (w64 W + BitVec.ofNat 64 32) 16 = Spec.Cmac.zeros 16 := by
      have fz : Frame [⟨w64 W + BitVec.ofNat 64 48, 16⟩] (Cmac.zero4 s.mem (w64 W + BitVec.ofNat 64 32)) s₁.mem := by
        rw [m₁]; exact Cmac.frame_store4 _ _ _ _ _
      rw [Proof.AesGcm.X86.bytesAt_frame fz (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide))
        (by decide)]
      exact Cmac.zero4_bytes _ _
    have pad := Cmac.padded_bytes s₁.mem (w64 W + BitVec.ofNat 64 32) (bytesAt s₁.mem (w64 P) k)
      (by rw [hlen]; exact hk16) hz
    rw [hlen] at pad
    have hP : bytesAt s₁.mem (w64 P) k = bytesAt s.mem (w64 P) k :=
      Proof.AesGcm.X86.bytesAt_frame f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact B.w.sub_right (Lay.wSub (by decide)))
        (by have := B.lt; omega)
    have hD : bytesAt s₂.mem (w64 W + BitVec.ofNat 64 2560) 16 = bytesAt s.mem (w64 W + BitVec.ofNat 64 2560) 16 :=
      Proof.AesGcm.X86.bytesAt_frame f₁₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by decide)) (by decide) (by decide))
        (by decide)
    rw [t₄, q₄, q₃, hD, t₃, m₂, L.aW (o := 32) (by decide), pad, hP, Siv.xor_eq, Spec.Siv.pad,
      show 16 - k - 1 = 15 - k by omega, length_bytesAt]
    rfl

/-! ## What `finish` leaves -/

/-- The parts of `W` `finish` writes: the output, the tail, the CMAC state and
`dbl(D)`, the variables, the working space of the functions called, and the
stack below `SP`. -/
abbrev finR (W SP : BitVec 32) (out : Nat) : List Region :=
  [⟨w64 W + BitVec.ofNat 64 out, 16⟩, ⟨w64 W + BitVec.ofNat 64 32, 32⟩, ⟨w64 W + BitVec.ofNat 64 144, 32⟩, VG.Proof.AesSiv.X86.wS W,
    ⟨w64 W + BitVec.ofNat 64 256, 2176⟩, below SP 56]

/-- What `finish out` leaves: S2V's end, from `D` and the string `P`, at
`W + out`. -/
structure FinPost (C W SP : BitVec 32) (R out : Nat) (P : BitVec 32) (k : Nat) (s s' : State) : Prop where
  env : VG.Proof.AesSiv.X86.Env C W SP s'
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame (VG.Proof.AesSiv.X86.finR W SP out) s.mem s'.mem
  out : bytesAt s'.mem (w64 W + BitVec.ofNat 64 out) 16 =
    Spec.Siv.s2vFinish (Spec.Siv.ctxMac s.mem (w64 C) R) (bytesAt s.mem (w64 W + BitVec.ofNat 64 dOff) 16)
      (bytesAt s.mem (w64 P) k)

theorem finR_c {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {out : Nat} (hout : out = 0 ∨ out = 112) :
    ∀ r ∈ VG.Proof.AesSiv.X86.finR W SP out, (⟨w64 C, 512⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact L.c_w.sub_right (Lay.wSub (by omega))
  · exact L.c_w.sub_right (Lay.wSub (by decide))
  · exact L.c_w.sub_right (Lay.wSub (by decide))
  · exact L.c_w.sub_right (Lay.wSub (by decide))
  · exact L.c_w.sub_right (Lay.wSub (by decide))
  · exact L.stk_c.symm

/-! ## The short case's call -/

theorem macPre_ok {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {R : Nat} {s : State} (E : VG.Proof.AesSiv.X86.Env C W SP s)
    (hc : slotv s.mem W ctxO = C) (hr : slotv s.mem W roundsO = BitVec.ofNat 32 R) {out : Nat}
    (hout : out = 0 ∨ out = 112) :
    ∃ s', runBlock isa (zero4 out ++ macArgs out ++ ([.mov .ebx (.reg .ebp), .alu .add .ebx (imm tailOff),
        .mov .esi (imm 16)] : List Instr)) s = some s' ∧
      s'.mem = Cmac.zero4 s.mem (w64 W + BitVec.ofNat 64 out) ∧
      s'.gpr .eax = C ∧ s'.gpr .ecx = BitVec.ofNat 32 R ∧ s'.gpr .edx = W + BitVec.ofNat 32 out ∧
      s'.gpr .ebx = W + BitVec.ofNat 32 32 ∧ s'.gpr .esi = BitVec.ofNat 32 16 ∧
      s'.gpr .edi = W + BitVec.ofNat 32 256 ∧ s'.gpr .ebp = W ∧ s'.gpr .esp = SP ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have z := zero4_fold s.mem W out
  rcases hout with rfl | rfl
  all_goals
    simp only [Nat.reduceAdd] at z
    refine ⟨_, by crun [zero4, macArgs, E.ebp, L.aW, E.perm.wW, E.perm.wR, hc, hr], ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_⟩
    · cmems [z]
    · cregs [hc]
    · cregs [hr]
    · cregs [E.ebp]
    · cregs [E.ebp]
    · cregs []
    · cregs [E.ebp]
    · cregs [E.ebp]
    · cregs [E.esp]
    all_goals cmems []

/-- A complete block's CMAC from the context's subkeys. -/
theorem ctxMac_block (m : Mem) (C : Addr) (R : Nat) {T : List Byte} (hT : T.length = 16) :
    Spec.Siv.ctxMac m C R T = Spec.Cmac.aesWith R (bytesAt m C (16 * (R + 1)))
      (Spec.Cmac.xor (Spec.Cmac.lastBlock 16 (bytesAt m (C + BitVec.ofNat 64 240) 16)
        (bytesAt m (C + BitVec.ofNat 64 256) 16) T) (Spec.Cmac.zeros 16)) := by
  have := Siv.cmacWith_split (Spec.Siv.schedCiph m C R) (bytesAt m (C + 240) 16) (bytesAt m (C + 256) 16)
    (msg := []) (last := T) (by decide) (by omega) (.inl rfl)
  simp only [List.nil_append] at this
  rw [Spec.Siv.ctxMac, this, Proof.Cmac.xor_comm]
  rfl

/-- The short case: the tail's CMAC, one complete block, into `W + out`. -/
theorem finishShort_ok (v : Ctr32Impl) {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {P : BitVec 32} {k : Nat} {s : State} (h : VG.Proof.AesSiv.X86.CmacPre C W SP R P k s)
    (hk16 : k < 16) {out : Nat} (hout : out = 0 ∨ out = 112) :
    WP isa (.seq shortTail (shortMac v.callee v.suffix out)) s (VG.Proof.AesSiv.X86.FinPost C W SP R out P k s) := by
  have hRb : R ≤ 14 := by omega
  refine WP.seq (WP.mono (VG.Proof.AesSiv.X86.shortTail_ok L h hk16) fun s₁ ⟨E₁, rd₁, wr₁, f₁, t₁⟩ => ?_)
  have k₁ : ∀ o, 176 ≤ o → o + 4 ≤ 200 → slotv s₁.mem W o = slotv s.mem W o := fun o h₁ h₂ =>
    f₁.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Lay.w_w (.inr (by omega)) (by omega) (by decide)
      · exact Lay.w_w (.inr (by omega)) (by omega) (by decide)) (by decide)
  obtain ⟨s₂, run₂, m₂, ax₂, cx₂, dx₂, bx₂, si₂, di₂, bp₂, sp₂, rd₂, wr₂⟩ := VG.Proof.AesSiv.X86.macPre_ok L E₁
    (by rw [k₁ _ (by decide) (by decide)]; exact h.ctx) (by rw [k₁ _ (by decide) (by decide)]; exact h.rounds) hout
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have E₂ : VG.Proof.AesSiv.X86.Env C W SP s₂ := ⟨bp₂, sp₂, E₁.perm.of_eq rd₂ wr₂⟩
  have dO : (⟨w64 W + BitVec.ofNat 64 out, 16⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 32, 16⟩ := by
    rcases hout with rfl | rfl <;> exact Lay.w_w (by decide) (by decide) (by decide)
  refine WP.mono (VG.Proof.AesSiv.X86.finCall_ok v L E₂ hR (y := out) (.inl (by omega)) (P := W + BitVec.ofNat 32 32) (l := 16)
    (Nat.le_refl _) (VG.Proof.AesSiv.X86.srcW L E₂.perm (t := 32) (k := 16) (by decide))
    (by rw [L.aW (o := 32) (by decide)]; exact dO.symm) ax₂ cx₂ dx₂ bx₂ si₂ di₂)
    fun s₃ ⟨E₃, rd₃, wr₃, _, f₃, o₃⟩ => ⟨E₃, by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁], ?_, ?_⟩
  · have fz : Frame [⟨w64 W + BitVec.ofNat 64 out, 16⟩] s₁.mem s₂.mem := by
      rw [m₂]; exact Cmac.frame_store4 _ _ _ _ _
    refine ((f₁.sub fun r hr => ?_).trans (fz.sub fun r hr => ?_)).trans (f₃.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  · have fz : Frame [⟨w64 W + BitVec.ofNat 64 out, 16⟩] s₁.mem s₂.mem := by
      rw [m₂]; exact Cmac.frame_store4 _ _ _ _ _
    have hz : bytesAt s₂.mem (w64 W + BitVec.ofNat 64 out) 16 = Spec.Cmac.zeros 16 := by
      rw [m₂]; exact Cmac.zero4_bytes _ _
    have hT : bytesAt s₂.mem (w64 W + BitVec.ofNat 64 32) 16 = bytesAt s₁.mem (w64 W + BitVec.ofNat 64 32) 16 :=
      Proof.AesGcm.X86.bytesAt_frame fz (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dO.symm) (by decide)
    have hc : Spec.Siv.ctxMac s₂.mem (w64 C) R = Spec.Siv.ctxMac s.mem (w64 C) R :=
      (VG.Proof.AesSiv.X86.ctxMac_frame fz (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.c_w.sub_right (Lay.wSub (by omega))) hRb).trans
      (VG.Proof.AesSiv.X86.ctxMac_frame f₁ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact L.c_w.sub_right (Lay.wSub (by decide))) hRb)
    rw [o₃, L.aW (o := 32) (by decide), hz, hT, Siv.s2vFinish_short _ _ (by rw [length_bytesAt]; exact hk16), ← t₁,
      ← hc, VG.Proof.AesSiv.X86.ctxMac_block _ _ _ (length_bytesAt _ _ _)]

end VG.Proof.AesSiv.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.X86.FinishLong`. -/
section

/-!
# AES-SIV on x86: finishing S2V with a string of a block or more

Untrusted: everything here is checked by Lean. For a last string `P` of
`L ≥ 16` bytes, with `k = kOf L` and `j = jOf L` (`Proof/AesSiv/Long.lean`),
the last `T = L − 16 k` bytes of `P` are copied to the tail at `W + 32` and
`D` XORed into its last 16 (`longTail_ok`, `xorend4_mem`): the tail is
`P[16k..] xorend D`. Then the `k` blocks of `P` and the first `j` of the
tail are chained into a zero state at `W + out` and the rest of the tail
finalized (`longMac_ok`), which is S2V's end (`long_spec`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesSiv.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4 copyLoop)
open VG.Proof.AesGcm.X86 (w64 toNat_ofNat32 toNat_add32 slotv zero4_fold length_bytesAt readW_writeW_off
  covers_left LoopPre CopyPost copyLoop_ok ofNat_sub32 CT shr4)

/-- `D` XORed into the last 16 of the `T` bytes at `B`, a word at a time. -/
theorem xorend4_mem (m : Mem) {B Q : Addr} {T : Nat} (hT : 16 ≤ T) (hw : B.toNat + T ≤ 2 ^ 64)
    (hd : (⟨B, T⟩ : Region).Disjoint ⟨Q, 16⟩) :
    bytesAt (Cmac.xor4Mem m (B + BitVec.ofNat 64 (T - 16)) Q (B + BitVec.ofNat 64 (T - 16))) B T =
      Spec.Siv.xorend (bytesAt m B T) (bytesAt m Q 16) := by
  have hc : Region.Sub ⟨B + BitVec.ofNat 64 (T - 16), 16⟩ ⟨B, T⟩ := Offset.sub_base B (by omega)
  have e : T = (T - 16) + 16 := by omega
  have hs := Proof.Cmac.Stream.bytesAt_append (Cmac.xor4Mem m (B + BitVec.ofNat 64 (T - 16)) Q
    (B + BitVec.ofNat 64 (T - 16))) B (T - 16) 16
  rw [← e] at hs
  rw [hs, Spec.Siv.xorend, Proof.Cmac.bytesAt_length, Proof.Cmac.bytesAt_length]
  have tk := take_bytesAt m B (a := T - 16) (b := 16)
  have dr := drop_bytesAt m B (a := T - 16) (b := 16)
  rw [← e] at tk dr
  rw [tk, dr, Proof.AesGcm.X86.bytesAt_frame (Cmac.xor4Mem_frame _ _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.base_disjoint B (by omega) (by omega)) (by omega),
    Cmac.xor4Mem_bytes m (c := B + BitVec.ofNat 64 (T - 16)) (p := Q) (q := B + BitVec.ofNat 64 (T - 16))
      (Cmac.Sep4.of_disjoint (hd.sub_left hc)) (Cmac.Sep4.self _), Siv.xor_eq,
    Proof.Cmac.xor_comm]

/-! ## The tail -/

theorem cmp17_ok {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {s : State} (E : VG.Proof.AesSiv.X86.Env C W SP s) {k : Nat}
    (hk : slotv s.mem W slenO = BitVec.ofNat 32 k) (hk32 : k < 2 ^ 32) :
    ∃ s', runBlock isa [.mov .eax (imm 0), .mov .ecx (slot slenO), .alu .cmp .ecx (imm 17)] s = some s' ∧
      s'.gpr .eax = BitVec.ofNat 32 0 ∧ s'.gpr .ecx = BitVec.ofNat 32 k ∧ s'.cf = some (decide (k < 17)) ∧
      s'.gpr .ebp = W ∧ s'.gpr .esp = SP ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [E.ebp, L.aW, E.perm.wR, hk], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cregs []
  · cregs [hk]
  · cmems [hk, VG.Proof.AesGcm.X86.toNat_ofNat32 hk32]; rfl
  · cregs [E.ebp]
  · cregs [E.esp]
  all_goals cmems []

/-- `16 k` in `eax`, from the comparison of the length with 17. -/
theorem kBranch_wp {s : State} {k : Nat} (hax : s.gpr .eax = BitVec.ofNat 32 0)
    (hcx : s.gpr .ecx = BitVec.ofNat 32 k) (hcf : s.cf = some (decide (k < 17))) (h16 : 16 ≤ k) (hk32 : k < 2 ^ 32) :
    WP isa (.ite .b (.block []) (.block [.mov .eax (.reg .ecx), .alu .sub .eax (imm 1),
        .alu .and .eax (imm 0xfffffff0), .alu .sub .eax (imm 16)])) s fun s' =>
      s'.gpr .eax = BitVec.ofNat 32 (16 * kOf k) ∧ s'.gpr .ecx = BitVec.ofNat 32 k ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.ite (decide (k < 17)) (VG.Proof.AesSiv.X86.eval_b hcf) (fun ht => ?_) (fun hf => ?_)
  · have h₁ := of_decide_eq_true ht
    refine WP.block_nil ⟨by rw [hax, kOf_lt h₁], hcx, fun _ _ => rfl, rfl, rfl, rfl⟩
  · have h₁ := of_decide_eq_false hf
    refine WP.of_runBlock ⟨_, by crun [], ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
    · cregs [hcx]
      rw [ofNat_sub32 (by omega) hk32, Proof.AesSiv.X86.and_m16, VG.Proof.AesGcm.X86.toNat_ofNat32 (by omega),
        ofNat_sub32 (by omega) (by omega), kOf_ge h₁]
      congr 1
      omega
    · cregs [hcx]
    · cregs []
    all_goals cmems []

/-- `D` XORed into the last 16 of the `t` bytes of the tail. -/
theorem xorEnd_ok {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {s : State} (E : VG.Proof.AesSiv.X86.Env C W SP s) {k b t : Nat}
    (hk : slotv s.mem W slenO = BitVec.ofNat 32 k) (hb : slotv s.mem W nbO = BitVec.ofNat 32 b)
    (ht : t = k - b) (hbk : b ≤ k) (hk32 : k < 2 ^ 32) (h16 : 16 ≤ t) (h32 : t ≤ 32) :
    ∃ s', runBlock isa (([.mov .edx (.reg .ebp), .alu .add .edx (slot slenO), .alu .sub .edx (slot nbO)] :
        List Instr) ++ xorInto dOff (tailOff - 16)) s = some s' ∧
      s'.mem = Cmac.xor4Mem s.mem (w64 W + BitVec.ofNat 64 (t + 16)) (w64 W + BitVec.ofNat 64 dOff)
        (w64 W + BitVec.ofNat 64 (t + 16)) ∧
      s'.gpr .ebp = W ∧ s'.gpr .esp = SP ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hdx : W + BitVec.ofNat 32 k - BitVec.ofNat 32 b = W + BitVec.ofNat 32 t := by
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg, ofNat_sub32 hbk hk32, ht]
  refine ⟨_, by crun [xorInto, E.ebp, L.aW, E.perm.wW, E.perm.wR, hk, hb, hdx, VG.Proof.AesSiv.X86.add32_assoc], ?_, ?_, ?_, ?_, ?_⟩
  · cmems [hk, hb, hdx, VG.Proof.AesSiv.X86.add32_assoc, Cmac.xor4Mem, VG.Proof.AesSiv.X86.add_ofNat_assoc, Nat.add_assoc]
  · cregs [E.ebp]
  · cregs [E.esp]
  all_goals cmems []

theorem tailArgs_ok {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {s : State} (E : VG.Proof.AesSiv.X86.Env C W SP s) {P a c : BitVec 32}
    (hax : s.gpr .eax = a) (hcx : s.gpr .ecx = c) (hp : slotv s.mem W strO = P) :
    ∃ s', runBlock isa [.store (at_ .ebp nbO) .eax, .mov .edi (slot strO), .alu .add .edi (.reg .eax),
        .alu .sub .ecx (.reg .eax), .mov .edx (.reg .ebp), .alu .add .edx (imm tailOff)] s = some s' ∧
      s'.mem = s.mem.writeW (w64 W + BitVec.ofNat 64 nbO) a ∧ s'.gpr .edi = P + a ∧ s'.gpr .ecx = c - a ∧
      s'.gpr .edx = W + BitVec.ofNat 32 32 ∧ s'.gpr .ebp = W ∧ s'.gpr .esp = SP ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [E.ebp, L.aW, E.perm.wW, E.perm.wR, hax, hp], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cmems [hax]
  · cregs [hax, hp]
  · cregs [hax, hcx]
  · cregs [E.ebp]
  · cregs [E.ebp]
  · cregs [E.esp]
  all_goals cmems []

/-- `longTail`: the tail at `W + 32` is `P[16k..] xorend D`, and `16 k` at
`W + nbO`. -/
theorem longTail_ok {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {R : Nat} {P : BitVec 32} {k : Nat} {s : State}
    (h : VG.Proof.AesSiv.X86.CmacPre C W SP R P k s) (h16 : 16 ≤ k) :
    WP isa longTail s fun s' => VG.Proof.AesSiv.X86.Env C W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨w64 W + BitVec.ofNat 64 32, 32⟩, ⟨w64 W + BitVec.ofNat 64 nbO, 4⟩] s.mem s'.mem ∧
      slotv s'.mem W nbO = BitVec.ofNat 32 (16 * kOf k) ∧
      bytesAt s'.mem (w64 W + BitVec.ofNat 64 32) (k - 16 * kOf k) =
        Spec.Siv.xorend ((bytesAt s.mem (w64 P) k).drop (16 * kOf k))
          (bytesAt s.mem (w64 W + BitVec.ofNat 64 dOff) 16) := by
  have E := h.env
  have B := h.buf
  have hk32 := h.k32
  have hT := kOf_tail h16
  obtain ⟨s₁, run₁, ax₁, cx₁, cf₁, bp₁, sp₁, m₁, rd₁, wr₁⟩ := VG.Proof.AesSiv.X86.cmp17_ok L E h.slen hk32
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (VG.Proof.AesSiv.X86.kBranch_wp ax₁ cx₁ cf₁ h16 hk32) fun s₂ ⟨ax₂, cx₂, g₂, m₂, rd₂, wr₂⟩ => ?_)
  have E₂ : VG.Proof.AesSiv.X86.Env C W SP s₂ := ⟨by rw [g₂ _ (by decide), bp₁], by rw [g₂ _ (by decide), sp₁],
    E.perm.of_eq (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])⟩
  obtain ⟨s₃, run₃, m₃, di₃, cx₃, dx₃, bp₃, sp₃, rd₃, wr₃⟩ := VG.Proof.AesSiv.X86.tailArgs_ok L E₂ (P := P) ax₂ cx₂
    (by rw [m₂, m₁]; exact h.str)
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have E₃ : VG.Proof.AesSiv.X86.Env C W SP s₃ := ⟨bp₃, sp₃, E₂.perm.of_eq rd₃ wr₃⟩
  have hkk : 16 * kOf k ≤ k := by omega
  have hwk : P.toNat + 16 * kOf k < 2 ^ 32 := by have := B.wrap; omega
  have B₃ : VG.Proof.AesSiv.X86.Buf W SP s₃ (P + BitVec.ofNat 32 (16 * kOf k)) (k - 16 * kOf k) :=
    (B.drop hkk hwk).of_eq (by rw [rd₃, rd₂, rd₁]) (by rw [wr₃, wr₂, wr₁])
  have hW := L.fw
  refine WP.seq (WP.mono (copyLoop_ok s₃ ⟨di₃, dx₃, by rw [cx₃, ofNat_sub32 hkk hk32], by omega, by omega, B₃.wrap,
    by rw [L.nW (o := 32) (by decide)]; omega, B₃.rd, by rw [L.aW (by decide)]; exact E₃.perm.wC (by omega),
    by rw [L.aW (by decide)]; exact B₃.w.sub_right (Lay.wSub (by omega))⟩) fun s₄ c₄ => ?_)
  have E₄ : VG.Proof.AesSiv.X86.Env C W SP s₄ := ⟨by rw [c₄.other _ (by decide) (by decide) (by decide) (by decide), bp₃],
    by rw [c₄.other _ (by decide) (by decide) (by decide) (by decide), sp₃], E₃.perm.of_eq c₄.rd c₄.wr⟩
  -- The slots `xorEnd` reads.
  have f₃₄ : Frame [⟨w64 W + BitVec.ofNat 64 32, 32⟩] s₃.mem s₄.mem := by
    rw [c₄.mem, L.aW (by decide)]
    exact VG.WriteBytes.writeBytes_frame _ _ _ (by
      rw [length_bytesAt]; exact Offset.contains (w64 W) (d := 32) (n := k - 16 * kOf k) (e := 32) (k := 32)
        (by omega) (by omega) (by omega))
  have k₄ : ∀ o, 64 ≤ o → o + 4 ≤ 2576 → slotv s₄.mem W o = slotv s₃.mem W o := fun o h₁ h₂ =>
    f₃₄.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by omega)) (by omega) (by decide))
      (by decide)
  have nb₃ : slotv s₃.mem W nbO = BitVec.ofNat 32 (16 * kOf k) := by
    rw [m₃]; exact Mem.readW_writeW_self32 _ _ _
  have sl₃ : slotv s₃.mem W slenO = BitVec.ofNat 32 k := by
    rw [m₃, slotv, readW_writeW_off _ _ _ (by decide) (by decide) (by decide), m₂, m₁]; exact h.slen
  obtain ⟨s₅, run₅, m₅, bp₅, sp₅, rd₅, wr₅⟩ := VG.Proof.AesSiv.X86.xorEnd_ok L E₄ (by rw [k₄ _ (by decide) (by decide)]; exact sl₃)
    (by rw [k₄ _ (by decide) (by decide)]; exact nb₃) rfl hkk hk32 hT.1 hT.2
  -- What it writes.
  have f₃ : Frame [⟨w64 W + BitVec.ofNat 64 32, 32⟩, ⟨w64 W + BitVec.ofNat 64 nbO, 4⟩] s.mem s₃.mem := by
    rw [m₃, m₂, m₁]
    exact (Frame.refl _ _).writeW (r := ⟨w64 W + BitVec.ofNat 64 nbO, 4⟩) (by simp) _ (Region.contains_self _ _)
  have f₄ : Frame [⟨w64 W + BitVec.ofNat 64 32, 32⟩, ⟨w64 W + BitVec.ofNat 64 nbO, 4⟩] s.mem s₄.mem :=
    f₃.trans (f₃₄.mono (by simp))
  have f₅ : Frame [⟨w64 W + BitVec.ofNat 64 32, 32⟩] s₄.mem s₅.mem := by
    rw [m₅]
    exact (Cmac.xor4Mem_frame _ _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by omega) (by omega)⟩
  refine WP.of_runBlock ⟨s₅, run₅, ⟨bp₅, sp₅, E₄.perm.of_eq rd₅ wr₅⟩,
    by rw [rd₅, c₄.rd, rd₃, rd₂, rd₁], by rw [wr₅, c₄.wr, wr₃, wr₂, wr₁], f₄.trans (f₅.mono (by simp)), ?_, ?_⟩
  · exact ((f₅.readW (w := 32) (r := ⟨w64 W + BitVec.ofNat 64 nbO, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by decide)) (by decide) (by decide))
      (by decide)).trans (k₄ _ (by decide) (by decide))).trans nb₃
  · have e : w64 W + BitVec.ofNat 64 (k - 16 * kOf k + 16) =
        w64 W + BitVec.ofNat 64 32 + BitVec.ofNat 64 (k - 16 * kOf k - 16) := by
      rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega
    have hw : (w64 W + BitVec.ofNat 64 32).toNat + (k - 16 * kOf k) ≤ 2 ^ 64 := by
      rw [← L.aW (o := 32) (by decide), Proof.AesGcm.X86.toNat_w64, L.nW (o := 32) (by decide)]; omega
    have hd : (⟨w64 W + BitVec.ofNat 64 32, k - 16 * kOf k⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 dOff, 16⟩ :=
      Lay.w_w (.inl (by rw [show dOff = 2560 from rfl]; omega)) (by omega) (by decide)
    have hP : bytesAt s₄.mem (w64 W + BitVec.ofNat 64 32) (k - 16 * kOf k) =
        (bytesAt s.mem (w64 P) k).drop (16 * kOf k) := by
      have hl : (bytesAt s₃.mem (w64 (P + BitVec.ofNat 32 (16 * kOf k))) (k - 16 * kOf k)).length < 2 ^ 64 := by
        rw [length_bytesAt]; omega
      have := Proof.AesGcm.X86.bytesAt_writeBytes_self s₃.mem (w64 (W + BitVec.ofNat 32 32)) _ hl
      rw [length_bytesAt] at this
      rw [c₄.mem, ← L.aW (o := 32) (by decide), this, Buf.ptr hwk,
        ← drop_bytesAt s₃.mem (w64 P) (a := 16 * kOf k) (b := k - 16 * kOf k), Nat.add_sub_cancel' hkk,
        Proof.AesGcm.X86.bytesAt_frame f₃ (fun r hr => by
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
          rcases hr with rfl | rfl <;> exact B.w.sub_right (Lay.wSub (by decide)))
          (by have := B.lt; omega)]
    have hD : bytesAt s₄.mem (w64 W + BitVec.ofNat 64 dOff) 16 = bytesAt s.mem (w64 W + BitVec.ofNat 64 dOff) 16 :=
      Proof.AesGcm.X86.bytesAt_frame f₄ (fun r hr => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
        rcases hr with rfl | rfl <;> exact Lay.w_w (.inr (by decide)) (by decide) (by decide)) (by decide)
    rw [m₅, e, VG.Proof.AesSiv.X86.xorend4_mem _ hT.1 hw hd, hP, hD]

/-! ## The calls -/

/-- The zero state at `W + out`, and the arguments for the `k` blocks of `P`. -/
theorem lm1_ok {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {R : Nat} {s : State} (E : VG.Proof.AesSiv.X86.Env C W SP s)
    (hc : slotv s.mem W ctxO = C) (hr : slotv s.mem W roundsO = BitVec.ofNat 32 R) {P : BitVec 32}
    (hp : slotv s.mem W strO = P) {n : Nat} (hn : slotv s.mem W nbO = BitVec.ofNat 32 (16 * n))
    (hn32 : 16 * n < 2 ^ 32) {out : Nat} (hout : out = 0 ∨ out = 112) :
    ∃ s', runBlock isa (zero4 out ++ ([.mov .esi (slot nbO), .shift .shr .esi 4, .mov .ebx (slot strO)] :
        List Instr) ++ macArgs out) s = some s' ∧
      s'.mem = Cmac.zero4 s.mem (w64 W + BitVec.ofNat 64 out) ∧
      s'.gpr .eax = C ∧ s'.gpr .ecx = BitVec.ofNat 32 R ∧ s'.gpr .edx = W + BitVec.ofNat 32 out ∧
      s'.gpr .ebx = P ∧ s'.gpr .esi = BitVec.ofNat 32 n ∧
      s'.gpr .edi = W + BitVec.ofNat 32 256 ∧ s'.gpr .ebp = W ∧ s'.gpr .esp = SP ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have z := zero4_fold s.mem W out
  have hsh := VG.Proof.AesGcm.X86.shr4 hn32
  rw [Nat.mul_div_cancel_left _ (by decide)] at hsh
  rcases hout with rfl | rfl
  all_goals
    simp only [Nat.reduceAdd] at z
    refine ⟨_, by crun [zero4, macArgs, E.ebp, L.aW, E.perm.wW, E.perm.wR, hc, hr, hp, hn], ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · cmems [z]
    · cregs [hc]
    · cregs [hr]
    · cregs [E.ebp]
    · cregs [hp]
    · cregs [hn, hsh]
    · cregs [E.ebp]
    · cregs [E.ebp]
    · cregs [E.esp]
    all_goals cmems []

theorem cmp17s_ok {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {s : State} (E : VG.Proof.AesSiv.X86.Env C W SP s) {k : Nat}
    (hk : slotv s.mem W slenO = BitVec.ofNat 32 k) (hk32 : k < 2 ^ 32) :
    ∃ s', runBlock isa [.mov .esi (imm 0), .mov .ecx (slot slenO), .alu .cmp .ecx (imm 17)] s = some s' ∧
      s'.gpr .esi = BitVec.ofNat 32 0 ∧ s'.cf = some (decide (k < 17)) ∧
      (∀ r, r ≠ .esi → r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [E.ebp, L.aW, E.perm.wR, hk], ?_, ?_, fun r h₁ h₂ => ?_, ?_, ?_, ?_⟩
  · cregs []
  · cmems [hk, VG.Proof.AesGcm.X86.toNat_ofNat32 hk32]; rfl
  · cregs []
  all_goals cmems []

/-- `j` in `esi`. -/
theorem jBranch_wp {s : State} {k : Nat} (hsi : s.gpr .esi = BitVec.ofNat 32 0)
    (hcf : s.cf = some (decide (k < 17))) :
    WP isa (.ite .b (.block []) (.block [.mov .esi (imm 1)])) s fun s' =>
      s'.gpr .esi = BitVec.ofNat 32 (VG.Proof.AesSiv.jOf k) ∧ (∀ r, r ≠ .esi → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.ite (decide (k < 17)) (VG.Proof.AesSiv.X86.eval_b hcf) (fun ht => ?_) (fun hf => ?_)
  · have h₁ := of_decide_eq_true ht
    refine WP.block_nil ⟨by rw [hsi]; simp [VG.Proof.AesSiv.jOf, h₁], fun _ _ => rfl, rfl, rfl, rfl⟩
  · have h₁ := of_decide_eq_false hf
    refine WP.of_runBlock ⟨_, by crun [], ?_, fun r hr => ?_, ?_, ?_, ?_⟩
    · cregs []; simp [VG.Proof.AesSiv.jOf, h₁]
    · cregs []
    all_goals cmems []

/-- `j` at `W + jO`, and the arguments for the first `j` blocks of the tail. -/
theorem lm3_ok {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {R : Nat} {s : State} (E : VG.Proof.AesSiv.X86.Env C W SP s)
    (hc : slotv s.mem W ctxO = C) (hr : slotv s.mem W roundsO = BitVec.ofNat 32 R) {j : Nat}
    (hsi : s.gpr .esi = BitVec.ofNat 32 j) {out : Nat} :
    ∃ s', runBlock isa (([.store (at_ .ebp jO) .esi, .mov .ebx (.reg .ebp), .alu .add .ebx (imm tailOff)] :
        List Instr) ++ macArgs out) s = some s' ∧
      s'.mem = s.mem.writeW (w64 W + BitVec.ofNat 64 jO) (BitVec.ofNat 32 j) ∧
      s'.gpr .eax = C ∧ s'.gpr .ecx = BitVec.ofNat 32 R ∧ s'.gpr .edx = W + BitVec.ofNat 32 out ∧
      s'.gpr .ebx = W + BitVec.ofNat 32 32 ∧ s'.gpr .esi = BitVec.ofNat 32 j ∧
      s'.gpr .edi = W + BitVec.ofNat 32 256 ∧ s'.gpr .ebp = W ∧ s'.gpr .esp = SP ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have rd : ∀ o, o + 4 ≤ jO →
      slotv (s.mem.writeW (w64 W + BitVec.ofNat 64 jO) (BitVec.ofNat 32 j)) W o = slotv s.mem W o :=
    fun o h₁ => readW_writeW_off _ _ _ (.inl h₁) (by simp only [jO] at h₁; omega) (by decide)
  have hc' := (rd ctxO (by decide)).trans hc
  have hr' := (rd roundsO (by decide)).trans hr
  refine ⟨_, by crun [macArgs, E.ebp, L.aW, E.perm.wW, E.perm.wR, hsi, hc', hr'], ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · cmems [hsi]
  · cregs [hc']
  · cregs [hr']
  · cregs [E.ebp]
  · cregs [E.ebp]
  · cregs [hsi]
  · cregs [E.ebp]
  · cregs [E.ebp]
  · cregs [E.esp]
  all_goals cmems []

/-- The arguments for the rest of the tail. -/
theorem lm5_ok {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {R : Nat} {s : State} (E : VG.Proof.AesSiv.X86.Env C W SP s)
    (hc : slotv s.mem W ctxO = C) (hr : slotv s.mem W roundsO = BitVec.ofNat 32 R) {j k b : Nat}
    (hj : slotv s.mem W jO = BitVec.ofNat 32 j) (hk : slotv s.mem W slenO = BitVec.ofNat 32 k)
    (hb : slotv s.mem W nbO = BitVec.ofNat 32 b) (hj1 : j ≤ 1) (hbk : b + 16 * j ≤ k) (hk32 : k < 2 ^ 32)
    {out : Nat} :
    ∃ s', runBlock isa (([.mov .eax (slot jO), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax),
        .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .mov .esi (slot slenO),
        .alu .sub .esi (slot nbO), .alu .sub .esi (.reg .eax), .mov .ebx (.reg .ebp),
        .alu .add .ebx (imm tailOff), .alu .add .ebx (.reg .eax)] : List Instr) ++ macArgs out) s = some s' ∧
      s'.mem = s.mem ∧
      s'.gpr .eax = C ∧ s'.gpr .ecx = BitVec.ofNat 32 R ∧ s'.gpr .edx = W + BitVec.ofNat 32 out ∧
      s'.gpr .ebx = W + BitVec.ofNat 32 (32 + 16 * j) ∧ s'.gpr .esi = BitVec.ofNat 32 (k - b - 16 * j) ∧
      s'.gpr .edi = W + BitVec.ofNat 32 256 ∧ s'.gpr .ebp = W ∧ s'.gpr .esp = SP ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have h₁ := ofNat_sub32 (a := k) (b := b) (by omega) hk32
  have h₂ := ofNat_sub32 (a := k - b) (b := 16 * j) (by omega) (by omega)
  rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
  all_goals
    refine ⟨_, by crun [macArgs, E.ebp, L.aW, E.perm.wR, hc, hr, hj, hk, hb], ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_⟩
    · rfl
    · cregs [hc]
    · cregs [hr]
    · cregs [E.ebp]
    · cregs [E.ebp, hj]
      simp only [BitVec.reduceAdd]
      rw [VG.Proof.AesSiv.X86.add32_assoc]
    · cregs [hj, hk, hb]
      simp only [BitVec.reduceAdd]
      rw [h₁]
      exact h₂
    · cregs [E.ebp]
    · cregs [E.ebp]
    · cregs [E.esp]
    all_goals rfl

/-! ## The long case -/

/-- What `longMac` writes: the output, `j`, the working space of the functions
called and the stack below `SP`. -/
abbrev macR (W SP : BitVec 32) (out : Nat) : List Region :=
  [⟨w64 W + BitVec.ofNat 64 out, 16⟩, ⟨w64 W + BitVec.ofNat 64 jO, 4⟩, ⟨w64 W + BitVec.ofNat 64 256, 2176⟩,
    below SP 56]

theorem macR_finR {W SP : BitVec 32} {out : Nat} : ∀ r ∈ VG.Proof.AesSiv.X86.macR W SP out, ∃ r' ∈ VG.Proof.AesSiv.X86.finR W SP out, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨VG.Proof.AesSiv.X86.wS W, by simp, Offset.sub _ (by decide) (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

theorem call_macR {W SP : BitVec 32} {out : Nat} :
    ∀ r ∈ [⟨w64 W + BitVec.ofNat 64 out, 16⟩, ⟨w64 W + BitVec.ofNat 64 256, 2176⟩, below SP 56],
      ∃ r' ∈ VG.Proof.AesSiv.X86.macR W SP out, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩

theorem finR_buf {W SP : BitVec 32} {s : State} {P : BitVec 32} {k : Nat} (B : VG.Proof.AesSiv.X86.Buf W SP s P k) {out : Nat}
    (hout : out = 0 ∨ out = 112) : ∀ r ∈ VG.Proof.AesSiv.X86.finR W SP out, (⟨w64 P, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact B.w.sub_right (Lay.wSub (by omega))
  · exact B.w.sub_right (Lay.wSub (by decide))
  · exact B.w.sub_right (Lay.wSub (by decide))
  · exact B.w.sub_right (Lay.wSub (by decide))
  · exact B.w.sub_right (Lay.wSub (by decide))
  · exact B.stk.symm

/-- The tail, apart from what `longMac` writes. -/
theorem tail_macR {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {out t : Nat} (hout : out = 0 ∨ out = 112) (ht : t ≤ 32) :
    ∀ r ∈ VG.Proof.AesSiv.X86.macR W SP out, (⟨w64 W + BitVec.ofNat 64 32, t⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Lay.w_w (by omega) (by omega) (by omega)
  · exact Lay.w_w (.inl (by simp only [jO]; omega)) (by omega) (by decide)
  · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (L.stk_w' (by omega)).symm

theorem slot_macR' {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {out : Nat} (hout : out = 0 ∨ out = 112) {m m' : Mem}
    (hf : Frame [⟨w64 W + BitVec.ofNat 64 out, 16⟩, ⟨w64 W + BitVec.ofNat 64 256, 2176⟩, below SP 56] m m')
    {o : Nat} (h₁ : 176 ≤ o) (h₂ : o + 4 ≤ 256) : slotv m' W o = slotv m W o :=
  hf.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Lay.w_w (.inr (by omega)) (by omega) (by omega)
    · exact Lay.w_w (.inl h₂) (by omega) (by decide)
    · exact (L.stk_w' (by omega)).symm) (by decide)

/-- The slots `longMac` reads. -/
theorem slot_macR {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {out : Nat} (hout : out = 0 ∨ out = 112) {m m' : Mem}
    (hf : Frame (VG.Proof.AesSiv.X86.macR W SP out) m m') {o : Nat} (h₁ : 176 ≤ o) (h₂ : o + 4 ≤ jO) :
    slotv m' W o = slotv m W o :=
  hf.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Lay.w_w (.inr (by omega)) (by simp only [jO] at h₂; omega) (by omega)
    · exact Lay.w_w (.inl h₂) (by simp only [jO] at h₂; omega) (by decide)
    · exact Lay.w_w (.inl (by simp only [jO] at h₂; omega)) (by simp only [jO] at h₂; omega) (by decide)
    · exact (L.stk_w' (by simp only [jO] at h₂; omega)).symm) (by decide)

/-- The slots a call keeps. -/
theorem slot_call {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {out : Nat} (hout : out = 0 ∨ out = 112) {m m' : Mem}
    (hf : Frame [⟨w64 W + BitVec.ofNat 64 out, 16⟩, ⟨w64 W + BitVec.ofNat 64 256, 2176⟩, below SP 56] m m')
    {o : Nat} (h₁ : 176 ≤ o) (h₂ : o + 4 ≤ 256) : slotv m' W o = slotv m W o :=
  VG.Proof.AesSiv.X86.slot_macR' L hout hf h₁ h₂

/-- The long case: `k` blocks of `P`, `j` of the tail, and the rest of the
tail, into `W + out`. -/
theorem finishLong_ok (v : Ctr32Impl) {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {P : BitVec 32} {k : Nat} {s : State} (h : VG.Proof.AesSiv.X86.CmacPre C W SP R P k s)
    (h16 : 16 ≤ k) {out : Nat} (hout : out = 0 ∨ out = 112) :
    WP isa (.seq longTail (longMac v.callee v.suffix out)) s (VG.Proof.AesSiv.X86.FinPost C W SP R out P k s) := by
  have hRb : R ≤ 14 := by omega
  have hk32 := h.k32
  have B := h.buf
  have hT := kOf_tail h16
  have hJ := jOf_rest h16
  have hj1 := jOf_le k
  have hkk : 16 * kOf k ≤ k := by omega
  have hyo : VG.Proof.AesSiv.X86.StOk out := by rcases hout with rfl | rfl <;> decide
  refine WP.seq (WP.mono (VG.Proof.AesSiv.X86.longTail_ok L h h16) fun s₁ ⟨E₁, rd₁, wr₁, f₁, nb₁, t₁⟩ => ?_)
  have k₁ : ∀ o, 176 ≤ o → o + 4 ≤ 208 → slotv s₁.mem W o = slotv s.mem W o := fun o h₁ h₂ =>
    f₁.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Lay.w_w (.inr (by omega)) (by omega) (by decide)
      · exact Lay.w_w (.inl h₂) (by omega) (by decide)) (by decide)
  -- The `k` blocks of `P`.
  obtain ⟨s₂, run₂, m₂, ax₂, cx₂, dx₂, bx₂, si₂, di₂, bp₂, sp₂, rd₂, wr₂⟩ := VG.Proof.AesSiv.X86.lm1_ok (C := C) (R := R) (P := P) L E₁
    (by rw [k₁ _ (by decide) (by decide)]; exact h.ctx) (by rw [k₁ _ (by decide) (by decide)]; exact h.rounds)
    (by rw [k₁ _ (by decide) (by decide)]; exact h.str) nb₁ (by omega) hout
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have E₂ : VG.Proof.AesSiv.X86.Env C W SP s₂ := ⟨bp₂, sp₂, E₁.perm.of_eq rd₂ wr₂⟩
  have B₂ : VG.Proof.AesSiv.X86.Buf W SP s₂ P (16 * kOf k) := (B.take hkk).of_eq (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])
  refine WP.seq (WP.mono (VG.Proof.AesSiv.X86.updCall_ok v L E₂ hR (y := out) hyo (VG.Proof.AesSiv.X86.srcBuf B₂)
    (B₂.w.sub_right (Lay.wSub (by omega))) (by omega) ax₂ cx₂ dx₂ bx₂ si₂ di₂)
    fun s₃ ⟨E₃, rd₃, wr₃, _, f₃, o₃⟩ => ?_)
  have fz : Frame [⟨w64 W + BitVec.ofNat 64 out, 16⟩] s₁.mem s₂.mem := by
    rw [m₂]; exact Cmac.frame_store4 _ _ _ _ _
  have f₁₃ : Frame (VG.Proof.AesSiv.X86.macR W SP out) s₁.mem s₃.mem :=
    (fz.sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩).trans (f₃.sub VG.Proof.AesSiv.X86.call_macR)
  -- `j`.
  have k₃ : ∀ o, 176 ≤ o → o + 4 ≤ 208 → slotv s₃.mem W o = slotv s.mem W o := fun o h₁ h₂ =>
    (VG.Proof.AesSiv.X86.slot_macR L hout f₁₃ h₁ (by simp only [jO]; omega)).trans (k₁ o h₁ h₂)
  have nb₃ : slotv s₃.mem W nbO = BitVec.ofNat 32 (16 * kOf k) :=
    (VG.Proof.AesSiv.X86.slot_macR L hout f₁₃ (o := nbO) (by decide) (by decide)).trans nb₁
  obtain ⟨s₄, run₄, si₄, cf₄, g₄, m₄, rd₄, wr₄⟩ := VG.Proof.AesSiv.X86.cmp17s_ok L E₃
    (by rw [k₃ _ (by decide) (by decide)]; exact h.slen) hk32
  refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
  have E₄ : VG.Proof.AesSiv.X86.Env C W SP s₄ := ⟨by rw [g₄ _ (by decide) (by decide), E₃.ebp],
    by rw [g₄ _ (by decide) (by decide), E₃.esp], E₃.perm.of_eq rd₄ wr₄⟩
  refine WP.seq (WP.mono (VG.Proof.AesSiv.X86.jBranch_wp si₄ cf₄) fun s₅ ⟨si₅, g₅, m₅, rd₅, wr₅⟩ => ?_)
  have E₅ : VG.Proof.AesSiv.X86.Env C W SP s₅ := ⟨by rw [g₅ _ (by decide), E₄.ebp], by rw [g₅ _ (by decide), E₄.esp],
    E₄.perm.of_eq rd₅ wr₅⟩
  have k₅ : ∀ o, slotv s₅.mem W o = slotv s₃.mem W o := fun o => by rw [m₅, m₄]
  obtain ⟨s₆, run₆, m₆, ax₆, cx₆, dx₆, bx₆, si₆, di₆, bp₆, sp₆, rd₆, wr₆⟩ := VG.Proof.AesSiv.X86.lm3_ok (out := out) L E₅
    (by rw [k₅, k₃ _ (by decide) (by decide)]; exact h.ctx)
    (by rw [k₅, k₃ _ (by decide) (by decide)]; exact h.rounds) si₅
  refine WP.seq (WP.of_runBlock ⟨s₆, run₆, ?_⟩)
  have E₆ : VG.Proof.AesSiv.X86.Env C W SP s₆ := ⟨bp₆, sp₆, E₅.perm.of_eq rd₆ wr₆⟩
  have f₃₆ : Frame [⟨w64 W + BitVec.ofNat 64 jO, 4⟩] s₃.mem s₆.mem := by
    rw [m₆, m₅, m₄]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  -- The first `j` blocks of the tail.
  refine WP.seq (WP.mono (VG.Proof.AesSiv.X86.updCall_ok v L E₆ hR (y := out) hyo (n := VG.Proof.AesSiv.jOf k)
    (VG.Proof.AesSiv.X86.srcW L E₆.perm (t := 32) (k := 16 * VG.Proof.AesSiv.jOf k) (by omega))
    (by rw [L.aW (o := 32) (by decide)]; exact Lay.w_w (by omega) (by omega) (by omega)) (by omega)
    ax₆ cx₆ dx₆ bx₆ si₆ di₆) fun s₇ ⟨E₇, rd₇, wr₇, _, f₇, o₇⟩ => ?_)
  have f₃₇ : Frame (VG.Proof.AesSiv.X86.macR W SP out) s₃.mem s₇.mem :=
    (f₃₆.sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩).trans (f₇.sub VG.Proof.AesSiv.X86.call_macR)
  have k₇ : ∀ o, 176 ≤ o → o + 4 ≤ 208 → slotv s₇.mem W o = slotv s.mem W o := fun o h₁ h₂ =>
    (VG.Proof.AesSiv.X86.slot_call L hout f₇ h₁ (by omega)).trans ((VG.Proof.AesSiv.X86.slot_macR L hout (f₃₆.sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩)
      h₁ (by simp only [jO]; omega)).trans (k₃ o h₁ h₂))
  have nb₇ : slotv s₇.mem W nbO = BitVec.ofNat 32 (16 * kOf k) :=
    (VG.Proof.AesSiv.X86.slot_call L hout f₇ (o := nbO) (by decide) (by decide)).trans ((VG.Proof.AesSiv.X86.slot_macR L hout
      (f₃₆.sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩) (o := nbO) (by decide) (by decide)).trans nb₃)
  have j₇ : slotv s₇.mem W jO = BitVec.ofNat 32 (VG.Proof.AesSiv.jOf k) :=
    (VG.Proof.AesSiv.X86.slot_call L hout f₇ (o := jO) (by decide) (by decide)).trans (by rw [m₆]; exact Mem.readW_writeW_self32 _ _ _)
  -- The rest of the tail.
  obtain ⟨s₈, run₈, m₈, ax₈, cx₈, dx₈, bx₈, si₈, di₈, bp₈, sp₈, rd₈, wr₈⟩ := VG.Proof.AesSiv.X86.lm5_ok (out := out) L E₇
    (by rw [k₇ _ (by decide) (by decide)]; exact h.ctx) (by rw [k₇ _ (by decide) (by decide)]; exact h.rounds) j₇
    (by rw [k₇ _ (by decide) (by decide)]; exact h.slen) nb₇ hj1 (by omega) hk32
  refine WP.seq (WP.of_runBlock ⟨s₈, run₈, ?_⟩)
  have E₈ : VG.Proof.AesSiv.X86.Env C W SP s₈ := ⟨bp₈, sp₈, E₇.perm.of_eq rd₈ wr₈⟩
  refine WP.mono (VG.Proof.AesSiv.X86.finCall_ok v L E₈ hR (y := out) hyo (P := W + BitVec.ofNat 32 (32 + 16 * VG.Proof.AesSiv.jOf k))
    (l := k - 16 * kOf k - 16 * VG.Proof.AesSiv.jOf k) (by omega)
    (VG.Proof.AesSiv.X86.srcW L E₈.perm (t := 32 + 16 * VG.Proof.AesSiv.jOf k) (k := k - 16 * kOf k - 16 * VG.Proof.AesSiv.jOf k) (by omega))
    (by rw [L.aW (by omega)]; exact Lay.w_w (by omega) (by omega) (by omega)) ax₈ cx₈ dx₈ bx₈ si₈ di₈)
    fun s₉ ⟨E₉, rd₉, wr₉, _, f₉, o₉⟩ => ?_
  -- What it writes.
  have f₁₉ : Frame (VG.Proof.AesSiv.X86.macR W SP out) s₁.mem s₉.mem :=
    (f₁₃.trans f₃₇).trans (by rw [← m₈]; exact f₉.sub VG.Proof.AesSiv.X86.call_macR)
  have F₁ : Frame (VG.Proof.AesSiv.X86.finR W SP out) s.mem s₁.mem := f₁.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨VG.Proof.AesSiv.X86.wS W, by simp, Offset.sub _ (by decide) (by decide)⟩
  have F : ∀ {m : Mem}, Frame (VG.Proof.AesSiv.X86.macR W SP out) s₁.mem m → Frame (VG.Proof.AesSiv.X86.finR W SP out) s.mem m :=
    fun hm => F₁.trans (hm.sub VG.Proof.AesSiv.X86.macR_finR)
  refine ⟨E₉, by rw [rd₉, rd₈, rd₇, rd₆, rd₅, rd₄, rd₃, rd₂, rd₁],
    by rw [wr₉, wr₈, wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁], F f₁₉, ?_⟩
  -- S2V's end.
  have hC {d n : Nat} (hd : d + n ≤ 512) {m : Mem} (hm : Frame (VG.Proof.AesSiv.X86.macR W SP out) s₁.mem m) :
      bytesAt m (w64 C + BitVec.ofNat 64 d) n = bytesAt s.mem (w64 C + BitVec.ofNat 64 d) n :=
    Proof.AesGcm.X86.bytesAt_frame (F hm) (fun r hr => (VG.Proof.AesSiv.X86.finR_c L hout r hr).sub_left (Offset.sub_base _ hd))
      (by omega)
  have hTl {n : Nat} (hn : n ≤ 32) {m : Mem} (hm : Frame (VG.Proof.AesSiv.X86.macR W SP out) s₁.mem m) :
      bytesAt m (w64 W + BitVec.ofNat 64 32) n = bytesAt s₁.mem (w64 W + BitVec.ofNat 64 32) n :=
    Proof.AesGcm.X86.bytesAt_frame hm (VG.Proof.AesSiv.X86.tail_macR L hout hn) (by omega)
  have f₁₂ : Frame (VG.Proof.AesSiv.X86.macR W SP out) s₁.mem s₂.mem := fz.sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩
  have f₁₆ : Frame (VG.Proof.AesSiv.X86.macR W SP out) s₁.mem s₆.mem :=
    f₁₃.trans (f₃₆.sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩)
  have f₁₈ : Frame (VG.Proof.AesSiv.X86.macR W SP out) s₁.mem s₈.mem := by rw [m₈]; exact f₁₃.trans f₃₇
  have sch₈ := hC (d := 0) (n := 16 * (R + 1)) (by omega) f₁₈
  have sch₆ := hC (d := 0) (n := 16 * (R + 1)) (by omega) f₁₆
  have sch₂ := hC (d := 0) (n := 16 * (R + 1)) (by omega) f₁₂
  have k1 := hC (d := 240) (n := 16) (by decide) f₁₈
  have k2 := hC (d := 256) (n := 16) (by decide) f₁₈
  rw [BitVec.add_zero] at sch₈ sch₆ sch₂
  -- The state after each call.
  have hz : bytesAt s₂.mem (w64 W + BitVec.ofNat 64 out) 16 = Spec.Cmac.zeros 16 := by
    rw [m₂]; exact Cmac.zero4_bytes _ _
  have s₆o : bytesAt s₆.mem (w64 W + BitVec.ofNat 64 out) 16 = bytesAt s₃.mem (w64 W + BitVec.ofNat 64 out) 16 :=
    Proof.AesGcm.X86.bytesAt_frame f₃₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Lay.w_w (.inl (by simp only [jO]; omega)) (by omega) (by decide)) (by decide)
  have pP : bytesAt s₂.mem (w64 P) (16 * kOf k) = (bytesAt s.mem (w64 P) k).take (16 * kOf k) := by
    rw [Proof.AesGcm.X86.bytesAt_frame (F f₁₂) (fun r hr => (VG.Proof.AesSiv.X86.finR_buf B hout r hr).sub_left
      (Region.sub_prefix hkk)) (by have := B.lt; omega)]
    have := take_bytesAt s.mem (w64 P) (a := 16 * kOf k) (b := k - 16 * kOf k)
    rw [Nat.add_sub_cancel' hkk] at this
    exact this.symm
  -- The tail.
  have tl : (Spec.Siv.xorend ((bytesAt s.mem (w64 P) k).drop (16 * kOf k))
      (bytesAt s.mem (w64 W + BitVec.ofNat 64 dOff) 16)).length = k - 16 * kOf k := by
    rw [← t₁, length_bytesAt]
  have pT : bytesAt s₆.mem (w64 W + BitVec.ofNat 64 32) (16 * VG.Proof.AesSiv.jOf k) =
      (Spec.Siv.xorend ((bytesAt s.mem (w64 P) k).drop (16 * kOf k))
        (bytesAt s.mem (w64 W + BitVec.ofNat 64 dOff) 16)).take (16 * VG.Proof.AesSiv.jOf k) := by
    rw [hTl (by omega) f₁₆, ← t₁]
    have := take_bytesAt s₁.mem (w64 W + BitVec.ofNat 64 32) (a := 16 * VG.Proof.AesSiv.jOf k) (b := k - 16 * kOf k - 16 * VG.Proof.AesSiv.jOf k)
    rw [Nat.add_sub_cancel' hJ.1] at this
    exact this.symm
  have dT : bytesAt s₈.mem (w64 (W + BitVec.ofNat 32 (32 + 16 * VG.Proof.AesSiv.jOf k))) (k - 16 * kOf k - 16 * VG.Proof.AesSiv.jOf k) =
      (Spec.Siv.xorend ((bytesAt s.mem (w64 P) k).drop (16 * kOf k))
        (bytesAt s.mem (w64 W + BitVec.ofNat 64 dOff) 16)).drop (16 * VG.Proof.AesSiv.jOf k) := by
    rw [← t₁, L.aW (by omega), ← hTl (by omega) f₁₈]
    have := drop_bytesAt s₈.mem (w64 W + BitVec.ofNat 64 32) (a := 16 * VG.Proof.AesSiv.jOf k) (b := k - 16 * kOf k - 16 * VG.Proof.AesSiv.jOf k)
    rw [Nat.add_sub_cancel' hJ.1, BitVec.add_assoc, BitVec.ofNat_add_ofNat] at this
    exact this.symm
  have spec := long_spec (Spec.Siv.schedCiph s.mem (w64 C) R) (bytesAt s.mem (w64 C + 240) 16)
    (bytesAt s.mem (w64 C + 256) 16) (bytesAt s.mem (w64 W + BitVec.ofNat 64 dOff) 16) (bytesAt s.mem (w64 P) k)
    (length_bytesAt _ _ _) (by rw [length_bytesAt]; exact h16)
  rw [length_bytesAt] at spec
  rw [o₉, m₈, o₇, s₆o, o₃, hz, Proof.Cmac.Stream.blocksAt_eq, Proof.Cmac.Stream.blocksAt_eq, pP,
    L.aW (o := 32) (by decide), pT, ← m₈, dT, sch₈, sch₆, sch₂, k1, k2, Spec.Siv.ctxMac, ← spec]
  rfl

end VG.Proof.AesSiv.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.X86.Finish`. -/
section

/-!
# AES-SIV on x86: finishing S2V

Untrusted: everything here is checked by Lean. `finish out` takes the short
case (`finishShort_ok`) for a last string of fewer than 16 bytes and the long
case (`finishLong_ok`) otherwise (`finish_ok`).
-/

namespace VG.Proof.AesSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesSiv.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4 copyLoop)
open VG.Proof.AesGcm.X86 (w64 toNat_ofNat32 slotv CT)

theorem cmp16_ok {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {s : State} (E : VG.Proof.AesSiv.X86.Env C W SP s) {k : Nat}
    (hk : slotv s.mem W slenO = BitVec.ofNat 32 k) (hk32 : k < 2 ^ 32) :
    ∃ s', runBlock isa [.mov .ecx (slot slenO), .alu .cmp .ecx (imm 16)] s = some s' ∧
      s'.cf = some (decide (k < 16)) ∧ (∀ r, r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  refine ⟨_, by crun [E.ebp, L.aW, E.perm.wR, hk], ?_, fun r h₁ => ?_, ?_, ?_, ?_⟩
  · cmems [hk, VG.Proof.AesGcm.X86.toNat_ofNat32 hk32]; rfl
  · cregs []
  all_goals cmems []

theorem CmacPre.of_eq {C W SP : BitVec 32} {R : Nat} {P : BitVec 32} {k : Nat} {s s' : State}
    (h : VG.Proof.AesSiv.X86.CmacPre C W SP R P k s) (hbp : s'.gpr .ebp = s.gpr .ebp) (hsp : s'.gpr .esp = s.gpr .esp)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesSiv.X86.CmacPre C W SP R P k s' :=
  ⟨⟨by rw [hbp]; exact h.env.ebp, by rw [hsp]; exact h.env.esp, h.env.perm.of_eq hrd hwr⟩,
    by rw [hm]; exact h.ctx, by rw [hm]; exact h.rounds, by rw [hm]; exact h.str, by rw [hm]; exact h.slen, h.k32,
    h.buf.of_eq hrd hwr⟩

theorem FinPost.of_eq {C W SP : BitVec 32} {R out : Nat} {P : BitVec 32} {k : Nat} {s s₁ s' : State}
    (h : VG.Proof.AesSiv.X86.FinPost C W SP R out P k s₁ s') (hm : s₁.mem = s.mem) (hrd : s₁.rd = s.rd) (hwr : s₁.wr = s.wr) :
    VG.Proof.AesSiv.X86.FinPost C W SP R out P k s s' :=
  ⟨h.env, h.rd.trans hrd, h.wr.trans hwr, by rw [← hm]; exact h.frame, by rw [← hm]; exact h.out⟩

/-- `finish out`: S2V's end, from `D` and the string at `W + strO`, at
`W + out`. -/
theorem finish_ok (v : Ctr32Impl) {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {P : BitVec 32} {k : Nat} {s : State} (h : VG.Proof.AesSiv.X86.CmacPre C W SP R P k s)
    {out : Nat} (hout : out = 0 ∨ out = 112) :
    WP isa (finish v.callee v.suffix out) s (VG.Proof.AesSiv.X86.FinPost C W SP R out P k s) := by
  obtain ⟨s₁, run₁, cf₁, g₁, m₁, rd₁, wr₁⟩ := VG.Proof.AesSiv.X86.cmp16_ok L h.env h.slen h.k32
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have h₁ := h.of_eq (g₁ _ (by decide)) (g₁ _ (by decide)) m₁ rd₁ wr₁
  refine WP.ite (decide (k < 16)) (VG.Proof.AesSiv.X86.eval_b cf₁) (fun ht => ?_) (fun hf => ?_)
  · exact WP.mono (VG.Proof.AesSiv.X86.finishShort_ok v L hR h₁ (of_decide_eq_true ht) hout) fun _ p => p.of_eq m₁ rd₁ wr₁
  · exact WP.mono (VG.Proof.AesSiv.X86.finishLong_ok v L hR h₁ (by have := of_decide_eq_false hf; omega) hout)
      fun _ p => p.of_eq m₁ rd₁ wr₁

end VG.Proof.AesSiv.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.X86.FinishCT`. -/
section

/-!
# AES-SIV on x86: finishing S2V is constant time

Untrusted: everything here is checked by Lean. The taint analysis checks each
block from `ebp`; the registers that hold addresses computed from the
string's length (public) are pinned to their values where a block uses
them, and the calls are constant time by their contracts.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesSiv.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4 copyLoop)
open VG.Proof.AesGcm.X86 (w64 toNat_ofNat32 slotv CT copyLoop_ct copyLoop_ok length_bytesAt)

/-- `copyN` of a public length, from public pointers. -/
theorem copyN_ct {I : State → Prop} {k : Nat} (hk : k < 2 ^ 32)
    (hr : ∀ s₁ s₂, I s₁ → I s₂ → ∀ r ∈ [Reg.edi, .edx, .ecx], s₁.gpr r = s₂.gpr r)
    (hc : ∀ s, I s → s.gpr .ecx = BitVec.ofNat 32 k) : CT I copyN := by
  refine CT.seq (J := fun s' => (∃ s, I s ∧ ∀ r, s'.gpr r = s.gpr r) ∧ s'.zf = some (decide (k = 0)))
    (CT.taint [.ecx] (VG.Proof.AesSiv.X86.pin1 fun s h => hc s h) (by taint_decide))
    (fun s hs => WP.of_runBlock ⟨_, by crun [hc s hs], ⟨s, hs, fun r => by cregs []⟩,
      by cmems [hc s hs]; rw [Proof.AesGcm.X86.and_self_beq32 hk]⟩) ?_
  refine CT.ite (decide (k = 0)) (fun s h => VG.Proof.AesSiv.X86.eval_e h.2) (fun _ => CT.nil) (fun _ => copyLoop_ct ?_)
  intro s₁ s₂ ⟨⟨t₁, i₁, e₁⟩, _⟩ ⟨⟨t₂, i₂, e₂⟩, _⟩ r hr'
  rw [e₁, e₂]; exact hr t₁ t₂ i₁ i₂ r hr'

/-! ## The short case -/

theorem shortTail_ct {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {R : Nat} {P : BitVec 32} {k : Nat}
    (hk16 : k < 16) {I : State → Prop} (hI : ∀ s, I s → VG.Proof.AesSiv.X86.CmacPre C W SP R P k s) : CT I shortTail := by
  refine CT.block_seq [.ebp] (VG.Proof.AesSiv.X86.pin_ebp fun s h => (hI s h).env.ebp) (by taint_decide)
    (fun s hs => VG.Proof.AesSiv.X86.shortA_ok L (hI s hs).env (hI s hs).str (hI s hs).slen) ?_
  refine CT.seq (J := fun s₂ => s₂.gpr .ebp = W ∧ VG.Proof.AesSiv.X86.Env C W SP s₂ ∧ slotv s₂.mem W slenO = BitVec.ofNat 32 k)
    (VG.Proof.AesSiv.X86.copyN_ct (k := k) (by omega) (VG.Proof.AesSiv.X86.pin3 fun s ⟨_, _, _, di, dx, cx, _⟩ => ⟨di, dx, cx⟩)
      fun s ⟨_, _, _, _, _, cx, _⟩ => cx) (fun s₁ ⟨s, hs, m₁, di₁, dx₁, cx₁, bp₁, sp₁, rd₁, wr₁⟩ => ?_) ?_
  · have h := hI s hs
    have B := h.buf
    have E₁ : VG.Proof.AesSiv.X86.Env C W SP s₁ := ⟨bp₁, sp₁, h.env.perm.of_eq rd₁ wr₁⟩
    have hw := L.fw
    refine WP.mono (VG.Proof.AesSiv.X86.copyN_ok di₁ dx₁ cx₁ h.k32 B.wrap (by rw [L.nW (by decide)]; omega)
      (by rw [rd₁, wr₁]; exact B.rd) (by rw [L.aW (by decide)]; exact E₁.perm.wC (by omega))
      (by rw [L.aW (by decide)]; exact B.w.sub_right (Lay.wSub (by omega)))) fun s₂ ⟨m₂, g₂, rd₂, wr₂⟩ => ?_
    have bp₂ : s₂.gpr .ebp = W := by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), bp₁]
    refine ⟨bp₂, ⟨bp₂, by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), sp₁], E₁.perm.of_eq rd₂ wr₂⟩, ?_⟩
    have f₁ : Frame [⟨w64 W + BitVec.ofNat 64 32, 32⟩] s.mem s₁.mem := by
      rw [m₁]
      exact ((Cmac.frame_store4 _ _ _ _ _).sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by decide) (by decide)⟩).trans
        ((Cmac.frame_store4 _ _ _ _ _).sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by decide) (by decide)⟩)
    have f₂ : Frame [⟨w64 W + BitVec.ofNat 64 32, 32⟩] s₁.mem s₂.mem := by
      rw [m₂, L.aW (by decide)]
      exact VG.WriteBytes.writeBytes_frame _ _ _ (by
        rw [length_bytesAt]; exact Offset.contains (w64 W) (d := 32) (n := k) (e := 32) (k := 32) (by omega)
          (by omega) (by omega))
    exact ((f₁.trans f₂).readW (w := 32) (r := ⟨w64 W + BitVec.ofNat 64 slenO, 4⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by decide)) (by decide) (by decide))
      (by decide)).trans h.slen
  · have e : ([.mov .edx (.reg .ebp), .alu .add .edx (slot slenO), .mov .eax (imm 0x80),
          .store8 (at_ .edx tailOff) .al,
          .mov .eax (slot dOff), .store (at_ .ebp dbOff) .eax, .mov .eax (slot (dOff + 4)),
          .store (at_ .ebp (dbOff + 4)) .eax, .mov .eax (slot (dOff + 8)), .store (at_ .ebp (dbOff + 8)) .eax,
          .mov .eax (slot (dOff + 12)), .store (at_ .ebp (dbOff + 12)) .eax] ++ dblAt dbOff ++
          [.mov .edx (.reg .ebp)] ++ xorInto dbOff tailOff : List Instr) =
        ([.mov .edx (.reg .ebp), .alu .add .edx (slot slenO)] : List Instr) ++
          ([.mov .eax (imm 0x80), .store8 (at_ .edx tailOff) .al,
          .mov .eax (slot dOff), .store (at_ .ebp dbOff) .eax, .mov .eax (slot (dOff + 4)),
          .store (at_ .ebp (dbOff + 4)) .eax, .mov .eax (slot (dOff + 8)), .store (at_ .ebp (dbOff + 8)) .eax,
          .mov .eax (slot (dOff + 12)), .store (at_ .ebp (dbOff + 12)) .eax] ++ dblAt dbOff ++
          [.mov .edx (.reg .ebp)] ++ xorInto dbOff tailOff) := by
      simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [e]
    refine RelCT.block_append (CT.seq (J := fun s => s.gpr .ebp = W ∧ s.gpr .edx = W + BitVec.ofNat 32 k)
      (CT.taint [.ebp] (VG.Proof.AesSiv.X86.pin_ebp fun s h => h.1) (by taint_decide))
      (fun s ⟨bp, E, sl⟩ => WP.of_runBlock ⟨_, by crun [bp, L.aW, E.perm.wR, sl], by cregs [bp], by cregs [bp, sl]⟩)
      (CT.taint [.ebp, .edx] (VG.Proof.AesSiv.X86.pin2 fun s h => h) (by taint_decide)))

theorem shortMac_ct (v : Ctr32Impl) {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {out : Nat} (hout : out = 0 ∨ out = 112) {I : State → Prop}
    (hI : ∀ s, I s → VG.Proof.AesSiv.X86.Env C W SP s ∧ slotv s.mem W ctxO = C ∧ slotv s.mem W roundsO = BitVec.ofNat 32 R) :
    CT I (shortMac v.callee v.suffix out) := by
  have hyo : VG.Proof.AesSiv.X86.StOk out := by rcases hout with rfl | rfl <;> decide
  have dO : (⟨w64 W + BitVec.ofNat 64 32, 16⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 out, 16⟩ := by
    rcases hout with rfl | rfl <;> exact Lay.w_w (by decide) (by decide) (by decide)
  have fin : CT (fun s' => ∃ s, I s ∧ s'.mem = Cmac.zero4 s.mem (w64 W + BitVec.ofNat 64 out) ∧
      s'.gpr .eax = C ∧ s'.gpr .ecx = BitVec.ofNat 32 R ∧ s'.gpr .edx = W + BitVec.ofNat 32 out ∧
      s'.gpr .ebx = W + BitVec.ofNat 32 32 ∧ s'.gpr .esi = BitVec.ofNat 32 16 ∧
      s'.gpr .edi = W + BitVec.ofNat 32 256 ∧ s'.gpr .ebp = W ∧ s'.gpr .esp = SP ∧ s'.rd = s.rd ∧
      s'.wr = s.wr) (finCall v.callee v.suffix) :=
    VG.Proof.AesSiv.X86.finCall_ct v L hR (y := out) hyo (P := W + BitVec.ofNat 32 32) (l := 16) (Nat.le_refl _)
      fun s₂ ⟨s, hs, _, ax, cx, dx, bx, si, di, bp, sp, rd, wr⟩ =>
        have P₂ := (hI s hs).1.perm.of_eq rd wr
        ⟨⟨bp, sp, P₂⟩, VG.Proof.AesSiv.X86.srcW L P₂ (t := 32) (k := 16) (by decide), by rw [L.aW (o := 32) (by decide)]; exact dO,
          ax, cx, dx, bx, si, di⟩
  rcases hout with rfl | rfl
  all_goals
    refine CT.block_seq [.ebp] (VG.Proof.AesSiv.X86.pin_ebp fun s h => (hI s h).1.ebp) (by taint_decide)
      (fun s hs => VG.Proof.AesSiv.X86.macPre_ok L (hI s hs).1 (hI s hs).2.1 (hI s hs).2.2 (by decide)) ?_
    exact fin

/-! ## The long case -/

theorem kRound_ct {I : State → Prop} :
    CT I (.block [.mov .eax (.reg .ecx), .alu .sub .eax (imm 1), .alu .and .eax (imm 0xfffffff0),
      .alu .sub .eax (imm 16)]) :=
  CT.taint [] (fun _ _ _ _ r hr => by simp at hr) (by taint_decide)

theorem longTail_ct {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {R : Nat} {P : BitVec 32} {k : Nat}
    (h16 : 16 ≤ k) (hk32 : k < 2 ^ 32) {I : State → Prop} (hI : ∀ s, I s → VG.Proof.AesSiv.X86.CmacPre C W SP R P k s) :
    CT I longTail := by
  have hT := kOf_tail h16
  have hkk : 16 * kOf k ≤ k := by omega
  refine CT.block_seq [.ebp] (VG.Proof.AesSiv.X86.pin_ebp fun s h => (hI s h).env.ebp) (by taint_decide)
    (fun s hs => VG.Proof.AesSiv.X86.cmp17_ok L (hI s hs).env (hI s hs).slen hk32) ?_
  refine CT.seq (J := fun s₂ => ∃ s, I s ∧ s₂.gpr .eax = BitVec.ofNat 32 (16 * kOf k) ∧
      s₂.gpr .ecx = BitVec.ofNat 32 k ∧ s₂.gpr .ebp = W ∧ s₂.gpr .esp = SP ∧ s₂.mem = s.mem ∧ s₂.rd = s.rd ∧
      s₂.wr = s.wr)
    (CT.ite (decide (k < 17)) (fun s ⟨_, _, _, _, cf, _⟩ => VG.Proof.AesSiv.X86.eval_b cf) (fun _ => CT.nil)
      (fun _ => VG.Proof.AesSiv.X86.kRound_ct))
    (fun s₁ ⟨s, hs, ax, cx, cf, bp, sp, m, rd, wr⟩ => WP.mono (VG.Proof.AesSiv.X86.kBranch_wp ax cx cf h16 hk32)
      fun s₂ ⟨ax₂, cx₂, g₂, m₂, rd₂, wr₂⟩ => ⟨s, hs, ax₂, cx₂, by rw [g₂ _ (by decide), bp],
        by rw [g₂ _ (by decide), sp], m₂.trans m, rd₂.trans rd, wr₂.trans wr⟩) ?_
  refine CT.block_seq [.ebp] (VG.Proof.AesSiv.X86.pin_ebp fun s ⟨_, _, _, _, bp, _⟩ => bp) (by taint_decide)
    (fun s₂ ⟨s, hs, ax, cx, bp, sp, m, rd, wr⟩ => VG.Proof.AesSiv.X86.tailArgs_ok L ⟨bp, sp, (hI s hs).env.perm.of_eq rd wr⟩
      (P := P) ax cx (by rw [m]; exact (hI s hs).str)) ?_
  refine CT.seq (J := fun s₄ => s₄.gpr .ebp = W ∧ VG.Proof.AesSiv.X86.Env C W SP s₄ ∧
      slotv s₄.mem W slenO = BitVec.ofNat 32 k ∧ slotv s₄.mem W nbO = BitVec.ofNat 32 (16 * kOf k))
    (copyLoop_ct (VG.Proof.AesSiv.X86.pin3 fun s ⟨_, _, _, di, cx, dx, _⟩ => ⟨di, dx, cx⟩))
    (fun s₃ ⟨s₂, ⟨s, hs, ax₂, cx₂, bp₂, sp₂, m₂, rd₂, wr₂⟩, m₃, di₃, cx₃, dx₃, bp₃, sp₃, rd₃, wr₃⟩ => ?_) ?_
  · have h := hI s hs
    have B := h.buf
    have E₃ : VG.Proof.AesSiv.X86.Env C W SP s₃ := ⟨bp₃, sp₃, h.env.perm.of_eq (by rw [rd₃, rd₂]) (by rw [wr₃, wr₂])⟩
    have hwk : P.toNat + 16 * kOf k < 2 ^ 32 := by have := B.wrap; omega
    have B₃ : VG.Proof.AesSiv.X86.Buf W SP s₃ (P + BitVec.ofNat 32 (16 * kOf k)) (k - 16 * kOf k) :=
      (B.drop hkk hwk).of_eq (by rw [rd₃, rd₂]) (by rw [wr₃, wr₂])
    have hW := L.fw
    refine WP.mono (copyLoop_ok s₃ ⟨di₃, dx₃, by rw [cx₃, Proof.AesGcm.X86.ofNat_sub32 hkk hk32],
      by omega, by omega, B₃.wrap, by rw [L.nW (o := 32) (by decide)]; omega, B₃.rd,
      by rw [L.aW (by decide)]; exact E₃.perm.wC (by omega),
      by rw [L.aW (by decide)]; exact B₃.w.sub_right (Lay.wSub (by omega))⟩) fun s₄ c₄ => ?_
    have bp₄ : s₄.gpr .ebp = W := by rw [c₄.other _ (by decide) (by decide) (by decide) (by decide), bp₃]
    have f₃₄ : Frame [⟨w64 W + BitVec.ofNat 64 32, 32⟩] s₃.mem s₄.mem := by
      rw [c₄.mem, L.aW (by decide)]
      exact VG.WriteBytes.writeBytes_frame _ _ _ (by
        rw [length_bytesAt]; exact Offset.contains (w64 W) (d := 32) (n := k - 16 * kOf k) (e := 32) (k := 32)
          (by omega) (by omega) (by omega))
    have k₄ : ∀ o, 64 ≤ o → o + 4 ≤ 2576 → slotv s₄.mem W o = slotv s₃.mem W o := fun o h₁ h₂ =>
      f₃₄.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by omega)) (by omega) (by decide))
        (by decide)
    refine ⟨bp₄, ⟨bp₄, by rw [c₄.other _ (by decide) (by decide) (by decide) (by decide), sp₃],
      E₃.perm.of_eq c₄.rd c₄.wr⟩, ?_, ?_⟩
    · rw [k₄ _ (by decide) (by decide), m₃, slotv, Proof.AesGcm.X86.readW_writeW_off _ _ _ (by decide) (by decide)
        (by decide), m₂]
      exact h.slen
    · rw [k₄ _ (by decide) (by decide), m₃]; exact Mem.readW_writeW_self32 _ _ _
  · have e : ([.mov .edx (.reg .ebp), .alu .add .edx (slot slenO), .alu .sub .edx (slot nbO)] ++
          xorInto dOff (tailOff - 16) : List Instr) =
        ([.mov .edx (.reg .ebp), .alu .add .edx (slot slenO), .alu .sub .edx (slot nbO)] : List Instr) ++
          xorInto dOff (tailOff - 16) := rfl
    rw [e]
    refine RelCT.block_append (CT.seq (J := fun s => s.gpr .ebp = W ∧
        s.gpr .edx = W + BitVec.ofNat 32 k - BitVec.ofNat 32 (16 * kOf k))
      (CT.taint [.ebp] (VG.Proof.AesSiv.X86.pin_ebp fun s h => h.1) (by taint_decide))
      (fun s ⟨bp, E, sl, nb⟩ => WP.of_runBlock ⟨_, by crun [bp, L.aW, E.perm.wR, sl, nb], by cregs [bp],
        by cregs [bp, sl, nb]⟩)
      (CT.taint [.ebp, .edx] (VG.Proof.AesSiv.X86.pin2 fun s h => h) (by taint_decide)))

theorem jSet_ct {I : State → Prop} : CT I (.block [.mov .esi (imm 1)]) :=
  CT.taint [] (fun _ _ _ _ r hr => by simp at hr) (by taint_decide)

/-- What `longMac` keeps between its calls. -/
structure LMS (C W SP : BitVec 32) (R : Nat) (k : Nat) (s : State) : Prop where
  env : VG.Proof.AesSiv.X86.Env C W SP s
  ctx : slotv s.mem W ctxO = C
  rounds : slotv s.mem W roundsO = BitVec.ofNat 32 R
  slen : slotv s.mem W slenO = BitVec.ofNat 32 k
  nb : slotv s.mem W nbO = BitVec.ofNat 32 (16 * kOf k)

theorem LMS.of_slots {C W SP : BitVec 32} {R k : Nat} {s s' : State} (h : VG.Proof.AesSiv.X86.LMS C W SP R k s) (E : VG.Proof.AesSiv.X86.Env C W SP s')
    (hs : ∀ o, 176 ≤ o → o + 4 ≤ jO → slotv s'.mem W o = slotv s.mem W o) : VG.Proof.AesSiv.X86.LMS C W SP R k s' :=
  ⟨E, by rw [hs _ (by decide) (by decide)]; exact h.ctx, by rw [hs _ (by decide) (by decide)]; exact h.rounds,
    by rw [hs _ (by decide) (by decide)]; exact h.slen, by rw [hs _ (by decide) (by decide)]; exact h.nb⟩

theorem slot_zero4 {W : BitVec 32} {out : Nat} (hout : out = 0 ∨ out = 112) (m : Mem)
    {o : Nat} (h₁ : 176 ≤ o) (h₂ : o + 4 ≤ 256) :
    slotv (Cmac.zero4 m (w64 W + BitVec.ofNat 64 out)) W o = slotv m W o :=
  (Cmac.frame_store4 _ _ _ _ _).readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by omega)) (by omega) (by omega))
    (by decide)

theorem longMac_ct (v : Ctr32Impl) {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {P : BitVec 32} {k : Nat} (h16 : 16 ≤ k) (hk32 : k < 2 ^ 32) {out : Nat}
    (hout : out = 0 ∨ out = 112) {I : State → Prop}
    (hI : ∀ s, I s → VG.Proof.AesSiv.X86.CmacPre C W SP R P k s ∧ slotv s.mem W nbO = BitVec.ofNat 32 (16 * kOf k)) :
    CT I (longMac v.callee v.suffix out) := by
  have hT := kOf_tail h16
  have hJ := jOf_rest h16
  have hj1 := jOf_le k
  have hkk : 16 * kOf k ≤ k := by omega
  have hyo : VG.Proof.AesSiv.X86.StOk out := by rcases hout with rfl | rfl <;> decide
  have hout' := hout
  rcases hout with rfl | rfl
  all_goals
    refine CT.block_seq [.ebp] (VG.Proof.AesSiv.X86.pin_ebp fun s h => (hI s h).1.env.ebp) (by taint_decide)
      (fun s hs => VG.Proof.AesSiv.X86.lm1_ok (C := C) (R := R) (P := P) L (hI s hs).1.env (hI s hs).1.ctx (hI s hs).1.rounds
        (hI s hs).1.str (hI s hs).2 (by omega) hout') ?_
    refine CT.seq (J := VG.Proof.AesSiv.X86.LMS C W SP R k)
      (VG.Proof.AesSiv.X86.updCall_ct v L hR hyo (Q := P) (n := kOf k) (by omega)
        fun s₂ ⟨s, hs, _, ax, cx, dx, bx, si, di, bp, sp, rd, wr⟩ =>
          have B₂ : VG.Proof.AesSiv.X86.Buf W SP s₂ P (16 * kOf k) := ((hI s hs).1.buf.take hkk).of_eq rd wr
          ⟨⟨bp, sp, (hI s hs).1.env.perm.of_eq rd wr⟩, VG.Proof.AesSiv.X86.srcBuf B₂, B₂.w.sub_right (Lay.wSub (by decide)),
            ax, cx, dx, bx, si, di⟩)
      (fun s₂ ⟨s, hs, m₂, ax, cx, dx, bx, si, di, bp, sp, rd, wr⟩ =>
        have B₂ : VG.Proof.AesSiv.X86.Buf W SP s₂ P (16 * kOf k) := ((hI s hs).1.buf.take hkk).of_eq rd wr
        WP.mono (VG.Proof.AesSiv.X86.updCall_ok v L ⟨bp, sp, (hI s hs).1.env.perm.of_eq rd wr⟩ hR hyo (VG.Proof.AesSiv.X86.srcBuf B₂)
          (B₂.w.sub_right (Lay.wSub (by decide))) (by omega) ax cx dx bx si di)
          fun s₃ ⟨E₃, _, _, _, f₃, _⟩ =>
            have hs' : ∀ o, 176 ≤ o → o + 4 ≤ 256 → slotv s₃.mem W o = slotv s.mem W o := fun o h₁ h₂ => by
              rw [VG.Proof.AesSiv.X86.slot_call L hout' f₃ h₁ h₂, m₂, VG.Proof.AesSiv.X86.slot_zero4 (W := W) hout' _ h₁ h₂]
            ⟨E₃, by rw [hs' _ (by decide) (by decide)]; exact (hI s hs).1.ctx,
              by rw [hs' _ (by decide) (by decide)]; exact (hI s hs).1.rounds,
              by rw [hs' _ (by decide) (by decide)]; exact (hI s hs).1.slen,
              by rw [hs' _ (by decide) (by decide)]; exact (hI s hs).2⟩) ?_
    refine CT.block_seq [.ebp] (VG.Proof.AesSiv.X86.pin_ebp fun s h => h.env.ebp) (by taint_decide)
      (fun s hs => VG.Proof.AesSiv.X86.cmp17s_ok L hs.env hs.slen hk32) ?_
    refine CT.seq (J := fun s₅ => VG.Proof.AesSiv.X86.LMS C W SP R k s₅ ∧ s₅.gpr .esi = BitVec.ofNat 32 (VG.Proof.AesSiv.jOf k))
      (CT.ite (decide (k < 17)) (fun s ⟨_, _, _, cf, _⟩ => VG.Proof.AesSiv.X86.eval_b cf) (fun _ => CT.nil) (fun _ => VG.Proof.AesSiv.X86.jSet_ct))
      (fun s₄ ⟨s, hs, si, cf, g, m, rd, wr⟩ => WP.mono (VG.Proof.AesSiv.X86.jBranch_wp si cf)
        fun s₅ ⟨si₅, g₅, m₅, rd₅, wr₅⟩ =>
          ⟨hs.of_slots ⟨by rw [g₅ _ (by decide), g _ (by decide) (by decide), hs.env.ebp],
            by rw [g₅ _ (by decide), g _ (by decide) (by decide), hs.env.esp],
            hs.env.perm.of_eq (rd₅.trans rd) (wr₅.trans wr)⟩ fun o _ _ => by rw [m₅, m], si₅⟩) ?_
    refine CT.block_seq [.ebp] (VG.Proof.AesSiv.X86.pin_ebp fun s h => h.1.env.ebp) (by taint_decide)
      (fun s hs => VG.Proof.AesSiv.X86.lm3_ok L hs.1.env hs.1.ctx hs.1.rounds hs.2) ?_
    refine CT.seq (J := fun s₇ => VG.Proof.AesSiv.X86.LMS C W SP R k s₇ ∧ slotv s₇.mem W jO = BitVec.ofNat 32 (VG.Proof.AesSiv.jOf k))
      (VG.Proof.AesSiv.X86.updCall_ct v L hR hyo (Q := W + BitVec.ofNat 32 32) (n := VG.Proof.AesSiv.jOf k) (by omega)
        fun s₆ ⟨s, hs, _, ax, cx, dx, bx, si, di, bp, sp, rd, wr⟩ =>
          have P₆ := hs.1.env.perm.of_eq rd wr
          ⟨⟨bp, sp, P₆⟩, VG.Proof.AesSiv.X86.srcW L P₆ (t := 32) (k := 16 * VG.Proof.AesSiv.jOf k) (by omega),
            by rw [L.aW (o := 32) (by decide)]; exact Lay.w_w (by omega) (by omega) (by omega),
            ax, cx, dx, bx, si, di⟩)
      (fun s₆ ⟨s, hs, m₆, ax, cx, dx, bx, si, di, bp, sp, rd, wr⟩ =>
        have P₆ := hs.1.env.perm.of_eq rd wr
        WP.mono (VG.Proof.AesSiv.X86.updCall_ok v L ⟨bp, sp, P₆⟩ hR hyo (n := VG.Proof.AesSiv.jOf k) (VG.Proof.AesSiv.X86.srcW L P₆ (t := 32) (k := 16 * VG.Proof.AesSiv.jOf k) (by omega))
          (by rw [L.aW (o := 32) (by decide)]; exact Lay.w_w (by omega) (by omega) (by omega)) (by omega)
          ax cx dx bx si di)
          fun s₇ ⟨E₇, _, _, _, f₇, _⟩ =>
            ⟨hs.1.of_slots E₇ fun o h₁ h₂ => by
              rw [VG.Proof.AesSiv.X86.slot_call L hout' f₇ h₁ (by simp only [jO] at h₂; omega), m₆, slotv,
                Proof.AesGcm.X86.readW_writeW_off _ _ _ (.inl h₂) (by simp only [jO] at h₂; omega) (by decide)],
              by rw [VG.Proof.AesSiv.X86.slot_call L hout' f₇ (by decide) (by decide), m₆]; exact Mem.readW_writeW_self32 _ _ _⟩) ?_
    refine CT.block_seq [.ebp] (VG.Proof.AesSiv.X86.pin_ebp fun s h => h.1.env.ebp) (by taint_decide)
      (fun s hs => VG.Proof.AesSiv.X86.lm5_ok L hs.1.env hs.1.ctx hs.1.rounds hs.2 hs.1.slen hs.1.nb hj1 (by omega) hk32) ?_
    exact VG.Proof.AesSiv.X86.finCall_ct v L hR hyo (P := W + BitVec.ofNat 32 (32 + 16 * VG.Proof.AesSiv.jOf k)) (l := k - 16 * kOf k - 16 * VG.Proof.AesSiv.jOf k)
      (by omega) fun s₈ ⟨s, hs, _, ax, cx, dx, bx, si, di, bp, sp, rd, wr⟩ =>
        have P₈ := hs.1.env.perm.of_eq rd wr
        ⟨⟨bp, sp, P₈⟩, VG.Proof.AesSiv.X86.srcW L P₈ (t := 32 + 16 * VG.Proof.AesSiv.jOf k) (k := k - 16 * kOf k - 16 * VG.Proof.AesSiv.jOf k) (by omega),
          by rw [L.aW (by omega)]; exact Lay.w_w (by omega) (by omega) (by omega), ax, cx, dx, bx, si, di⟩

/-! ## The whole -/

/-- `finish out` is constant time from what it starts from. -/
theorem finish_ct (v : Ctr32Impl) {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {P : BitVec 32} {k : Nat} (hk32 : k < 2 ^ 32) {out : Nat}
    (hout : out = 0 ∨ out = 112) : CT (VG.Proof.AesSiv.X86.CmacPre C W SP R P k) (finish v.callee v.suffix out) := by
  refine CT.block_seq [.ebp] (VG.Proof.AesSiv.X86.pin_ebp fun s h => h.env.ebp) (by taint_decide)
    (fun s hs => VG.Proof.AesSiv.X86.cmp16_ok L hs.env hs.slen hk32) ?_
  have pre : ∀ s₁, (∃ s, VG.Proof.AesSiv.X86.CmacPre C W SP R P k s ∧ s₁.cf = some (decide (k < 16)) ∧
      (∀ r, r ≠ .ecx → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr) →
      VG.Proof.AesSiv.X86.CmacPre C W SP R P k s₁ := fun s₁ ⟨s, hs, _, g, m, rd, wr⟩ =>
    hs.of_eq (g _ (by decide)) (g _ (by decide)) m rd wr
  refine CT.ite (decide (k < 16)) (fun s ⟨_, _, cf, _⟩ => VG.Proof.AesSiv.X86.eval_b cf) (fun ht => ?_) (fun hf => ?_)
  · have hk16 := of_decide_eq_true ht
    refine CT.seq (J := fun s₂ => VG.Proof.AesSiv.X86.Env C W SP s₂ ∧ slotv s₂.mem W ctxO = C ∧
        slotv s₂.mem W roundsO = BitVec.ofNat 32 R) (VG.Proof.AesSiv.X86.shortTail_ct L hk16 pre)
      (fun s₁ h₁ => WP.mono (VG.Proof.AesSiv.X86.shortTail_ok L (pre s₁ h₁) hk16) fun s₂ ⟨E₂, _, _, f₂, _⟩ => ?_)
      (VG.Proof.AesSiv.X86.shortMac_ct v L hR hout fun s h => h)
    have h₁ := pre s₁ h₁
    have k₂ : ∀ o, 176 ≤ o → o + 4 ≤ 200 → slotv s₂.mem W o = slotv s₁.mem W o := fun o h₁ h₂ =>
      f₂.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Lay.w_w (.inr (by omega)) (by omega) (by decide)
        · exact Lay.w_w (.inr (by omega)) (by omega) (by decide)) (by decide)
    exact ⟨E₂, by rw [k₂ _ (by decide) (by decide)]; exact h₁.ctx, by rw [k₂ _ (by decide) (by decide)]; exact h₁.rounds⟩
  · have h16 : 16 ≤ k := by have := of_decide_eq_false hf; omega
    refine CT.seq (J := fun s₂ => VG.Proof.AesSiv.X86.CmacPre C W SP R P k s₂ ∧ slotv s₂.mem W nbO = BitVec.ofNat 32 (16 * kOf k))
      (VG.Proof.AesSiv.X86.longTail_ct L h16 hk32 pre)
      (fun s₁ h₁ => WP.mono (VG.Proof.AesSiv.X86.longTail_ok L (pre s₁ h₁) h16) fun s₂ ⟨E₂, rd₂, wr₂, f₂, nb₂, _⟩ => ?_)
      (VG.Proof.AesSiv.X86.longMac_ct v L hR h16 hk32 hout fun s h => h)
    have h₁ := pre s₁ h₁
    have k₂ : ∀ o, 176 ≤ o → o + 4 ≤ 208 → slotv s₂.mem W o = slotv s₁.mem W o := fun o h₁ h₂ =>
      f₂.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Lay.w_w (.inr (by omega)) (by omega) (by decide)
        · exact Lay.w_w (.inl h₂) (by omega) (by decide)) (by decide)
    exact ⟨⟨E₂, by rw [k₂ _ (by decide) (by decide)]; exact h₁.ctx, by rw [k₂ _ (by decide) (by decide)]; exact h₁.rounds,
      by rw [k₂ _ (by decide) (by decide)]; exact h₁.str, by rw [k₂ _ (by decide) (by decide)]; exact h₁.slen, h₁.k32,
      h₁.buf.of_eq rd₂ wr₂⟩, nb₂⟩

end VG.Proof.AesSiv.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.X86.Enc`. -/
section

/-!
# AES-SIV on x86: S2V of the associated data, and `vg_aes_siv_encrypt`

Untrusted: everything here is checked by Lean. `encS2v` saves our caller's
registers and keeps the arguments in `W` (`entry_ok`), sets S2V's first
state (`start_ok`), absorbs the components of associated data
(`s2vAds_ok`) and makes the data S2V's last string (`dataStr_ok`):
`encS2v_ok`. `encrypt` then finishes S2V with the plaintext into the IV at
`W` (`finish_ok`), sets the counter from it (`counter_ok`), encrypts the
plaintext with CTR (`ctr_ok`), copies the IV to `siv` (`sivOut_ok`) and
restores the registers (`encrypt_wp`):
`encryptWith` of the context's PRF and cipher (`Spec.Siv.encryptWith_eq`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesSiv.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot restore)
open VG.Proof.AesGcm.X86 (w64 slotv argsR SavedAt savedR exit_ok readW_writeW_off covers_left covers_off ret_below
  length_bytesAt CT argA argA_sub argA_contains w64_add)

/-- What `encrypt` and `decrypt` start from: the key context `C`, `R`
rounds, the `N` descriptors at `A`, the `n` bytes of data at `D`, `siv`
(16 bytes at `T`, which they may at least read) and the working space `W`,
the arguments on the stack at `SP`. -/
structure EPre (C W SP A D T : BitVec 32) (R N n : Nat) (s : State) : Prop where
  ads : AdCtx s C W SP A R N
  data : Dat C W SP s D n
  perm : Perm C W s
  sp : s.gpr .esp = SP
  a0 : arg s 0 = C
  a1 : arg s 1 = BitVec.ofNat 32 R
  a2 : arg s 2 = A
  a3 : arg s 3 = BitVec.ofNat 32 N
  a4 : arg s 4 = D
  a5 : arg s 5 = BitVec.ofNat 32 n
  a6 : arg s 6 = T
  a7 : arg s 7 = W
  rA : Covers [argsR SP 8] (s.rd ++ s.wr)
  aw : (argsR SP 8).Disjoint ⟨w64 W, 2576⟩
  ad : (argsR SP 8).Disjoint ⟨w64 D, n⟩
  as : (below SP 56).Disjoint (argsR SP 8)
  fa : SP.toNat + 4 + 4 * 8 ≤ 2 ^ 32
  ret : (⟨w64 SP, 4⟩ : Region).Disjoint ⟨w64 W, 2576⟩
  retD : (⟨w64 SP, 4⟩ : Region).Disjoint ⟨w64 D, n⟩
  retT : (⟨w64 SP, 4⟩ : Region).Disjoint ⟨w64 T, 16⟩
  n32 : n < 2 ^ 32
  tfit : T.toNat + 16 ≤ 2 ^ 32
  t_rd : Covers [⟨w64 T, 16⟩] (s.rd ++ s.wr)
  t_w : (⟨w64 T, 16⟩ : Region).Disjoint ⟨w64 W, 2576⟩
  t_stk : (below SP 56).Disjoint ⟨w64 T, 16⟩

/-- The data as S2V's last string. -/
theorem dataStr_ok {C W SP : BitVec 32} (L : Lay C W SP) {s : State} (E : Env C W SP s) {D : BitVec 32} {n : Nat}
    (hd : slotv s.mem W dataO = D) (hl : slotv s.mem W lenO = BitVec.ofNat 32 n) :
    ∃ s', runBlock isa [.mov .eax (slot dataO), .store (at_ .ebp strO) .eax, .mov .eax (slot lenO),
        .store (at_ .ebp slenO) .eax] s = some s' ∧
      s'.mem = (s.mem.writeW (w64 W + BitVec.ofNat 64 strO) D).writeW (w64 W + BitVec.ofNat 64 slenO)
        (BitVec.ofNat 32 n) ∧
      s'.gpr .ebp = W ∧ s'.gpr .esp = SP ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [E.ebp, L.aW, E.perm.wW, E.perm.wR, hd, hl], ?_, ?_, ?_, ?_, ?_⟩
  · cmems [hd, hl]
  · cregs [E.ebp]
  · cregs [E.esp]
  all_goals cmems []

/-- The data as S2V's last string: what `cmacOf` and `finish` start from. -/
theorem dataStr_pre {C W SP : BitVec 32} (L : Lay C W SP) {s₀ : State} {R : Nat} {D : BitVec 32} {n : Nat}
    {ext : List Region} {s : State} (K : Kept s₀ C W SP R D n ext s)
    (hext : ∀ r ∈ ext, r.Disjoint ⟨w64 W + BitVec.ofNat 64 128, 2448⟩) (hD : Buf W SP s D n) (hn : n < 2 ^ 32) :
    ∃ s', runBlock isa [.mov .eax (slot dataO), .store (at_ .ebp strO) .eax, .mov .eax (slot lenO),
        .store (at_ .ebp slenO) .eax] s = some s' ∧ CmacPre C W SP R D n s' ∧ Kept s₀ C W SP R D n ext s' ∧
      Frame [⟨w64 W + BitVec.ofNat 64 strO, 8⟩] s.mem s'.mem := by
  obtain ⟨s₄, run₄, m₄, bp₄, sp₄, rd₄, wr₄⟩ := dataStr_ok L K.env K.slots.data K.slots.len
  have E₄ : Env C W SP s₄ := ⟨bp₄, sp₄, K.env.perm.of_eq rd₄ wr₄⟩
  have c (d : Nat) (hd : d + 4 ≤ 8) : (⟨w64 W + BitVec.ofNat 64 strO, 8⟩ : Region).Contains
      (w64 W + BitVec.ofNat 64 strO + BitVec.ofNat 64 d) 4 := Offset.contains_base _ hd (by omega)
  have c0 : (⟨w64 W + BitVec.ofNat 64 strO, 8⟩ : Region).Contains (w64 W + BitVec.ofNat 64 strO) (32 / 8) := by
    simpa using c 0 (by decide)
  have c4 : (⟨w64 W + BitVec.ofNat 64 strO, 8⟩ : Region).Contains (w64 W + BitVec.ofNat 64 slenO) (32 / 8) := by
    have e : w64 W + BitVec.ofNat 64 slenO = w64 W + BitVec.ofNat 64 strO + BitVec.ofNat 64 4 := by
      rw [Offset.add_add]
    rw [e]; exact c 4 (by decide)
  have f₄ : Frame [⟨w64 W + BitVec.ofNat 64 strO, 8⟩] s.mem s₄.mem := by
    rw [m₄]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c0).writeW (List.mem_singleton_self _) _ c4
  have K₄ : Kept s₀ C W SP R D n ext s₄ := K.step L hext E₄ rd₄ wr₄ f₄ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact .inl ⟨wS W, by simp, sub_wS (by decide) (by decide)⟩
  refine ⟨s₄, run₄, ⟨E₄, K₄.slots.ctx, K₄.slots.rounds, ?_, ?_, hn, hD.of_eq rd₄ wr₄⟩, K₄, f₄⟩
  · rw [m₄, slotv, readW_writeW_off _ _ _ (.inl (by decide)) (by decide) (by decide)]
    exact Mem.readW_writeW_self32 _ _ _
  · rw [m₄]; exact Mem.readW_writeW_self32 _ _ _

/-- What `encS2v` leaves: the data as S2V's last string, and `D` S2V's state
of the components. -/
structure S2vOut (C W SP A D : BitVec 32) (R N n : Nat) (s s' : State) : Prop where
  pre : CmacPre C W SP R D n s'
  kept : Kept s C W SP R D n [] s'
  acc : bytesAt s'.mem (w64 W + BitVec.ofNat 64 dOff) 16 =
    Spec.Siv.s2vAcc (Spec.Siv.ctxMac s.mem (w64 C) R) (Spec.Siv.components 32 s.mem (w64 A) N)

/-- The entry's memory, as `Kept` (the slots are the arguments). -/
theorem kept_of_entered {C W SP A D T : BitVec 32} {R N n : Nat} {s s₁ : State} (h : EPre C W SP A D T R N n s)
    (en : Entered s W s₁) : Kept s C W SP R D n [] s₁ ∧ slotv s₁.mem W adsO = A ∧
      slotv s₁.mem W leftO = BitVec.ofNat 32 N := by
  have sl := en.slots
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at sl
  obtain ⟨c₁, r₁, a₁, l₁, d₁, n₁⟩ := sl
  refine ⟨{ env := ⟨en.ebp, by rw [en.esp, h.sp], h.perm.of_eq en.rd en.wr⟩
            rd := en.rd
            wr := en.wr
            slots := ⟨c₁.trans h.a0, r₁.trans h.a1, d₁.trans h.a4, n₁.trans h.a5⟩
            saved := en.saved
            big := en.frame.sub fun r hr => by
              simp only [List.mem_singleton] at hr; subst hr
              exact ⟨⟨w64 W + BitVec.ofNat 64 16, 2560⟩, by simp, Offset.sub _ (by decide) (by decide)⟩ },
    a₁.trans h.a2, l₁.trans h.a3⟩

theorem entry_wp {C W SP A D T : BitVec 32} {R N n : Nat} {s : State} (h : EPre C W SP A D T R N n s) :
    WP isa sivEntry s (Entered s W) := by
  have L := h.ads.lay
  have wW : Covers [⟨w64 W, 2560⟩] s.wr := fun a m ⟨r, hr, hc⟩ => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.perm.w a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩
  have aw : (argsR (s.gpr .esp) 8).Disjoint ⟨w64 W, 2560⟩ := by
    rw [h.sp]; exact h.aw.sub_right (Region.sub_prefix (by decide))
  exact entry_ok (s := s) (W := W) h.a7 wW (by rw [h.sp]; exact h.rA) aw (by rw [h.sp]; exact h.fa)
    (by have := L.fw; omega)

/-- S2V's first state, after the entry. -/
theorem start_wp (v : Ctr32Impl) {C W SP A D T : BitVec 32} {R N n : Nat} {s s₁ : State}
    (h : EPre C W SP A D T R N n s) (en : Entered s W s₁) :
    WP isa (start v.callee v.suffix) s₁ (AInv s C W SP A R N D n 0) := by
  have L := h.ads.lay
  obtain ⟨K₁, a₁, l₁⟩ := kept_of_entered h en
  refine WP.mono (start_ok v L h.ads.rounds K₁) fun s₂ ⟨K₂, f₂, st₂⟩ => ?_
  have k₂ : ∀ o, 176 ≤ o → o + 4 ≤ 200 → slotv s₂.mem W o = slotv s₁.mem W o := fun o h₁ h₂ =>
    f₂.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact Lay.w_w (.inr (by omega)) (by omega) (by decide)
      · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
      · exact (L.stk_w' (by omega)).symm) (by decide)
  exact ⟨K₂, Nat.zero_le _, by rw [k₂ _ (by decide) (by decide), a₁, Nat.mul_zero]; exact (BitVec.add_zero _).symm,
    by rw [k₂ _ (by decide) (by decide), l₁, Nat.sub_zero],
    by rw [List.take_zero, Spec.Siv.s2vAcc, List.foldl_nil]; exact st₂⟩

/-- The data as S2V's last string, after S2V of the associated data. -/
theorem s2vEnd_ok {C W SP A D T : BitVec 32} {R N n : Nat} {s s₃ : State} (h : EPre C W SP A D T R N n s)
    (I : AInv s C W SP A R N D n N s₃) :
    ∃ s₄, runBlock isa [.mov .eax (slot dataO), .store (at_ .ebp strO) .eax, .mov .eax (slot lenO),
      .store (at_ .ebp slenO) .eax] s₃ = some s₄ ∧ S2vOut C W SP A D R N n s s₄ := by
  have L := h.ads.lay
  obtain ⟨s₄, run₄, P₄, K₄, f₄⟩ := dataStr_pre L I.kept (by simp) (h.data.buf.of_eq I.kept.rd I.kept.wr) h.n32
  refine ⟨s₄, run₄, P₄, K₄, ?_⟩
  rw [Proof.AesGcm.X86.bytesAt_frame f₄ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by decide)) (by decide) (by decide))
    (by decide), I.acc, components_take_all]

theorem encS2v_ok (v : Ctr32Impl) {C W SP A D T : BitVec 32} {R N n : Nat} {s : State}
    (h : EPre C W SP A D T R N n s) :
    WP isa (encS2v v.callee v.suffix) s (S2vOut C W SP A D R N n s) := by
  refine WP.seq (WP.mono (entry_wp h) fun s₁ en => ?_)
  refine WP.seq (WP.mono (start_wp v h en) fun s₂ I₀ => ?_)
  refine WP.seq (WP.mono (s2vAds_ok v h.ads I₀) fun s₃ I => ?_)
  obtain ⟨s₄, run₄, O⟩ := s2vEnd_ok h I
  exact WP.of_runBlock ⟨s₄, run₄, O⟩

/-! ## `vg_aes_siv_encrypt` -/

theorem Kept.widen {s₀ : State} {C W SP : BitVec 32} {R : Nat} {D : BitVec 32} {n : Nat} {ext : List Region}
    {s : State} (h : Kept s₀ C W SP R D n ext s) (e : Region) : Kept s₀ C W SP R D n (ext ++ [e]) s :=
  { h with big := h.big.mono fun r hr => by rw [← List.append_assoc]; exact List.mem_append_left _ hr }

/-- The IV at `W`, while no piece names it. -/
theorem Kept.iv {s₀ : State} {C W SP : BitVec 32} {R : Nat} {D : BitVec 32} {n : Nat} {ext : List Region}
    {s : State} (L : Lay C W SP) (h : Kept s₀ C W SP R D n ext s)
    (he : ∀ r ∈ ext, (⟨w64 W, 16⟩ : Region).Disjoint r) : bytesAt s.mem (w64 W) 16 = bytesAt s₀.mem (w64 W) 16 :=
  Proof.AesGcm.X86.bytesAt_frame h.big (fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons] at hr
    rcases hr with rfl | rfl | hr
    · simpa using Lay.w_w (W := W) (a := 0) (n := 16) (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w.sub_right (Region.sub_prefix (by decide))).symm
    · exact he r hr) (by decide)

/-- What `finish out` writes: the IV at `W` (which the pieces name in `ext`) or
the IV at `W + 112`, and parts of `W` the pieces write. -/
theorem finR_wR {W SP : BitVec 32} {out : Nat} {ext : List Region}
    (hout : out = 0 ∧ (⟨w64 W, 16⟩ : Region) ∈ ext ∨ out = 112) :
    ∀ r ∈ finR W SP out, (∃ r' ∈ wR W SP, Region.Sub r r') ∨ ∃ r' ∈ ext, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rcases hout with ⟨rfl, he⟩ | rfl
    · exact .inr ⟨_, he, Offset.sub_base _ (by decide)⟩
    · exact .inl ⟨wA W, by simp, Offset.sub _ (by decide) (by decide)⟩
  · exact .inl ⟨wA W, by simp, Offset.sub _ (by decide) (by decide)⟩
  · exact .inl ⟨wB W, by simp, fun _ h => h⟩
  · exact .inl ⟨wS W, by simp, fun _ h => h⟩
  · exact .inl ⟨wC W, by simp, Offset.sub _ (by decide) (by decide)⟩
  · exact .inl ⟨below SP 56, by simp, fun _ h => h⟩

theorem ctrR_wR {W SP D : BitVec 32} {n : Nat} {ext : List Region} (he : (⟨w64 D, n⟩ : Region) ∈ ext) :
    ∀ r ∈ ctrR W SP D n, (∃ r' ∈ wR W SP, Region.Sub r r') ∨ ∃ r' ∈ ext, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact .inl ⟨wA W, by simp, Offset.sub _ (by decide) (by decide)⟩
  · exact .inl ⟨wC W, by simp, Offset.sub _ (by decide) (by decide)⟩
  · exact .inl ⟨below SP 56, by simp, fun _ h => h⟩
  · exact .inr ⟨_, he, fun _ h => h⟩

/-- The counter block: written by `counter`, in `wA`. -/
theorem counter_wR {W SP : BitVec 32} {e : List Region} :
    ∀ r ∈ [(⟨w64 W + BitVec.ofNat 64 cbOff, 16⟩ : Region)],
      (∃ r' ∈ wR W SP, Region.Sub r r') ∨ ∃ r' ∈ e, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact .inl ⟨wA W, by simp, Offset.sub _ (by decide) (by decide)⟩

/-- `siv`'s address, the stack argument 6, as on entry, after code that wrote
apart from the arguments. -/
theorem Kept.arg6 {C W SP A D T : BitVec 32} {R N n : Nat} {s₀ s : State} (h : EPre C W SP A D T R N n s₀)
    {ext : List Region} (K : Kept s₀ C W SP R D n ext s)
    (he : ∀ r ∈ ext, (argsR SP 8).Disjoint r) :
    s.mem.readW (argA SP 6) 32 = T ∧ InRegions (s.rd ++ s.wr) (argA SP 6) 4 := by
  have hs6 := argA_sub (SP := SP) (n := 8) (i := 6) (by decide) h.fa
  refine ⟨?_, by rw [K.rd, K.wr]; exact h.rA _ _ ⟨_, List.mem_singleton_self _, argA_contains (by decide) h.fa⟩⟩
  rw [K.big.readW (r := ⟨argA SP 6, 4⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons] at hr
    rcases hr with rfl | rfl | hr
    · exact (h.aw.sub_left hs6).sub_right (Lay.wSub (by decide))
    · exact h.as.symm.sub_left hs6
    · exact (he r hr).sub_left hs6) (by decide), ← h.a6, arg, argAddr, h.sp]

/-- `sivOut`: the IV at `W` copied to `T`, the stack argument 6. -/
theorem sivOut_ok {C W SP : BitVec 32} (L : Lay C W SP) {s : State} (E : Env C W SP s) {T : BitVec 32}
    (hin : InRegions (s.rd ++ s.wr) (argA SP 6) 4) (hv : s.mem.readW (argA SP 6) 32 = T)
    (tW : Covers [⟨w64 T, 16⟩] s.wr) (fT : T.toNat + 16 ≤ 2 ^ 32) :
    WP isa sivOut s fun s' => bytesAt s'.mem (w64 T) 16 = bytesAt s.mem (w64 W + BitVec.ofNat 64 0) 16 ∧
      Frame [⟨w64 T, 16⟩] s.mem s'.mem ∧ s'.gpr .ebp = W ∧ s'.gpr .esp = SP ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have aT : ∀ {k}, k < 16 → w64 (T + BitVec.ofNat 32 k) = w64 T + BitVec.ofNat 64 k := fun hk => w64_add (by omega)
  have tIn : ∀ {k}, k + 4 ≤ 16 → InRegions s.wr (w64 T + BitVec.ofNat 64 k) 4 := fun hk =>
    Proof.AesGcm.X86.in_off tW hk (by decide)
  have hs := Proof.AesGcm.X86.store4_eq s.mem T 0
  simp only [Nat.reduceAdd] at hs
  refine WP.seq (WP.of_runBlock ⟨_, by crun [E.ebp, E.esp, L.aW, E.perm.wR, hin, hv], ?_⟩)
  refine WP.of_runBlock ⟨_, by crun [aT, tIn], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cmems [hs]
    rw [show w64 T + 0#64 = w64 T from BitVec.add_zero _, Cmac.bytesAt_store4, Cmac.bytesAt_split4, Cmac.le4_readW,
      Cmac.le4_readW, Cmac.le4_readW, Cmac.le4_readW, add_ofNat_assoc, add_ofNat_assoc, add_ofNat_assoc]
  · cmems [hs]
    rw [show w64 T + 0#64 = w64 T from BitVec.add_zero _]
    exact Cmac.frame_store4 _ _ _ _ _
  · cregs [E.ebp]
  · cregs [E.esp]
  · cmems []
  · cmems []

/-- `vg_aes_siv_encrypt`: the synthetic IV at `T` and the ciphertext in place. -/
theorem encrypt_wp (v : Ctr32Impl) {C W SP A D T : BitVec 32} {R N n : Nat} {s : State}
    (h : EPre C W SP A D T R N n s) (hTw : Covers [⟨w64 T, 16⟩] s.wr)
    (hTd : (⟨w64 T, 16⟩ : Region).Disjoint ⟨w64 D, n⟩) :
    WP isa (encrypt v.callee v.suffix) s fun s' => abiPreserved s s' ∧
      Spec.Siv.encryptWith (Spec.Siv.ctxMac s.mem (w64 C) R) (Spec.Siv.ctxCiph s.mem (w64 C) R)
          (Spec.Siv.components 32 s.mem (w64 A) N) (bytesAt s.mem (w64 D) n) =
        (bytesAt s'.mem (w64 T) 16, bytesAt s'.mem (w64 D) n) := by
  have L := h.ads.lay
  have hR := h.ads.rounds
  have hRb := rounds_le hR
  have hW16 : (⟨w64 W, 16⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 128, 2448⟩ := by
    simpa using Lay.w_w (W := W) (a := 0) (n := 16) (.inl (by decide)) (by decide) (by decide)
  have hDw : (⟨w64 D, n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 128, 2448⟩ :=
    h.data.buf.w.sub_right (Lay.wSub (by decide))
  refine WP.seq (WP.mono (encS2v_ok v h) fun s₁ O => ?_)
  have K₁ := O.kept
  refine WP.seq (WP.mono (finish_ok v L hR O.pre (out := 0) (.inl rfl)) fun s₂ F => ?_)
  have K₂ : Kept s C W SP R D n [⟨w64 W, 16⟩] s₂ := (K₁.widen ⟨w64 W, 16⟩).step L
    (fun r hr => by simp only [List.nil_append, List.mem_singleton] at hr; subst hr; exact hW16)
    F.env F.rd F.wr F.frame (finR_wR (.inl ⟨rfl, by simp⟩))
  obtain ⟨s₃, run₃, m₃, bp₃, sp₃, rd₃, wr₃⟩ := counter_ok L F.env
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have E₃ : Env C W SP s₃ := ⟨bp₃, sp₃, F.env.perm.of_eq rd₃ wr₃⟩
  have f₃ : Frame [⟨w64 W + BitVec.ofNat 64 cbOff, 16⟩] s₂.mem s₃.mem := by
    rw [m₃]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  have K₃ : Kept s C W SP R D n [⟨w64 W, 16⟩] s₃ := K₂.step L
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hW16) E₃ rd₃ wr₃ f₃ counter_wR
  have hq : bytesAt s₃.mem (w64 W + BitVec.ofNat 64 cbOff) 16 = Spec.Siv.counter (bytesAt s₂.mem (w64 W) 16) := by
    rw [m₃]; exact counter_bytes _ _
  have hD₃ : Dat C W SP s₃ D n := h.data.of_eq K₃.rd K₃.wr
  refine WP.seq (WP.mono (ctr_ok v L hR E₃ hD₃ h.n32 K₃.slots.ctx K₃.slots.rounds K₃.slots.data K₃.slots.len hq
    (counter_low _)) fun s₄ ⟨E₄, rd₄, wr₄, f₄, d₄⟩ => ?_)
  have K₄ : Kept s C W SP R D n [⟨w64 W, 16⟩, ⟨w64 D, n⟩] s₄ := (K₃.widen _).step L (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hW16
      · exact hDw) E₄ rd₄ wr₄ f₄ (ctrR_wR (by simp))
  -- The IV copied to `siv`.
  have hs6 := argA_sub (SP := SP) (n := 8) (i := 6) (by decide) h.fa
  have v6 : s₄.mem.readW (argA SP 6) 32 = T := by
    rw [K₄.big.readW (r := ⟨argA SP 6, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact (h.aw.sub_left hs6).sub_right (Lay.wSub (by decide))
      · exact h.as.symm.sub_left hs6
      · exact (h.aw.sub_left hs6).sub_right (Region.sub_prefix (by decide))
      · exact h.ad.sub_left hs6) (by decide), ← h.a6, arg, argAddr, h.sp]
  have i6 : InRegions (s₄.rd ++ s₄.wr) (argA SP 6) 4 := by
    rw [K₄.rd, K₄.wr]; exact h.rA _ _ ⟨_, List.mem_singleton_self _, argA_contains (by decide) h.fa⟩
  refine WP.seq (WP.mono (sivOut_ok L K₄.env i6 v6 (by rw [K₄.wr]; exact hTw) h.tfit)
    fun s₅ ⟨iv₅, f₅, bp₅, sp₅, rd₅, wr₅⟩ => ?_)
  have hTW : (⟨w64 T, 16⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 128, 2448⟩ :=
    h.t_w.sub_right (Lay.wSub (by decide))
  have K₅ : Kept s C W SP R D n ([⟨w64 W, 16⟩, ⟨w64 D, n⟩] ++ [⟨w64 T, 16⟩]) s₅ := (K₄.widen _).step L
    (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hW16
      · exact hDw
      · exact hTW) ⟨bp₅, sp₅, K₄.env.perm.of_eq rd₅ wr₅⟩ rd₅ wr₅ f₅ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact .inr ⟨_, by simp, fun _ h => h⟩)
  have hret : s₅.mem.readW (w64 (s.gpr .esp)) 32 = s.mem.readW (w64 (s.gpr .esp)) 32 := by
    rw [h.sp]
    exact K₅.big.readW (r := ⟨w64 SP, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact h.ret.sub_right (Lay.wSub (by decide))
      · exact ret_below L.sp
      · exact h.ret.sub_right (Region.sub_prefix (by decide))
      · exact h.retD
      · exact h.retT) (by decide)
  refine WP.mono (exit_ok K₅.env.ebp (by rw [K₅.env.esp, h.sp]) (covers_left (fun a m ⟨r, hr, hc⟩ => by
      simp only [List.mem_singleton] at hr; subst hr
      exact K₅.env.perm.w a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩))
    (by have := L.fw; omega) K₅.saved hret) fun s₆ ⟨ab, m₆, _, _, _⟩ => ⟨ab, ?_⟩
  have pD : bytesAt s₅.mem (w64 D) n = bytesAt s₄.mem (w64 D) n :=
    Proof.AesGcm.X86.bytesAt_frame f₅ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hTd.symm) (by have := h.data.buf.lt; omega)
  -- The values.
  have dW : ∀ r ∈ ctrR W SP D n, (⟨w64 W, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa using Lay.w_w (W := W) (a := 0) (n := 16) (.inl (by decide)) (by decide) (by decide)
    · simpa using Lay.w_w (W := W) (a := 0) (n := 16) (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w.sub_right (Region.sub_prefix (by decide))).symm
    · exact (h.data.buf.w.sub_right (Region.sub_prefix (by decide))).symm
  have iv : bytesAt s₄.mem (w64 W) 16 = bytesAt s₂.mem (w64 W) 16 := by
    rw [Proof.AesGcm.X86.bytesAt_frame f₄ dW (by decide), Proof.AesGcm.X86.bytesAt_frame f₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      simpa using Lay.w_w (W := W) (a := 0) (n := 16) (.inl (by decide)) (by decide) (by decide)) (by decide)]
  have dc : ∀ r ∈ ([] : List Region), (⟨w64 C, 512⟩ : Region).Disjoint r := by simp
  have mac₁ : Spec.Siv.ctxMac s₁.mem (w64 C) R = Spec.Siv.ctxMac s.mem (w64 C) R := K₁.mac L hR dc
  have ciph₃ : Spec.Siv.ctxCiph s₃.mem (w64 C) R = Spec.Siv.ctxCiph s.mem (w64 C) R :=
    ctxCiph_frame K₃.big (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact L.c_w.sub_right (Lay.wSub (by decide))
      · exact L.stk_c.symm
      · exact L.c_w.sub_right (Region.sub_prefix (by decide))) hRb
  have dDW : (⟨w64 D, n⟩ : Region).Disjoint ⟨w64 W, 16⟩ := h.data.buf.w.sub_right (Region.sub_prefix (by decide))
  have p₁ : bytesAt s₁.mem (w64 D) n = bytesAt s.mem (w64 D) n :=
    K₁.bytes h.data.buf.w h.data.buf.stk (by simp) (by have := h.data.buf.lt; omega)
  have p₃ : bytesAt s₃.mem (w64 D) n = bytesAt s.mem (w64 D) n :=
    K₃.bytes h.data.buf.w h.data.buf.stk (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dDW) (by have := h.data.buf.lt; omega)
  have o₂ := F.out
  rw [BitVec.add_zero] at o₂
  rw [m₆, iv₅, BitVec.add_zero, pD, Spec.Siv.encryptWith_eq, Spec.Siv.sealWith, d₄, iv, o₂, mac₁, O.acc, p₁,
    ciph₃, p₃]

end VG.Proof.AesSiv.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.X86.Dec`. -/
section

/-!
# AES-SIV on x86: `vg_aes_siv_decrypt`

Untrusted: everything here is checked by Lean. `decrypt` copies the received
IV from `siv` to `W` (`sivIn_ok`) after S2V of the associated data, decrypts
the data with CTR from it, finishes S2V with the plaintext into `W + 112`,
compares the IVs without a branch and masks the data with the result
(`decrypt_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesSiv.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot restore)
open VG.Proof.AesGcm.X86 (exit_ok ret_below covers_left readW_writeW_off argA argA_sub argA_contains)
open VG.Proof.AesGcm.X86 (w64 slotv bytes16_eq xor4_eq_zero w64_add in_of_covers succ_ofNat32 add_zero32 pred_count
  pred_beq bytesAt_succ length_bytesAt and_self_beq32 CT)

/-- `cmp eax, 1` and `adc` of 0 after the OR of the XORs of two blocks' words:
1 if they are equal, else 0. -/
theorem cmpAdc (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : BitVec 32) :
    0#32 + 0#32 + BitVec.setWidth 32 (BitVec.ofBool (decide
      ((a₀ ^^^ b₀ ||| a₁ ^^^ b₁ ||| a₂ ^^^ b₂ ||| a₃ ^^^ b₃).toNat < (1#32).toNat))) =
      BitVec.ofNat 32 (if a₀ = b₀ ∧ a₁ = b₁ ∧ a₂ = b₂ ∧ a₃ = b₃ then 1 else 0) := by
  have e := xor4_eq_zero a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃
  by_cases h : a₀ = b₀ ∧ a₁ = b₁ ∧ a₂ = b₂ ∧ a₃ = b₃
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    simp only [and_self, ↓reduceIte, BitVec.xor_self, BitVec.or_self]
    decide
  · have h0 : (a₀ ^^^ b₀) ||| (a₁ ^^^ b₁) ||| (a₂ ^^^ b₂) ||| (a₃ ^^^ b₃) ≠ 0 := fun h' => h (e.mp h')
    have hne : ((a₀ ^^^ b₀) ||| (a₁ ^^^ b₁) ||| (a₂ ^^^ b₂) ||| (a₃ ^^^ b₃)).toNat ≠ 0 := fun h' =>
      h0 (BitVec.eq_of_toNat_eq (by simpa using h'))
    have hlt : ¬ ((a₀ ^^^ b₀) ||| (a₁ ^^^ b₁) ||| (a₂ ^^^ b₂) ||| (a₃ ^^^ b₃)).toNat < (1#32).toNat := by
      rw [BitVec.toNat_ofNat]; omega
    simp only [h, ↓reduceIte, decide_eq_false hlt]
    rfl

/-- Whether the IVs at `W` and `W + 112` are equal, as a word. -/
abbrev okVal (m : Mem) (W : BitVec 32) : BitVec 32 :=
  BitVec.ofNat 32 (if bytesAt m (w64 W) 16 = bytesAt m (w64 W + BitVec.ofNat 64 tOff) 16 then 1 else 0)

theorem compare_ok {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {s : State} (E : VG.Proof.AesSiv.X86.Env C W SP s) :
    ∃ s', runBlock isa compare s = some s' ∧ s'.mem = s.mem.writeW (w64 W + BitVec.ofNat 64 okO) (VG.Proof.AesSiv.X86.okVal s.mem W) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [Impl.AesSiv.X86.compare, E.ebp, L.aW, E.perm.wR, E.perm.wW], ?_, fun r h₁ h₂ => ?_, ?_, ?_⟩
  · cmems []
    rw [VG.Proof.AesSiv.X86.cmpAdc]
    simp only [VG.Proof.AesSiv.X86.okVal, bytes16_eq, BitVec.add_zero, VG.Proof.AesSiv.X86.add_ofNat_assoc, Nat.reduceAdd, tOff]
  · cregs []
  all_goals cmems []

/-! ## `mask` -/

theorem mask_byte32 (b : Byte) (c : Bool) :
    ((b.setWidth 32 &&& ((0 : BitVec 32) - (if c then 1 else 0))).setWidth 8) = if c then b else 0 := by
  cases c
  · simp
  · rw [show (if true = true then (1 : BitVec 32) else 0) = 1 from rfl,
      show (0 : BitVec 32) - 1 = BitVec.allOnes 32 by decide, BitVec.and_allOnes]
    simp

abbrev maskBody : List Instr :=
  [.movzx8 .edx (at_ .edi 0), .alu .and .edx (.reg .ebx), .store8 (at_ .edi 0) .dl, .alu .add .edi (imm 1),
    .alu .sub .ecx (imm 1)]

theorem maskStep_ok (s : State) {P : BitVec 32} {i n : Nat} {c : Bool} (hs : s.gpr .edi = P + BitVec.ofNat 32 i)
    (hc : s.gpr .ecx = BitVec.ofNat 32 (n - i)) (hb : s.gpr .ebx = 0 - (if c then 1 else 0))
    (eP : w64 (P + BitVec.ofNat 32 i) = w64 P + BitVec.ofNat 64 i)
    (r : InRegions (s.rd ++ s.wr) (w64 P + BitVec.ofNat 64 i) 1) (w : InRegions s.wr (w64 P + BitVec.ofNat 64 i) 1) :
    ∃ s', runBlock isa VG.Proof.AesSiv.X86.maskBody s = some s' ∧
      s'.mem = s.mem.writeW (w64 P + BitVec.ofNat 64 i) ((if c then s.mem (w64 P + BitVec.ofNat 64 i) else 0 : Byte)) ∧
      s'.gpr .edi = P + BitVec.ofNat 32 (i + 1) ∧ s'.gpr .ecx = BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 ∧
      s'.zf = some (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) ∧
      (∀ r, r ≠ .edx → r ≠ .edi → r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [VG.Proof.AesSiv.X86.maskBody, add_zero32, hs, eP, r, w], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cmems [hb, VG.Proof.AesSiv.X86.mask_byte32]
  · cregs [hs, succ_ofNat32]
  · cregs [hc]
  · cmems [hc]
  · intro r h₁ h₂ h₃; cregs [h₁, h₂, h₃]
  all_goals cmems []

theorem length_mask (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P j else Spec.Siv.zeros j).length = j := by
  cases c <;> simp [Spec.Siv.zeros, length_bytesAt]

theorem mask_succ (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P (j + 1) else Spec.Siv.zeros (j + 1)) =
      (if c then bytesAt m P j else Spec.Siv.zeros j) ++ [if c then m (P + BitVec.ofNat 64 j) else 0] := by
  cases c <;> simp [Spec.Siv.zeros, bytesAt_succ, List.replicate_succ']

/-- Every byte of the data ANDed with `0 − ok`, for `ok` (at `W + okO`) 1 or 0. -/
theorem mask_ok {C W SP : BitVec 32} {s : State} (L : VG.Proof.AesSiv.X86.Lay C W SP) (E : VG.Proof.AesSiv.X86.Env C W SP s) {D : BitVec 32} {n : Nat}
    (hDp : slotv s.mem W dataO = D) (hlen : slotv s.mem W lenO = BitVec.ofNat 32 n) (hn32 : n < 2 ^ 32)
    (hD : VG.Proof.AesSiv.X86.Buf W SP s D n) (hDw : Covers [⟨w64 D, n⟩] s.wr) {c : Bool}
    (hok : slotv s.mem W okO = if c then 1 else 0) :
    WP isa mask s fun s' => VG.Proof.AesSiv.X86.Env C W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = VG.WriteBytes.writeBytes s.mem (w64 D) (if c then bytesAt s.mem (w64 D) n else Spec.Siv.zeros n) := by
  obtain ⟨s₁, run₁, m₁, cx₁, zf₁, bp₁, sp₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [.mov .ecx (slot lenO), .alu .test .ecx (.reg .ecx)] s = some s₁ ∧ s₁.mem = s.mem ∧
      s₁.gpr .ecx = BitVec.ofNat 32 n ∧ s₁.zf = some (decide (n = 0)) ∧ s₁.gpr .ebp = W ∧ s₁.gpr .esp = SP ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by crun [E.ebp, L.aW, E.perm.wR, hlen], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · cregs [hlen]
    · cmems [hlen]; rw [and_self_beq32 hn32]
    · cregs [E.ebp]
    · cregs [E.esp]
    all_goals cmems []
  have E₁ : VG.Proof.AesSiv.X86.Env C W SP s₁ := E.keep (by rw [bp₁, E.ebp]) (by rw [sp₁, E.esp]) rd₁ wr₁
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (n = 0)) (VG.Proof.AesSiv.X86.eval_e zf₁) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hn0 : n = 0 := of_decide_eq_true hb
    subst hn0
    refine ⟨E₁, rd₁, wr₁, ?_⟩
    rw [m₁]
    cases c <;> simp [Spec.Aes.bytesAt, Spec.Siv.zeros, VG.WriteBytes.writeBytes_nil]
  have hn0 : 0 < n := Nat.pos_of_ne_zero (of_decide_eq_false hb)
  obtain ⟨s₂, run₂, m₂, bx₂, di₂, cx₂, bp₂, sp₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa
      [.mov .ebx (imm 0), .alu .sub .ebx (slot okO), .mov .edi (slot dataO)] s₁ = some s₂ ∧ s₂.mem = s.mem ∧
      s₂.gpr .ebx = 0 - (if c then 1 else 0) ∧ s₂.gpr .edi = D ∧ s₂.gpr .ecx = BitVec.ofNat 32 n ∧
      s₂.gpr .ebp = W ∧ s₂.gpr .esp = SP ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
    have hok₁ : slotv s₁.mem W okO = if c then 1 else 0 := by rw [m₁]; exact hok
    have hd₁ : slotv s₁.mem W dataO = D := by rw [m₁]; exact hDp
    refine ⟨_, by crun [bp₁, L.aW, E₁.perm.wR, hok₁, hd₁], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · cmems [m₁]
    · cregs [hok₁]; rfl
    · cregs [hd₁]
    · cregs [cx₁]
    · cregs [bp₁]
    · cregs [sp₁]
    · cmems [rd₁]
    · cmems [wr₁]
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have hfD := hD.wrap
  refine WP.loop (M := isa) (body := .block VG.Proof.AesSiv.X86.maskBody) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ j, k = n - j ∧ j < n ∧ t.gpr .edi = D + BitVec.ofNat 32 j ∧
      t.gpr .ecx = BitVec.ofNat 32 (n - j) ∧
      t.mem = VG.WriteBytes.writeBytes s.mem (w64 D) (if c then bytesAt s.mem (w64 D) j else Spec.Siv.zeros j) ∧
      (∀ r, r ≠ .edx → r ≠ .edi → r ≠ .ecx → t.gpr r = s₂.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (n - 0) _
    ⟨0, rfl, hn0, by rw [di₂, add_zero32], by rw [cx₂, Nat.sub_zero], by
      rw [m₂]; cases c <;> simp [Spec.Aes.bytesAt, Spec.Siv.zeros, VG.WriteBytes.writeBytes_nil], fun r _ _ _ => rfl, rd₂, wr₂⟩
  rintro k t ⟨j, rfl, hj, di, cx, mem, g, rd, wr⟩
  obtain ⟨t', run', mem', di', cx', zf', g', rd', wr'⟩ := VG.Proof.AesSiv.X86.maskStep_ok t (P := D) (i := j) (n := n) (c := c) di cx
    (by rw [g _ (by decide) (by decide) (by decide), bx₂]) (w64_add (by omega))
    (by rw [rd, wr]; exact in_of_covers hD.rd hj (by omega))
    (by rw [wr]; exact in_of_covers hDw hj (by omega))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have fr : Frame [⟨w64 D, j⟩] s.mem t.mem := by
    rw [mem]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [VG.Proof.AesSiv.X86.length_mask]; exact Region.contains_self _ _)
  have hq : t.mem (w64 D + BitVec.ofNat 64 j) = s.mem (w64 D + BitVec.ofNat 64 j) :=
    fr _ fun r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      simp only [Region.Contains, Mem.sub_ofNat_toNat (w64 D) (show j < 2 ^ 64 by omega)] at hcon; omega
  have hmem : t'.mem = VG.WriteBytes.writeBytes s.mem (w64 D) (if c then bytesAt s.mem (w64 D) (j + 1) else Spec.Siv.zeros (j + 1)) := by
    rw [mem', hq, mem, VG.Proof.AesSiv.X86.mask_succ, VG.WriteBytes.writeBytes_snoc _ _ _ _ (by rw [VG.Proof.AesSiv.X86.length_mask]; omega), VG.Proof.AesSiv.X86.length_mask]
  have hz : t'.zf = some (decide (j + 1 = n)) := by rw [zf', pred_beq hj hn32]
  have gg : ∀ r, r ≠ .edx → r ≠ .edi → r ≠ .ecx → t'.gpr r = s₂.gpr r := fun r h₁ h₂ h₃ => by
    rw [g' r h₁ h₂ h₃, g r h₁ h₂ h₃]
  have E' : VG.Proof.AesSiv.X86.Env C W SP t' := ⟨by rw [gg _ (by decide) (by decide) (by decide), bp₂],
    by rw [gg _ (by decide) (by decide) (by decide), sp₂], E.perm.of_eq (by rw [rd', rd]) (by rw [wr', wr])⟩
  by_cases he : j + 1 = n
  · left
    exact ⟨by simp [eval, hz, he], E', by rw [rd', rd], by rw [wr', wr], by rw [hmem, he]⟩
  · right
    refine ⟨by simp [eval, hz, he], n - (j + 1), by omega, j + 1, rfl, by omega, di',
      by rw [cx', pred_count hj hn32], hmem, gg, by rw [rd', rd], by rw [wr', wr]⟩


/-! ## `vg_aes_siv_decrypt` -/

theorem okVal_eq (m : Mem) (W : BitVec 32) :
    VG.Proof.AesSiv.X86.okVal m W = if decide (bytesAt m (w64 W) 16 = bytesAt m (w64 W + BitVec.ofNat 64 tOff) 16) then 1 else 0 := by
  unfold VG.Proof.AesSiv.X86.okVal; split <;> simp_all

theorem retEax_ok {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {s : State} (E : VG.Proof.AesSiv.X86.Env C W SP s) :
    ∃ s', runBlock isa [.mov .eax (slot okO)] s = some s' ∧ s'.gpr .eax = slotv s.mem W okO ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [E.ebp, L.aW, E.perm.wR], ?_, fun r h₁ => ?_, ?_, ?_, ?_⟩
  · cregs []
  · cregs []
  all_goals cmems []

/-- `sivIn`: the IV at `T`, the stack argument 6, copied to `W`. -/
theorem sivIn_ok {C W SP : BitVec 32} (L : Lay C W SP) {s : State} (E : Env C W SP s) {T : BitVec 32}
    (hin : InRegions (s.rd ++ s.wr) (argA SP 6) 4) (hv : s.mem.readW (argA SP 6) 32 = T)
    (tR : Covers [⟨w64 T, 16⟩] (s.rd ++ s.wr)) (fT : T.toNat + 16 ≤ 2 ^ 32) :
    WP isa sivIn s fun s' => bytesAt s'.mem (w64 W + BitVec.ofNat 64 0) 16 = bytesAt s.mem (w64 T + BitVec.ofNat 64 0) 16 ∧
      Frame [⟨w64 W + BitVec.ofNat 64 0, 16⟩] s.mem s'.mem ∧ s'.gpr .ebp = W ∧ s'.gpr .esp = SP ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have aT : ∀ {k}, k < 16 → w64 (T + BitVec.ofNat 32 k) = w64 T + BitVec.ofNat 64 k := fun hk => w64_add (by omega)
  have tIn : ∀ {k}, k + 4 ≤ 16 → InRegions (s.rd ++ s.wr) (w64 T + BitVec.ofNat 64 k) 4 := fun hk =>
    Proof.AesGcm.X86.in_off tR hk (by decide)
  have hs := Proof.AesGcm.X86.store4_eq s.mem W 0
  simp only [Nat.reduceAdd] at hs
  refine WP.seq (WP.of_runBlock ⟨_, by crun [E.esp, hin, hv], ?_⟩)
  refine WP.of_runBlock ⟨_, by crun [aT, tIn, E.ebp, L.aW, E.perm.wW], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cmems [hs]
    rw [Cmac.bytesAt_store4, Cmac.bytesAt_split4, Cmac.le4_readW, Cmac.le4_readW, Cmac.le4_readW, Cmac.le4_readW,
      add_ofNat_assoc, add_ofNat_assoc, add_ofNat_assoc]
  · cmems [hs]
    exact Cmac.frame_store4 _ _ _ _ _
  · cregs [E.ebp]
  · cregs [E.esp]
  · cmems []
  · cmems []

/-- What a piece writes in `wR` or the data misses the IV at `W`. -/
theorem w16_dis {C W SP D : BitVec 32} {n : Nat} (L : Lay C W SP)
    (hD : (⟨w64 W, 16⟩ : Region).Disjoint ⟨w64 D, n⟩) {rs : List Region}
    (hs : ∀ r ∈ rs, (∃ r' ∈ wR W SP, Region.Sub r r') ∨ ∃ r' ∈ [(⟨w64 D, n⟩ : Region)], Region.Sub r r') :
    ∀ r ∈ rs, (⟨w64 W, 16⟩ : Region).Disjoint r := by
  intro r hr
  rcases hs r hr with ⟨r', hr', hsub⟩ | ⟨r', hr', hsub⟩
  · refine Region.Disjoint.sub_right ?_ hsub
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl
    · simpa using Lay.w_w (W := W) (a := 0) (n := 16) (d := 16) (k := 112) (.inl (by decide)) (by decide) (by decide)
    · simpa using Lay.w_w (W := W) (a := 0) (n := 16) (d := 144) (k := 32) (.inl (by decide)) (by decide) (by decide)
    · simpa using Lay.w_w (W := W) (a := 0) (n := 16) (d := 184) (k := 8) (.inl (by decide)) (by decide) (by decide)
    · simpa using Lay.w_w (W := W) (a := 0) (n := 16) (d := 200) (k := 56) (.inl (by decide)) (by decide) (by decide)
    · simpa using Lay.w_w (W := W) (a := 0) (n := 16) (d := 256) (k := 2320) (.inl (by decide)) (by decide)
        (by decide)
    · exact (L.stk_w.sub_right (Region.sub_prefix (by decide))).symm
  · simp only [List.mem_singleton] at hr'; subst hr'
    exact hD.sub_right hsub

/-- `vg_aes_siv_decrypt`: the plaintext and 1 if the IV at `T` is right,
zeros and 0 if not. -/
theorem decrypt_wp (v : Ctr32Impl) {C W SP A D T : BitVec 32} {R N n : Nat} {s : State}
    (h : EPre C W SP A D T R N n s) :
    WP isa (decrypt v.callee v.suffix) s fun s' => abiPreserved s s' ∧
      match Spec.Siv.decryptWith (Spec.Siv.ctxMac s.mem (w64 C) R) (Spec.Siv.ctxCiph s.mem (w64 C) R)
          (Spec.Siv.components 32 s.mem (w64 A) N) (bytesAt s.mem (w64 T) 16) (bytesAt s.mem (w64 D) n) with
      | some pt => s'.gpr .eax = 1 ∧ bytesAt s'.mem (w64 D) n = pt
      | none => s'.gpr .eax = 0 ∧ bytesAt s'.mem (w64 D) n = Spec.Siv.zeros n := by
  have L := h.ads.lay
  have hR := h.ads.rounds
  have hRb := VG.Proof.AesSiv.X86.rounds_le hR
  have hDw : (⟨w64 D, n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 128, 2448⟩ :=
    h.data.buf.w.sub_right (Lay.wSub (by decide))
  have hW16 : (⟨w64 W, 16⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 128, 2448⟩ := by
    simpa using Lay.w_w (W := W) (a := 0) (n := 16) (.inl (by decide)) (by decide) (by decide)
  have dDW : (⟨w64 W, 16⟩ : Region).Disjoint ⟨w64 D, n⟩ :=
    (h.data.buf.w.sub_right (Region.sub_prefix (by decide))).symm
  have hext1 : ∀ r ∈ [(⟨w64 W, 16⟩ : Region)], r.Disjoint ⟨w64 W + BitVec.ofNat 64 128, 2448⟩ := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hW16
  have hext2 : ∀ r ∈ [(⟨w64 W, 16⟩ : Region), ⟨w64 D, n⟩], r.Disjoint ⟨w64 W + BitVec.ofNat 64 128, 2448⟩ :=
    fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hW16
      · exact hDw
  refine WP.seq (WP.mono (encS2v_ok v h) fun s₀ O => ?_)
  have K₀ := O.kept
  -- The received IV copied from `siv`.
  have hs6 := argA_sub (SP := SP) (n := 8) (i := 6) (by decide) h.fa
  have v6 : s₀.mem.readW (argA SP 6) 32 = T := by
    rw [K₀.big.readW (r := ⟨argA SP 6, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.append_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl
      · exact (h.aw.sub_left hs6).sub_right (Lay.wSub (by decide))
      · exact h.as.symm.sub_left hs6) (by decide), ← h.a6, arg, argAddr, h.sp]
  have i6 : InRegions (s₀.rd ++ s₀.wr) (argA SP 6) 4 := by
    rw [K₀.rd, K₀.wr]; exact h.rA _ _ ⟨_, List.mem_singleton_self _, argA_contains (by decide) h.fa⟩
  refine WP.seq (WP.mono (sivIn_ok L K₀.env i6 v6 (by rw [K₀.rd, K₀.wr]; exact h.t_rd) h.tfit)
    fun s₁ ⟨iv₁, fIn, bp₁, sp₁, rd₁, wr₁⟩ => ?_)
  have K₁ : Kept s C W SP R D n [⟨w64 W, 16⟩] s₁ := (K₀.widen _).step L hext1
    ⟨bp₁, sp₁, K₀.env.perm.of_eq rd₁ wr₁⟩ rd₁ wr₁ fIn (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact .inr ⟨⟨w64 W, 16⟩, by simp, Offset.sub_base (k := 16) _ (by decide)⟩)
  have ivT : bytesAt s₁.mem (w64 W) 16 = bytesAt s.mem (w64 T) 16 := by
    rw [BitVec.add_zero, BitVec.add_zero] at iv₁
    rw [iv₁]
    exact K₀.bytes h.t_w h.t_stk (by simp) (by decide)
  -- CTR from the IV.
  obtain ⟨s₂, run₂, m₂, bp₂, sp₂, rd₂, wr₂⟩ := VG.Proof.AesSiv.X86.counter_ok L K₁.env
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have E₂ : VG.Proof.AesSiv.X86.Env C W SP s₂ := ⟨bp₂, sp₂, K₁.env.perm.of_eq rd₂ wr₂⟩
  have f₂ : Frame [⟨w64 W + BitVec.ofNat 64 cbOff, 16⟩] s₁.mem s₂.mem := by
    rw [m₂]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  have K₂ : Kept s C W SP R D n [⟨w64 W, 16⟩] s₂ := K₁.step L hext1 E₂ rd₂ wr₂ f₂ counter_wR
  have hq : bytesAt s₂.mem (w64 W + BitVec.ofNat 64 cbOff) 16 = Spec.Siv.counter (bytesAt s₁.mem (w64 W) 16) := by
    rw [m₂]; exact VG.Proof.AesSiv.X86.counter_bytes _ _
  refine WP.seq (WP.mono (VG.Proof.AesSiv.X86.ctr_ok v L hR E₂ (h.data.of_eq K₂.rd K₂.wr) h.n32 K₂.slots.ctx K₂.slots.rounds
    K₂.slots.data K₂.slots.len hq (counter_low _)) fun s₃ ⟨E₃, rd₃, wr₃, f₃, d₃⟩ => ?_)
  have K₃ : Kept s C W SP R D n [⟨w64 W, 16⟩, ⟨w64 D, n⟩] s₃ :=
    (K₂.widen _).step L hext2 E₃ rd₃ wr₃ f₃ (ctrR_wR (by simp))
  -- S2V's end with the plaintext into `W + 112`.
  obtain ⟨s₄, run₄, P₄, K₄, f₄⟩ := dataStr_pre L K₃ hext2 (h.data.buf.of_eq K₃.rd K₃.wr) h.n32
  refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
  refine WP.seq (WP.mono (finish_ok v L hR P₄ (out := tOff) (.inr rfl)) fun s₅ F => ?_)
  have K₅ : Kept s C W SP R D n [⟨w64 W, 16⟩, ⟨w64 D, n⟩] s₅ :=
    K₄.step L hext2 F.env F.rd F.wr F.frame (finR_wR (.inr rfl))
  -- The comparison.
  obtain ⟨s₆, run₆, m₆, g₆, rd₆, wr₆⟩ := VG.Proof.AesSiv.X86.compare_ok L F.env
  refine WP.seq (WP.of_runBlock ⟨s₆, run₆, ?_⟩)
  have E₆ : VG.Proof.AesSiv.X86.Env C W SP s₆ := F.env.keep (g₆ _ (by decide) (by decide)) (g₆ _ (by decide) (by decide)) rd₆ wr₆
  have f₆ : Frame [⟨w64 W + BitVec.ofNat 64 okO, 4⟩] s₅.mem s₆.mem := by
    rw [m₆]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have K₆ : Kept s C W SP R D n [⟨w64 W, 16⟩, ⟨w64 D, n⟩] s₆ := K₅.step L hext2 E₆ rd₆ wr₆ f₆ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact .inl ⟨VG.Proof.AesSiv.X86.wS W, by simp, VG.Proof.AesSiv.X86.sub_wS (by decide) (by decide)⟩
  have hok : slotv s₆.mem W okO = VG.Proof.AesSiv.X86.okVal s₅.mem W := by rw [m₆]; exact Mem.readW_writeW_self32 _ _ _
  rw [VG.Proof.AesSiv.X86.okVal_eq] at hok
  -- The mask.
  refine WP.seq (WP.mono (VG.Proof.AesSiv.X86.mask_ok L E₆ K₆.slots.data K₆.slots.len h.n32 (h.data.buf.of_eq K₆.rd K₆.wr)
    (by rw [K₆.wr]; exact h.data.wr) hok) fun s₇ ⟨E₇, rd₇, wr₇, m₇⟩ => ?_)
  have f₇ : Frame [⟨w64 D, n⟩] s₆.mem s₇.mem := by
    rw [m₇]; exact writeBytes_frame _ _ _ (by rw [length_mask]; exact Region.contains_self _ _)
  have K₇ : Kept s C W SP R D n [⟨w64 W, 16⟩, ⟨w64 D, n⟩] s₇ := K₆.step L hext2 E₇ rd₇ wr₇ f₇ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact .inr ⟨_, by simp, fun _ h => h⟩
  -- The result, and the exit.
  rw [WP.block_append_iff]
  obtain ⟨s₈, run₈, ax₈, g₈, m₈, rd₈, wr₈⟩ := VG.Proof.AesSiv.X86.retEax_ok L E₇
  refine WP.of_runBlock ⟨s₈, run₈, ?_⟩
  have K₈ : Kept s C W SP R D n [⟨w64 W, 16⟩, ⟨w64 D, n⟩] s₈ :=
    K₇.step L hext2 (E₇.keep (g₈ _ (by decide)) (g₈ _ (by decide)) rd₈ wr₈) rd₈ wr₈ (rs := [])
      (by rw [m₈]; exact Frame.refl _ _) (fun r hr => by simp at hr)
  have hret : s₈.mem.readW (w64 (s.gpr .esp)) 32 = s.mem.readW (w64 (s.gpr .esp)) 32 := by
    rw [h.sp]
    exact K₈.big.readW (r := ⟨w64 SP, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact h.ret.sub_right (Lay.wSub (by decide))
      · exact ret_below L.sp
      · exact h.ret.sub_right (Region.sub_prefix (by decide))
      · exact h.retD) (by decide)
  refine WP.mono (exit_ok K₈.env.ebp (by rw [K₈.env.esp, h.sp]) (covers_left (fun a m ⟨r, hr, hc⟩ => by
      simp only [List.mem_singleton] at hr; subst hr
      exact K₈.env.perm.w a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩))
    (by have := L.fw; omega) K₈.saved hret) fun s₉ ⟨ab, m₉, ax₉, _, _⟩ => ⟨ab, ?_⟩
  -- The values.
  have iv₅ : bytesAt s₅.mem (w64 W) 16 = bytesAt s.mem (w64 T) 16 := by
    rw [Proof.AesGcm.X86.bytesAt_frame F.frame (w16_dis L dDW (finR_wR (.inr rfl))) (by decide),
      Proof.AesGcm.X86.bytesAt_frame f₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        simpa using Lay.w_w (W := W) (a := 0) (n := 16) (d := strO) (k := 8) (.inl (by decide)) (by decide)
          (by decide)) (by decide),
      Proof.AesGcm.X86.bytesAt_frame f₃ (w16_dis L dDW (ctrR_wR (by simp))) (by decide),
      Proof.AesGcm.X86.bytesAt_frame f₂ (w16_dis L dDW counter_wR) (by decide), ivT]
  have dc : ∀ r ∈ [(⟨w64 W, 16⟩ : Region), ⟨w64 D, n⟩], (⟨w64 C, 512⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact L.c_w.sub_right (Region.sub_prefix (by decide))
    · exact h.data.c
  have mac₄ : Spec.Siv.ctxMac s₄.mem (w64 C) R = Spec.Siv.ctxMac s.mem (w64 C) R := K₄.mac L hR dc
  have ciph₂ : Spec.Siv.ctxCiph s₂.mem (w64 C) R = Spec.Siv.ctxCiph s.mem (w64 C) R :=
    ctxCiph_frame K₂.big (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact L.c_w.sub_right (Lay.wSub (by decide))
      · exact L.stk_c.symm
      · exact L.c_w.sub_right (Region.sub_prefix (by decide))) hRb
  have p₂ : bytesAt s₂.mem (w64 D) n = bytesAt s.mem (w64 D) n :=
    K₂.bytes h.data.buf.w h.data.buf.stk (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dDW.symm) (by have := h.data.buf.lt; omega)
  -- `D`, from `encS2v` to `finish`.
  have dD : ∀ {rs : List Region}, (∀ r ∈ rs, (⟨w64 W + BitVec.ofNat 64 dOff, 16⟩ : Region).Disjoint r) →
      ∀ {m m' : Mem}, Frame rs m m' →
      bytesAt m' (w64 W + BitVec.ofNat 64 dOff) 16 = bytesAt m (w64 W + BitVec.ofNat 64 dOff) 16 :=
    fun hd _ _ hf => Proof.AesGcm.X86.bytesAt_frame hf hd (by decide)
  have acc₄ : bytesAt s₄.mem (w64 W + BitVec.ofNat 64 dOff) 16 =
      Spec.Siv.s2vAcc (Spec.Siv.ctxMac s.mem (w64 C) R) (Spec.Siv.components 32 s.mem (w64 A) N) := by
    rw [dD (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by decide)) (by decide) (by decide)) f₄,
      dD (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
        · exact (L.stk_w' (by decide)).symm
        · exact (h.data.buf.w.sub_right (Lay.wSub (by decide))).symm) f₃,
      dD (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by decide)) (by decide) (by decide)) f₂,
      dD (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by decide)) (by decide) (by decide))
        fIn, O.acc]
  have pt₄ : bytesAt s₄.mem (w64 D) n = bytesAt s₃.mem (w64 D) n :=
    Proof.AesGcm.X86.bytesAt_frame f₄ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.data.buf.w.sub_right (Lay.wSub (by decide)))
      (by have := h.data.buf.lt; omega)
  have o₅ := F.out
  rw [mac₄, acc₄, pt₄] at o₅
  have pt₃ := d₃
  rw [ciph₂, p₂, ivT] at pt₃
  -- The plaintext through the comparison.
  have pt₆ : bytesAt s₆.mem (w64 D) n = bytesAt s₃.mem (w64 D) n := by
    rw [Proof.AesGcm.X86.bytesAt_frame f₆ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact h.data.buf.w.sub_right (Lay.wSub (by decide)))
        (by have := h.data.buf.lt; omega)]
    exact Proof.AesGcm.X86.bytesAt_frame F.frame (fun r hr => (VG.Proof.AesSiv.X86.finR_buf h.data.buf (.inr rfl) r hr))
      (by have := h.data.buf.lt; omega) |>.trans pt₄
  have hlm := VG.Proof.AesSiv.X86.length_mask s₆.mem (w64 D) (decide (bytesAt s₅.mem (w64 W) 16 =
    bytesAt s₅.mem (w64 W + BitVec.ofNat 64 tOff) 16)) n
  have out₇ : bytesAt s₇.mem (w64 D) n = if decide (bytesAt s₅.mem (w64 W) 16 =
      bytesAt s₅.mem (w64 W + BitVec.ofNat 64 tOff) 16) then bytesAt s₆.mem (w64 D) n else Spec.Siv.zeros n := by
    rw [m₇]
    have := Proof.AesGcm.X86.bytesAt_writeBytes_self s₆.mem (w64 D) _ (by rw [hlm]; have := h.data.buf.lt; omega)
    rw [hlm] at this
    exact this
  have ok₇ : slotv s₇.mem W okO = slotv s₆.mem W okO :=
    f₇.readW (r := ⟨w64 W + BitVec.ofNat 64 okO, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.data.buf.w.sub_right (Lay.wSub (by decide))).symm) (by decide)
  have eax₉ : s₉.gpr .eax = if decide (bytesAt s₅.mem (w64 W) 16 =
      bytesAt s₅.mem (w64 W + BitVec.ofNat 64 tOff) 16) then 1 else 0 := by
    rw [ax₉, ax₈, ok₇, hok]
  rw [Spec.Siv.decryptWith_eq, Spec.Siv.openWith, ← pt₃]
  rw [m₉, m₈, out₇, eax₉, iv₅, o₅, pt₆]
  by_cases hc : Spec.Siv.s2vFinish (Spec.Siv.ctxMac s.mem (w64 C) R)
      (Spec.Siv.s2vAcc (Spec.Siv.ctxMac s.mem (w64 C) R) (Spec.Siv.components 32 s.mem (w64 A) N))
      (bytesAt s₃.mem (w64 D) n) = bytesAt s.mem (w64 T) 16
  · simp only [hc, ↓reduceIte, decide_true]
    exact ⟨trivial, trivial⟩
  · have hc' : ¬ bytesAt s.mem (w64 T) 16 = Spec.Siv.s2vFinish (Spec.Siv.ctxMac s.mem (w64 C) R)
        (Spec.Siv.s2vAcc (Spec.Siv.ctxMac s.mem (w64 C) R) (Spec.Siv.components 32 s.mem (w64 A) N))
        (bytesAt s₃.mem (w64 D) n) := fun e => hc e.symm
    simp only [hc, hc', ↓reduceIte, decide_false]
    exact ⟨rfl, rfl⟩

end VG.Proof.AesSiv.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.X86.EncCT`. -/
section

/-!
# AES-SIV on x86: `encrypt` and `decrypt` are constant time

Untrusted: everything here is checked by Lean. Two runs with the same
public arguments and the same descriptors of the components (`ETop`) leak
the same. The entry's block reads the stack arguments, which are public;
between the pieces, the correctness lemmas give each run the next piece's
invariant (from `Kept` since the entry); `decrypt` compares the IVs and
masks the data without a branch, so nothing it does depends on the result.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesSiv.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot restore)
open VG.Proof.AesGcm.X86 (CT w64 slotv argA argsR argA_contains and_self_beq32)

/-- The entry, with the components' addresses and lengths `ca`, `cl`. -/
structure ETop (C W SP A D T : BitVec 32) (R N n : Nat) (ca : Nat → BitVec 32) (cl : Nat → Nat) (s : State) :
    Prop where
  pre : EPre C W SP A D T R N n s
  comps : ∀ j < N, compA s.mem A j = ca j ∧ compL s.mem A j = cl j

theorem sivEntry_ct {I : State → Prop} {W SP : BitVec 32}
    (h : ∀ s, I s → s.gpr .esp = SP ∧ arg s 7 = W ∧ Covers [argsR SP 8] (s.rd ++ s.wr) ∧
      SP.toNat + 4 + 4 * 8 ≤ 2 ^ 32) : CT I sivEntry := by
  refine CT.seq (J := fun s => s.gpr .eax = W ∧ s.gpr .esp = SP)
    (CT.taint [.esp] (VG.Proof.AesSiv.X86.pin1 fun s h' => (h s h').1) (by taint_decide)) (fun s hs => ?_)
    (CT.taint [.eax, .esp] (VG.Proof.AesSiv.X86.pin2 fun _ h => h) (by taint_decide))
  obtain ⟨hSP, hW, rA, fa⟩ := h s hs
  have i₀ : InRegions (s.rd ++ s.wr) (argA SP 7) 4 := rA _ _ ⟨_, List.mem_singleton_self _, argA_contains (by decide) fa⟩
  refine WP.of_runBlock ⟨_, by crun [hSP, i₀], ?_, ?_⟩
  · rw [gpr_setReg_self, ← hSP]; exact hW
  · rw [gpr_setReg_of_ne _ _ (by decide), hSP]

theorem dataStr_ct {I : State → Prop} {W : BitVec 32} (h : ∀ s, I s → s.gpr .ebp = W) :
    CT I (.block [.mov .eax (slot dataO), .store (at_ .ebp strO) .eax, .mov .eax (slot lenO),
      .store (at_ .ebp slenO) .eax]) :=
  CT.taint [.ebp] (VG.Proof.AesSiv.X86.pin_ebp h) (by taint_decide)

/-- `encS2v` is constant time. -/
theorem encS2v_ct (v : Ctr32Impl) {C W SP A D T : BitVec 32} {R N n : Nat} {ca : Nat → BitVec 32} {cl : Nat → Nat}
    (L : Lay C W SP) (hR : R = 10 ∨ R = 12 ∨ R = 14) (hN : N < 2 ^ 32) (hcl : ∀ j < N, cl j < 2 ^ 32) :
    CT (ETop C W SP A D T R N n ca cl) (encS2v v.callee v.suffix) := by
  refine CT.seq (J := fun s₁ => ∃ s, ETop C W SP A D T R N n ca cl s ∧ Entered s W s₁)
    (sivEntry_ct fun s hs => ⟨hs.pre.sp, hs.pre.a7, hs.pre.rA, hs.pre.fa⟩)
    (fun s hs => WP.mono (entry_wp hs.pre) fun s₁ en => ⟨s, hs, en⟩) ?_
  refine CT.seq (J := fun s₂ => ∃ s, ETop C W SP A D T R N n ca cl s ∧ AInv s C W SP A R N D n 0 s₂)
    ((start_ct v L hR).mono fun s₁ ⟨s, hs, en⟩ =>
      let K := (kept_of_entered hs.pre en).1
      ⟨K.env, K.slots.ctx, K.slots.rounds⟩)
    (fun s₁ ⟨s, hs, en⟩ => WP.mono (start_wp v hs.pre en) fun s₂ I => ⟨s, hs, I⟩) ?_
  refine CT.seq (J := fun s₃ => ∃ s, ETop C W SP A D T R N n ca cl s ∧ AInv s C W SP A R N D n N s₃)
    ((s2vAds_ct v L hR hN hcl).mono fun s₂ ⟨s, hs, I⟩ => ⟨s, D, n, hs.pre.ads, hs.comps, I⟩)
    (fun s₂ ⟨s, hs, I⟩ => WP.mono (s2vAds_ok v hs.pre.ads I) fun s₃ I' => ⟨s, hs, I'⟩) ?_
  exact dataStr_ct fun s₃ ⟨_, _, I⟩ => I.kept.env.ebp

/-- After `encS2v`. -/
abbrev EOut (C W SP A D T : BitVec 32) (R N n : Nat) (ca : Nat → BitVec 32) (cl : Nat → Nat) (s : State) : Prop :=
  ∃ s₀, ETop C W SP A D T R N n ca cl s₀ ∧ S2vOut C W SP A D R N n s₀ s

theorem encS2v_wp (v : Ctr32Impl) {C W SP A D T : BitVec 32} {R N n : Nat} {ca : Nat → BitVec 32} {cl : Nat → Nat}
    {s : State} (h : ETop C W SP A D T R N n ca cl s) :
    WP isa (encS2v v.callee v.suffix) s (EOut C W SP A D T R N n ca cl) :=
  WP.mono (encS2v_ok v h.pre) fun _ O => ⟨s, h, O⟩

/-- The pieces after `encS2v`: `Kept` since an entry, with the regions
`ext`. -/
abbrev EKept (C W SP A D T : BitVec 32) (R N n : Nat) (ca : Nat → BitVec 32) (cl : Nat → Nat) (ext : List Region)
    (s : State) : Prop :=
  ∃ s₀, ETop C W SP A D T R N n ca cl s₀ ∧ Kept s₀ C W SP R D n ext s

theorem EKept.ctrPre {C W SP A D T : BitVec 32} {R N n : Nat} {ca : Nat → BitVec 32} {cl : Nat → Nat}
    {ext : List Region} {s : State} (h : EKept C W SP A D T R N n ca cl ext s) : CtrPre C W SP R D n s :=
  let ⟨_, T, K⟩ := h
  ⟨K.env, T.pre.data.of_eq K.rd K.wr, T.pre.n32, K.slots.ctx, K.slots.rounds, K.slots.data, K.slots.len⟩

theorem counter_ct {I : State → Prop} {W : BitVec 32} (h : ∀ s, I s → s.gpr .ebp = W) :
    CT I (.block (counter 0)) :=
  CT.taint [.ebp] (VG.Proof.AesSiv.X86.pin_ebp h) (by taint_decide)

/-- The counter `Q` from the IV, and `Kept`: what CTR starts from. -/
theorem counter_wp {C W SP A D T : BitVec 32} {R N n : Nat} {ca : Nat → BitVec 32} {cl : Nat → Nat}
    {ext : List Region} (hext : ∀ r ∈ ext, r.Disjoint ⟨w64 W + BitVec.ofNat 64 128, 2448⟩) {s : State}
    (h : EKept C W SP A D T R N n ca cl ext s) :
    WP isa (.block (counter 0)) s fun s' => (EKept C W SP A D T R N n ca cl ext s' ∧
      Spec.Siv.beNat (bytesAt s'.mem (w64 W + BitVec.ofNat 64 cbOff) 16) % 2 ^ 32 < 2 ^ 31) ∧ s'.wr = s.wr := by
  obtain ⟨s₀, T, K⟩ := h
  have L := T.pre.ads.lay
  obtain ⟨s₃, run₃, m₃, bp₃, sp₃, rd₃, wr₃⟩ := VG.Proof.AesSiv.X86.counter_ok L K.env
  have E₃ : VG.Proof.AesSiv.X86.Env C W SP s₃ := ⟨bp₃, sp₃, K.env.perm.of_eq rd₃ wr₃⟩
  have f₃ : Frame [⟨w64 W + BitVec.ofNat 64 cbOff, 16⟩] s.mem s₃.mem := by
    rw [m₃]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  refine WP.of_runBlock ⟨s₃, run₃, ⟨⟨s₀, T, K.step L hext E₃ rd₃ wr₃ f₃ counter_wR⟩, ?_⟩, wr₃⟩
  rw [m₃, counter_bytes]
  exact counter_low _

/-- `sivOut` is constant time: `siv`'s address, the stack argument 6, is the
same in both runs. -/
theorem sivOut_ct {C W SP T : BitVec 32} (L : Lay C W SP) {I : State → Prop}
    (h : ∀ s, I s → Env C W SP s ∧ s.mem.readW (argA SP 6) 32 = T ∧ InRegions (s.rd ++ s.wr) (argA SP 6) 4) :
    CT I sivOut := by
  refine CT.seq (J := fun s => s.gpr .edi = T)
    (CT.taint [.ebp, .esp] (pin2 fun s hs => ⟨(h s hs).1.ebp, (h s hs).1.esp⟩) (by taint_decide))
    (fun s hs => ?_) (CT.taint [.edi] (pin1 fun _ h => h) (by taint_decide))
  obtain ⟨E, hv, hin⟩ := h s hs
  exact WP.of_runBlock ⟨_, by crun [E.ebp, E.esp, L.aW, E.perm.wR, hin, hv], by cregs []⟩

/-- `sivIn` is constant time: `siv`'s address, the stack argument 6, is the
same in both runs. -/
theorem sivIn_ct {C W SP T : BitVec 32} {I : State → Prop}
    (h : ∀ s, I s → Env C W SP s ∧ s.mem.readW (argA SP 6) 32 = T ∧ InRegions (s.rd ++ s.wr) (argA SP 6) 4) :
    CT I sivIn := by
  refine CT.seq (J := fun s => s.gpr .edi = T ∧ s.gpr .ebp = W)
    (CT.taint [.esp] (pin1 fun s hs => (h s hs).1.esp) (by taint_decide))
    (fun s hs => ?_) (CT.taint [.edi, .ebp] (pin2 fun _ h => h) (by taint_decide))
  obtain ⟨E, hv, hin⟩ := h s hs
  exact WP.of_runBlock ⟨_, by crun [E.esp, hin, hv], by cregs [], by cregs [E.ebp]⟩

/-- `vg_aes_siv_encrypt` is constant time, with `siv` writable. -/
theorem encrypt_top_ct (v : Ctr32Impl) {C W SP A D T : BitVec 32} {R N n : Nat} {ca : Nat → BitVec 32}
    {cl : Nat → Nat} (z : State) (Tz : ETop C W SP A D T R N n ca cl z) :
    CT (fun s => ETop C W SP A D T R N n ca cl s ∧ Covers [⟨w64 T, 16⟩] s.wr) (encrypt v.callee v.suffix) := by
  have L := Tz.pre.ads.lay
  have hR := Tz.pre.ads.rounds
  have hcl : ∀ j < N, cl j < 2 ^ 32 := fun j hj => by rw [← (Tz.comps j hj).2]; exact BitVec.isLt _
  have hW16 : (⟨w64 W, 16⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 128, 2448⟩ := by
    simpa using Lay.w_w (W := W) (a := 0) (n := 16) (.inl (by decide)) (by decide) (by decide)
  have hext : ∀ r ∈ [(⟨w64 W, 16⟩ : Region)], r.Disjoint ⟨w64 W + BitVec.ofNat 64 128, 2448⟩ := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hW16
  have hDw : (⟨w64 D, n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 128, 2448⟩ :=
    Tz.pre.data.buf.w.sub_right (Lay.wSub (by decide))
  have hext2 : ∀ r ∈ [(⟨w64 W, 16⟩ : Region), ⟨w64 D, n⟩], r.Disjoint ⟨w64 W + BitVec.ofNat 64 128, 2448⟩ :=
    fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hW16
      · exact hDw
  refine CT.seq (J := fun s => EOut C W SP A D T R N n ca cl s ∧ Covers [⟨w64 T, 16⟩] s.wr)
    ((encS2v_ct v L hR Tz.pre.ads.N32 hcl).mono fun s h => h.1)
    (fun s hs => WP.mono (encS2v_ok v hs.1.pre) fun s' O => ⟨⟨s, hs.1, O⟩, by rw [O.kept.wr]; exact hs.2⟩) ?_
  refine CT.seq (J := fun s => EKept C W SP A D T R N n ca cl [⟨w64 W, 16⟩] s ∧ Covers [⟨w64 T, 16⟩] s.wr)
    ((finish_ct v L hR Tz.pre.n32 (.inl rfl)).mono fun s ⟨⟨_, _, O⟩, _⟩ => O.pre)
    (fun s ⟨⟨s₀, T₀, O⟩, hc⟩ => WP.mono (finish_ok v L hR O.pre (out := 0) (.inl rfl)) fun s₂ F =>
      ⟨⟨s₀, T₀, (O.kept.widen _).step L (fun r hr => by
        simp only [List.nil_append, List.mem_singleton] at hr; subst hr; exact hW16)
        F.env F.rd F.wr F.frame (finR_wR (.inl ⟨rfl, by simp⟩))⟩, by rw [F.wr]; exact hc⟩) ?_
  refine CT.seq (J := fun s => (EKept C W SP A D T R N n ca cl [⟨w64 W, 16⟩] s ∧
      Spec.Siv.beNat (bytesAt s.mem (w64 W + BitVec.ofNat 64 cbOff) 16) % 2 ^ 32 < 2 ^ 31) ∧
      Covers [⟨w64 T, 16⟩] s.wr)
    (counter_ct fun s ⟨⟨_, _, K⟩, _⟩ => K.env.ebp)
    (fun s hs => WP.mono (counter_wp hext hs.1) fun s' ⟨p, e⟩ => ⟨p, by rw [e]; exact hs.2⟩) ?_
  refine CT.seq (J := fun s => EKept C W SP A D T R N n ca cl [⟨w64 W, 16⟩, ⟨w64 D, n⟩] s ∧
      Covers [⟨w64 T, 16⟩] s.wr)
    ((ctr_ct v L hR).mono fun s ⟨⟨h, low⟩, _⟩ => ⟨h.ctrPre, low⟩)
    (fun s ⟨⟨⟨s₀, T₀, K⟩, low⟩, hc⟩ =>
      let P := (show EKept C W SP A D T R N n ca cl [⟨w64 W, 16⟩] s from ⟨s₀, T₀, K⟩).ctrPre
      WP.mono (ctr_ok v L hR P.env P.dat P.n32 P.ctx P.rounds P.data P.len rfl low)
        fun _ ⟨E, rd, wr, f, _⟩ => ⟨⟨s₀, T₀, (K.widen _).step L hext2 E rd wr f (ctrR_wR (by simp))⟩,
          by rw [wr]; exact hc⟩) ?_
  have arg6 : ∀ s, EKept C W SP A D T R N n ca cl [⟨w64 W, 16⟩, ⟨w64 D, n⟩] s →
      s.mem.readW (argA SP 6) 32 = T ∧ InRegions (s.rd ++ s.wr) (argA SP 6) 4 := fun s ⟨_, T₀, K⟩ =>
    Kept.arg6 T₀.pre K fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact T₀.pre.aw.sub_right (Region.sub_prefix (by decide))
      · exact T₀.pre.ad
  refine CT.seq (J := fun s => s.gpr .ebp = W)
    (sivOut_ct L fun s hs => ⟨(match hs.1 with | ⟨_, _, K⟩ => K.env), arg6 s hs.1⟩) ?_ ?_
  · intro s ⟨⟨s₀, T₀, K⟩, hc⟩
    obtain ⟨v6, i6⟩ := arg6 s ⟨s₀, T₀, K⟩
    exact WP.mono (sivOut_ok L K.env i6 v6 hc T₀.pre.tfit) fun _ ⟨_, _, bp, _⟩ => bp
  exact CT.taint [.ebp] (pin_ebp fun _ h => h) (by taint_decide)

/-! ## `decrypt` -/

theorem maskTest_ok {C W SP : BitVec 32} {s : State} (L : VG.Proof.AesSiv.X86.Lay C W SP) (E : VG.Proof.AesSiv.X86.Env C W SP s) {n : Nat}
    (hlen : slotv s.mem W lenO = BitVec.ofNat 32 n) (hn32 : n < 2 ^ 32) :
    ∃ s₁, runBlock isa [.mov .ecx (slot lenO), .alu .test .ecx (.reg .ecx)] s = some s₁ ∧ s₁.mem = s.mem ∧
      s₁.gpr .ecx = BitVec.ofNat 32 n ∧ s₁.zf = some (decide (n = 0)) ∧ s₁.gpr .ebp = W ∧ s₁.gpr .esp = SP ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  refine ⟨_, by crun [E.ebp, L.aW, E.perm.wR, hlen], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · cregs [hlen]
  · cmems [hlen]; rw [and_self_beq32 hn32]
  · cregs [E.ebp]
  · cregs [E.esp]
  all_goals cmems []

theorem maskArgs_ok {C W SP : BitVec 32} {s₁ : State} (L : VG.Proof.AesSiv.X86.Lay C W SP) (E₁ : VG.Proof.AesSiv.X86.Env C W SP s₁) {D : BitVec 32} {n : Nat}
    (hd₁ : slotv s₁.mem W dataO = D) (cx₁ : s₁.gpr .ecx = BitVec.ofNat 32 n) :
    ∃ s₂, runBlock isa [.mov .ebx (imm 0), .alu .sub .ebx (slot okO), .mov .edi (slot dataO)] s₁ = some s₂ ∧
      s₂.gpr .edi = D ∧ s₂.gpr .ecx = BitVec.ofNat 32 n := by
  refine ⟨_, by crun [E₁.ebp, L.aW, E₁.perm.wR, hd₁], ?_, ?_⟩
  · cregs [hd₁]
  · cregs [cx₁]

theorem mask_ct {C W SP : BitVec 32} (L : VG.Proof.AesSiv.X86.Lay C W SP) {D : BitVec 32} {n : Nat} (hn32 : n < 2 ^ 32)
    {I : State → Prop}
    (h : ∀ s, I s → VG.Proof.AesSiv.X86.Env C W SP s ∧ slotv s.mem W dataO = D ∧ slotv s.mem W lenO = BitVec.ofNat 32 n) :
    CT I mask := by
  refine CT.block_seq [.ebp] (VG.Proof.AesSiv.X86.pin_ebp fun s hs => (h s hs).1.ebp) (by taint_decide)
    (fun s hs => VG.Proof.AesSiv.X86.maskTest_ok L (h s hs).1 (h s hs).2.2 hn32) ?_
  refine CT.ite (decide (n = 0)) (fun _ ⟨_, _, _, _, hzf, _⟩ => VG.Proof.AesSiv.X86.eval_e hzf) (fun _ => CT.nil) fun _ => ?_
  refine CT.block_seq [.ebp] (VG.Proof.AesSiv.X86.pin_ebp fun _ ⟨_, _, _, _, _, hbp, _⟩ => hbp) (by taint_decide)
    (fun s₁ ⟨s, hs, m₁, cx₁, _, bp₁, sp₁, rd₁, wr₁⟩ => VG.Proof.AesSiv.X86.maskArgs_ok L
      ⟨bp₁, sp₁, (h s hs).1.perm.of_eq rd₁ wr₁⟩ (by rw [m₁]; exact (h s hs).2.1) cx₁) ?_
  exact CT.taint [.edi, .ecx] (VG.Proof.AesSiv.X86.pin2 fun _ ⟨_, _, hdi, hcx⟩ => ⟨hdi, hcx⟩) (by taint_decide)

theorem compare_ct {I : State → Prop} {W : BitVec 32} (h : ∀ s, I s → s.gpr .ebp = W) :
    CT I (.block compare) :=
  CT.taint [.ebp] (VG.Proof.AesSiv.X86.pin_ebp h) (by taint_decide)

/-- `vg_aes_siv_decrypt` is constant time. -/
theorem decrypt_top_ct (v : Ctr32Impl) {C W SP A D T : BitVec 32} {R N n : Nat} {ca : Nat → BitVec 32}
    {cl : Nat → Nat} (z : State) (Tz : ETop C W SP A D T R N n ca cl z) :
    CT (ETop C W SP A D T R N n ca cl) (decrypt v.callee v.suffix) := by
  have L := Tz.pre.ads.lay
  have hR := Tz.pre.ads.rounds
  have hcl : ∀ j < N, cl j < 2 ^ 32 := fun j hj => by rw [← (Tz.comps j hj).2]; exact BitVec.isLt _
  have hDw : (⟨w64 D, n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 128, 2448⟩ :=
    Tz.pre.data.buf.w.sub_right (Lay.wSub (by decide))
  have hW16 : (⟨w64 W, 16⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 128, 2448⟩ := by
    simpa using Lay.w_w (W := W) (a := 0) (n := 16) (.inl (by decide)) (by decide) (by decide)
  have hext1 : ∀ r ∈ [(⟨w64 W, 16⟩ : Region)], r.Disjoint ⟨w64 W + BitVec.ofNat 64 128, 2448⟩ := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hW16
  have hextD : ∀ r ∈ [(⟨w64 W, 16⟩ : Region), ⟨w64 D, n⟩], r.Disjoint ⟨w64 W + BitVec.ofNat 64 128, 2448⟩ :=
    fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hW16
      · exact hDw
  refine CT.seq (J := EOut C W SP A D T R N n ca cl) (encS2v_ct v L hR Tz.pre.ads.N32 hcl)
    (fun s hs => encS2v_wp v hs) ?_
  -- The received IV copied from `siv`.
  have arg6 : ∀ s, EOut C W SP A D T R N n ca cl s →
      s.mem.readW (argA SP 6) 32 = T ∧ InRegions (s.rd ++ s.wr) (argA SP 6) 4 := fun s ⟨_, T₀, O⟩ =>
    Kept.arg6 T₀.pre O.kept (by simp)
  refine CT.seq (J := EKept C W SP A D T R N n ca cl [⟨w64 W, 16⟩])
    (sivIn_ct fun s hs => ⟨(match hs with | ⟨_, _, O⟩ => O.kept.env), arg6 s hs⟩)
    (fun s ⟨s₀, T₀, O⟩ => by
      obtain ⟨v6, i6⟩ := arg6 s ⟨s₀, T₀, O⟩
      exact WP.mono (sivIn_ok L O.kept.env i6 v6 (by rw [O.kept.rd, O.kept.wr]; exact T₀.pre.t_rd) T₀.pre.tfit)
        fun _ ⟨_, fIn, bp, sp, rd, wr⟩ => ⟨s₀, T₀, (O.kept.widen _).step L hext1
          ⟨bp, sp, O.kept.env.perm.of_eq rd wr⟩ rd wr fIn (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact .inr ⟨⟨w64 W, 16⟩, by simp, Offset.sub_base (k := 16) _ (by decide)⟩)⟩) ?_
  -- CTR.
  refine CT.seq (J := fun s => EKept C W SP A D T R N n ca cl [⟨w64 W, 16⟩] s ∧
      Spec.Siv.beNat (bytesAt s.mem (w64 W + BitVec.ofNat 64 cbOff) 16) % 2 ^ 32 < 2 ^ 31)
    (counter_ct fun s ⟨_, _, K⟩ => K.env.ebp)
    (fun s hs => WP.mono (counter_wp hext1 hs) fun _ h => h.1) ?_
  refine CT.seq (J := EKept C W SP A D T R N n ca cl [⟨w64 W, 16⟩, ⟨w64 D, n⟩])
    ((ctr_ct v L hR).mono fun s ⟨h, low⟩ => ⟨h.ctrPre, low⟩)
    (fun s ⟨⟨s₀, T₀, K⟩, low⟩ =>
      let P := (show EKept C W SP A D T R N n ca cl [⟨w64 W, 16⟩] s from ⟨s₀, T₀, K⟩).ctrPre
      WP.mono (ctr_ok v L hR P.env P.dat P.n32 P.ctx P.rounds P.data P.len rfl low)
        fun _ ⟨E, rd, wr, f, _⟩ => ⟨s₀, T₀, (K.widen _).step L hextD E rd wr f (ctrR_wR (by simp))⟩) ?_
  -- S2V's end with the plaintext.
  refine CT.seq (J := fun s => EKept C W SP A D T R N n ca cl [⟨w64 W, 16⟩, ⟨w64 D, n⟩] s ∧ CmacPre C W SP R D n s)
    (dataStr_ct fun s ⟨_, _, K⟩ => K.env.ebp)
    (fun s ⟨s₀, T, K⟩ => by
      obtain ⟨s₄, run₄, P₄, K₄, _⟩ := VG.Proof.AesSiv.X86.dataStr_pre L K hextD (T.pre.data.buf.of_eq K.rd K.wr) T.pre.n32
      exact WP.of_runBlock ⟨s₄, run₄, ⟨s₀, T, K₄⟩, P₄⟩) ?_
  refine CT.seq (J := EKept C W SP A D T R N n ca cl [⟨w64 W, 16⟩, ⟨w64 D, n⟩])
    ((finish_ct v L hR Tz.pre.n32 (.inr rfl)).mono fun s h => h.2)
    (fun s ⟨⟨s₀, T, K⟩, P⟩ => WP.mono (finish_ok v L hR P (out := tOff) (.inr rfl)) fun _ F =>
      ⟨s₀, T, K.step L hextD F.env F.rd F.wr F.frame (finR_wR (.inr rfl))⟩) ?_
  -- The comparison and the mask.
  refine CT.seq (J := fun s => EKept C W SP A D T R N n ca cl [⟨w64 W, 16⟩, ⟨w64 D, n⟩] s ∧
      ∃ c : Bool, slotv s.mem W okO = if c then 1 else 0)
    (VG.Proof.AesSiv.X86.compare_ct fun s ⟨_, _, K⟩ => K.env.ebp)
    (fun s ⟨s₀, T, K⟩ => by
      obtain ⟨s₆, run₆, m₆, g₆, rd₆, wr₆⟩ := VG.Proof.AesSiv.X86.compare_ok L K.env
      have E₆ : VG.Proof.AesSiv.X86.Env C W SP s₆ := K.env.keep (g₆ _ (by decide) (by decide)) (g₆ _ (by decide) (by decide)) rd₆ wr₆
      have f₆ : Frame [⟨w64 W + BitVec.ofNat 64 okO, 4⟩] s.mem s₆.mem := by
        rw [m₆]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
      refine WP.of_runBlock ⟨s₆, run₆, ⟨s₀, T, K.step L hextD E₆ rd₆ wr₆ f₆ fun r hr => ?_⟩,
        decide (bytesAt s.mem (w64 W) 16 = bytesAt s.mem (w64 W + BitVec.ofNat 64 tOff) 16), ?_⟩
      · simp only [List.mem_singleton] at hr; subst hr
        exact .inl ⟨VG.Proof.AesSiv.X86.wS W, by simp, VG.Proof.AesSiv.X86.sub_wS (by decide) (by decide)⟩
      · rw [m₆, ← VG.Proof.AesSiv.X86.okVal_eq]; exact Mem.readW_writeW_self32 _ _ _) ?_
  refine CT.seq (J := fun s => s.gpr .ebp = W)
    (VG.Proof.AesSiv.X86.mask_ct L Tz.pre.n32 fun s ⟨⟨_, _, K⟩, _⟩ => ⟨K.env, K.slots.data, K.slots.len⟩)
    (fun s ⟨⟨s₀, T, K⟩, c, hc⟩ => WP.mono (VG.Proof.AesSiv.X86.mask_ok L K.env K.slots.data K.slots.len T.pre.n32
      (T.pre.data.buf.of_eq K.rd K.wr) (by rw [K.wr]; exact T.pre.data.wr) hc) fun _ ⟨E, _⟩ => E.ebp) ?_
  exact CT.taint [.ebp] (VG.Proof.AesSiv.X86.pin_ebp fun _ h => h) (by taint_decide)

end VG.Proof.AesSiv.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.X86.Init`. -/
section

/-!
# AES-SIV on x86: `vg_aes_siv_init`'s code

Untrusted: everything here is checked by Lean. `initCore` saves the
registers in the scratch buffer (as streaming AES-CMAC's `init`, whose
pieces this reuses), expands `K1` into the context, derives its subkeys
after the schedule, expands `K2` after them and restores the registers: the
context is then that of the key (`Proof.AesSiv.keyRepr_of`). The code
between the calls is constant time by the taint analysis (from `esp` and the
stack arguments), and the calls by their own proofs (`ek_rel`, `sub_rel`),
their arguments pinned by `IMid₁`, `IMid₂` and `IMid₃`.
-/

namespace VG.Proof.AesSiv.X86

open VG VG.X86 VG.Impl.AesSiv.X86
open VG.Impl.CmacAes.Stream.X86 (call4 save restore saved)
open VG.Proof.CmacAes.Stream.X86 (EArgs EPost SArgs SPost ek_call ek_rel sub_call sub_rel savedMem savedMem_frame
  saveMem_slot saved_bound saved_ne_eax save_wp restore_wp arg_sub args_below arg_keep arg_ofNat add_setWidth
  add_toNat arg_contains Pt Pt.refl Pt.agree below_eq ret_below)
open VG.Impl.CmacAes.X86 (argOp)
open VG.Proof.MdStream.X86 (Upd wp_mov wp_addi wp_add wp_shr)
open VG.Proof.CmacAes.X86 (wp_arg)

variable (v : Proof.Aes.X86.Ctr32Impl)

section
variable (s₀ : State)

abbrev iKp : BitVec 32 := VG.X86.arg s₀ 0
abbrev iKL : Nat := (VG.X86.arg s₀ 1).toNat
abbrev iCt : BitVec 32 := VG.X86.arg s₀ 2
abbrev iSc : BitVec 32 := VG.X86.arg s₀ 3
abbrev iE : BitVec 32 := s₀.gpr .esp
abbrev ikR : Region := ⟨(VG.Proof.AesSiv.X86.iKp s₀).setWidth 64, VG.Proof.AesSiv.X86.iKL s₀⟩
abbrev ictR : Region := ⟨(VG.Proof.AesSiv.X86.iCt s₀).setWidth 64, 512⟩
abbrev iscR : Region := ⟨(VG.Proof.AesSiv.X86.iSc s₀).setWidth 64, 2560⟩
abbrev iaR : Region := ⟨argAddr s₀ 0, 16⟩

/-- Where the code writes: the context, the scratch buffer and the stack. -/
abbrev IBig : List Region := [VG.Proof.AesSiv.X86.ictR s₀, VG.Proof.AesSiv.X86.iscR s₀, below (VG.Proof.AesSiv.X86.iE s₀) 48]

end

/-- The precondition, by name. -/
structure IPre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.AesSiv.X86.ikR s₀, VG.Proof.AesSiv.X86.iaR s₀]
  wr : s₀.wr = [VG.Proof.AesSiv.X86.ictR s₀, VG.Proof.AesSiv.X86.iscR s₀]
  k_c : (VG.Proof.AesSiv.X86.ikR s₀).Disjoint (VG.Proof.AesSiv.X86.ictR s₀)
  k_s : (VG.Proof.AesSiv.X86.ikR s₀).Disjoint (VG.Proof.AesSiv.X86.iscR s₀)
  k_a : (VG.Proof.AesSiv.X86.ikR s₀).Disjoint (VG.Proof.AesSiv.X86.iaR s₀)
  c_s : (VG.Proof.AesSiv.X86.ictR s₀).Disjoint (VG.Proof.AesSiv.X86.iscR s₀)
  c_a : (VG.Proof.AesSiv.X86.ictR s₀).Disjoint (VG.Proof.AesSiv.X86.iaR s₀)
  s_a : (VG.Proof.AesSiv.X86.iscR s₀).Disjoint (VG.Proof.AesSiv.X86.iaR s₀)
  ret_k : (⟨(VG.Proof.AesSiv.X86.iE s₀).setWidth 64, 4⟩ : Region).Disjoint (VG.Proof.AesSiv.X86.ikR s₀)
  ret_c : (⟨(VG.Proof.AesSiv.X86.iE s₀).setWidth 64, 4⟩ : Region).Disjoint (VG.Proof.AesSiv.X86.ictR s₀)
  ret_s : (⟨(VG.Proof.AesSiv.X86.iE s₀).setWidth 64, 4⟩ : Region).Disjoint (VG.Proof.AesSiv.X86.iscR s₀)
  ret_a : (⟨(VG.Proof.AesSiv.X86.iE s₀).setWidth 64, 4⟩ : Region).Disjoint (VG.Proof.AesSiv.X86.iaR s₀)
  b_k' : (⟨(VG.Proof.AesSiv.X86.iE s₀).setWidth 64 - BitVec.ofNat 64 48, 48⟩ : Region).Disjoint (VG.Proof.AesSiv.X86.ikR s₀)
  b_c' : (⟨(VG.Proof.AesSiv.X86.iE s₀).setWidth 64 - BitVec.ofNat 64 48, 48⟩ : Region).Disjoint (VG.Proof.AesSiv.X86.ictR s₀)
  b_s' : (⟨(VG.Proof.AesSiv.X86.iE s₀).setWidth 64 - BitVec.ofNat 64 48, 48⟩ : Region).Disjoint (VG.Proof.AesSiv.X86.iscR s₀)
  b_a' : (⟨(VG.Proof.AesSiv.X86.iE s₀).setWidth 64 - BitVec.ofNat 64 48, 48⟩ : Region).Disjoint (VG.Proof.AesSiv.X86.iaR s₀)
  fK : (VG.Proof.AesSiv.X86.iKp s₀).toNat + VG.Proof.AesSiv.X86.iKL s₀ ≤ 2 ^ 32
  fC : (VG.Proof.AesSiv.X86.iCt s₀).toNat + 512 ≤ 2 ^ 32
  fS : (VG.Proof.AesSiv.X86.iSc s₀).toNat + 2560 ≤ 2 ^ 32
  esp48 : 48 ≤ (VG.Proof.AesSiv.X86.iE s₀).toNat
  espfit : (VG.Proof.AesSiv.X86.iE s₀).toNat + 20 ≤ 2 ^ 32
  klen : VG.Proof.AesSiv.X86.iKL s₀ = 32 ∨ VG.Proof.AesSiv.X86.iKL s₀ = 48 ∨ VG.Proof.AesSiv.X86.iKL s₀ = 64

theorem IPre.of {s₀ : State} (h : initX86.pre s₀) : VG.Proof.AesSiv.X86.IPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, w⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, w⟩

namespace IPre
variable {s₀ : State} (hp : VG.Proof.AesSiv.X86.IPre s₀)
include hp

theorem b_k : (below (VG.Proof.AesSiv.X86.iE s₀) 48).Disjoint (VG.Proof.AesSiv.X86.ikR s₀) := by rw [VG.Proof.CmacAes.Stream.X86.below_eq hp.esp48]; exact hp.b_k'
theorem b_c : (below (VG.Proof.AesSiv.X86.iE s₀) 48).Disjoint (VG.Proof.AesSiv.X86.ictR s₀) := by rw [VG.Proof.CmacAes.Stream.X86.below_eq hp.esp48]; exact hp.b_c'
theorem b_s : (below (VG.Proof.AesSiv.X86.iE s₀) 48).Disjoint (VG.Proof.AesSiv.X86.iscR s₀) := by rw [VG.Proof.CmacAes.Stream.X86.below_eq hp.esp48]; exact hp.b_s'

theorem fit : (s₀.gpr .esp).toNat + 4 + 4 * 4 ≤ 2 ^ 32 := by have := hp.espfit; omega

theorem arg_in {i : Nat} (hi : i < 4) : InRegions (s₀.rd ++ s₀.wr) (argAddr s₀ i) 4 :=
  ⟨VG.Proof.AesSiv.X86.iaR s₀, by simp [hp.rd, hp.wr], VG.Proof.CmacAes.Stream.X86.arg_contains hp.fit hi⟩

/-- The stack arguments are unchanged where only `IBig` changes. -/
theorem keep {m : Mem} (hf : Frame (VG.Proof.AesSiv.X86.IBig s₀) s₀.mem m) {i : Nat} (hi : i < 4) :
    m.readW (argAddr s₀ i) 32 = VG.X86.arg s₀ i :=
  arg_keep hf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.c_a.symm.sub_left (VG.Proof.CmacAes.Stream.X86.arg_sub hp.fit hi)
    · exact hp.s_a.symm.sub_left (VG.Proof.CmacAes.Stream.X86.arg_sub hp.fit hi)
    · exact (args_below hp.fit (by decide) hp.esp48).symm.sub_left (VG.Proof.CmacAes.Stream.X86.arg_sub hp.fit hi)

theorem argsOut : ArgsOut 4 s₀ := by
  refine ⟨by have := hp.espfit; omega, ?_⟩
  rw [hp.wr]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact VG.X86.Taint.frame_disjoint (n := 16) (by have := hp.espfit; omega) hp.ret_c hp.c_a.symm
  · exact VG.X86.Taint.frame_disjoint (n := 16) (by have := hp.espfit; omega) hp.ret_s hp.s_a.symm

end IPre

theorem IPre.savedMem_big {s₀ : State} (_hp : VG.Proof.AesSiv.X86.IPre s₀) : Frame (VG.Proof.AesSiv.X86.IBig s₀) s₀.mem (savedMem s₀ (VG.Proof.AesSiv.X86.iSc s₀)) :=
  (savedMem_frame _ _).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨VG.Proof.AesSiv.X86.iscR s₀, by simp, Offset.sub_base _ (by decide)⟩

/-! ## Arithmetic -/

theorem shr_ofNat (x : BitVec 32) (k : Nat) : x >>> k = BitVec.ofNat 32 (x.toNat / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) x.isLt)]

theorem rounds32 {KL : Nat} (h : KL = 32 ∨ KL = 48 ∨ KL = 64) :
    BitVec.ofNat 32 KL >>> 3 + 6 = BitVec.ofNat 32 (KL / 8 + 6) := by
  rcases h with rfl | rfl | rfl <;> decide

/-! ## Before the first call -/

theorem initPre_eq : VG.Impl.AesSiv.X86.initPre = .mov .eax (argOp 3) :: (save ++ ([.mov .eax (argOp 0), .mov .ecx (argOp 1),
    .shift .shr .ecx 1, .mov .edx (argOp 2), .mov .ebx (argOp 3)] : List Instr)) := rfl

/-- What the code before the first call leaves. -/
structure IMid₁ (s₀ s : State) : Prop where
  args : EArgs s (VG.Proof.AesSiv.X86.iKp s₀) (VG.Proof.AesSiv.X86.iCt s₀) (VG.Proof.AesSiv.X86.iSc s₀) (VG.Proof.AesSiv.X86.iKL s₀ / 2)
  esp : s.gpr .esp = VG.Proof.AesSiv.X86.iE s₀
  mem : s.mem = savedMem s₀ (VG.Proof.AesSiv.X86.iSc s₀)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem initPre_wp {s₀ : State} (hp : VG.Proof.AesSiv.X86.IPre s₀) : WP isa (.block VG.Impl.AesSiv.X86.initPre) s₀ (VG.Proof.AesSiv.X86.IMid₁ s₀) := by
  have fS := hp.fS
  have fC := hp.fC
  have fK := hp.fK
  have e48 := hp.esp48
  have kl := hp.klen
  rw [VG.Proof.AesSiv.X86.initPre_eq]
  refine VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀) rfl (hp.arg_in (by decide)) rfl fun s₁ u₁ => ?_
  refine save_wp (Sc := VG.Proof.AesSiv.X86.iSc s₀) u₁.gpr (by omega) (by
      rw [u₁.wr, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.AesSiv.X86.iscR s₀, by simp, 0, by simp, by simp⟩)
    fun s₂ g₂ rd₂ wr₂ m₂ => ?_
  have hm₂ : s₂.mem = savedMem s₀ (VG.Proof.AesSiv.X86.iSc s₀) := by
    rw [m₂, u₁.mem, savedMem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p hp' => u₁.other _ (saved_ne_eax p hp')
  have esp₂ : s₂.gpr .esp = VG.Proof.AesSiv.X86.iE s₀ := by rw [g₂, u₁.other _ (by decide)]
  have rd₂' : s₂.rd = s₀.rd := by rw [rd₂, u₁.rd]
  have wr₂' : s₂.wr = s₀.wr := by rw [wr₂, u₁.wr]
  have av : ∀ i < 4, s₂.mem.readW (argAddr s₀ i) 32 = VG.X86.arg s₀ i := fun i hi => by
    rw [hm₂]; exact hp.keep hp.savedMem_big hi
  refine VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀) esp₂ (by rw [rd₂', wr₂']; exact hp.arg_in (by decide)) (av 0 (by decide))
    fun s₃ u₃ => ?_
  refine VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀) (by rw [u₃.other _ (by decide), esp₂])
    (by rw [u₃.rd, u₃.wr, rd₂', wr₂']; exact hp.arg_in (by decide)) (by rw [u₃.mem]; exact av 1 (by decide))
    fun s₄ u₄ => ?_
  refine wp_shr (by decide) fun s₅ u₅ => ?_
  refine VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀) (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), esp₂])
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, rd₂', wr₂']; exact hp.arg_in (by decide))
    (by rw [u₅.mem, u₄.mem, u₃.mem]; exact av 2 (by decide)) fun s₆ u₆ => ?_
  refine VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀)
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), esp₂])
    (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, rd₂', wr₂']; exact hp.arg_in (by decide))
    (by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem]; exact av 3 (by decide)) fun s₇ u₇ => WP.block_nil ?_
  have esp₇ : s₇.gpr .esp = VG.Proof.AesSiv.X86.iE s₀ := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), esp₂]
  have rd₇ : s₇.rd = s₀.rd := by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂']
  have wr₇ : s₇.wr = s₀.wr := by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂']
  have b20 : Region.Sub (below (VG.Proof.AesSiv.X86.iE s₀) 20) (below (VG.Proof.AesSiv.X86.iE s₀) 48) := VG.X86.below_sub (by decide) e48
  have hk : Region.Sub ⟨(VG.Proof.AesSiv.X86.iKp s₀).setWidth 64, VG.Proof.AesSiv.X86.iKL s₀ / 2⟩ (VG.Proof.AesSiv.X86.ikR s₀) := Region.sub_prefix (by omega)
  refine ⟨?_, esp₇, by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, hm₂], rd₇, wr₇⟩
  exact
  { eax := by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.gpr]
    ecx := by
      rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.gpr, VG.Proof.AesSiv.X86.shr_ofNat]
    edx := by rw [u₇.other _ (by decide), u₆.gpr]
    ebx := u₇.gpr
    klen := by omega
    esp := by rw [esp₇]; omega
    kw := (hp.k_c.sub_left hk).sub_right (Region.sub_prefix (by decide))
    ks := (hp.k_s.sub_left hk).sub_right (Region.sub_prefix (by decide))
    ws := (hp.c_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    bK := by rw [esp₇]; exact (hp.b_k.sub_left b20).sub_right hk
    bW := by rw [esp₇]; exact (hp.b_c.sub_left b20).sub_right (Region.sub_prefix (by decide))
    bS := by rw [esp₇]; exact (hp.b_s.sub_left b20).sub_right (Region.sub_prefix (by decide))
    fK := by omega
    fW := by omega
    fS := by omega
    reads := by
      rw [rd₇, wr₇, hp.rd, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.AesSiv.X86.ikR s₀, by simp, 0, by simp, by simp only [Nat.zero_add]; omega⟩
    writes := by
      rw [wr₇, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨VG.Proof.AesSiv.X86.ictR s₀, by simp, 0, by simp, by simp⟩
      · exact ⟨VG.Proof.AesSiv.X86.iscR s₀, by simp, 0, by simp, by simp⟩ }

/-! ## After a call -/

/-- What is known after each call. -/
structure IAft (s₀ s : State) : Prop where
  esp : s.gpr .esp = VG.Proof.AesSiv.X86.iE s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (VG.Proof.AesSiv.X86.IBig s₀) s₀.mem s.mem

theorem IAft.pt {s₀ s : State} (hp : VG.Proof.AesSiv.X86.IPre s₀) (h : VG.Proof.AesSiv.X86.IAft s₀ s) : Pt 4 s₀ s :=
  ⟨h.esp, h.wr, fun _ hi => hp.keep h.frame hi⟩

theorem IMid₁.after {s₀ s s' : State} (hp : VG.Proof.AesSiv.X86.IPre s₀) (h : VG.Proof.AesSiv.X86.IMid₁ s₀ s)
    (h' : EPost s (VG.Proof.AesSiv.X86.iKp s₀) (VG.Proof.AesSiv.X86.iCt s₀) (VG.Proof.AesSiv.X86.iSc s₀) (VG.Proof.AesSiv.X86.iKL s₀ / 2) s') : VG.Proof.AesSiv.X86.IAft s₀ s' := by
  have fr := h'.frame
  rw [h.esp, h.mem] at fr
  refine ⟨by rw [h'.saved .esp (by simp [calleeSaved]), h.esp], by rw [h'.rd, h.rd], by rw [h'.wr, h.wr],
    hp.savedMem_big.trans (fr.sub fun r hr => ?_)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨VG.Proof.AesSiv.X86.ictR s₀, by simp, Region.sub_prefix (by decide)⟩
  · exact ⟨VG.Proof.AesSiv.X86.iscR s₀, by simp, Region.sub_prefix (by decide)⟩
  · exact ⟨below (VG.Proof.AesSiv.X86.iE s₀) 48, by simp, VG.X86.below_sub (by decide) hp.esp48⟩

/-! ## Between the first two calls -/

/-- What the code between the first two calls leaves. -/
structure IMid₂ (s₀ s : State) : Prop where
  args : SArgs s (VG.Proof.AesSiv.X86.iCt s₀) (VG.Proof.AesSiv.X86.iCt s₀ + BitVec.ofNat 32 240) (VG.Proof.AesSiv.X86.iSc s₀) (VG.Proof.AesSiv.X86.iKL s₀ / 8 + 6)
  aft : VG.Proof.AesSiv.X86.IAft s₀ s

theorem initMid₁_wp {s₀ s : State} (hp : VG.Proof.AesSiv.X86.IPre s₀) (h : VG.Proof.AesSiv.X86.IAft s₀ s) :
    WP isa (.block initMid₁) s fun s' => VG.Proof.AesSiv.X86.IMid₂ s₀ s' ∧ s'.mem = s.mem := by
  have fS := hp.fS
  have fC := hp.fC
  have e48 := hp.esp48
  have rw₀ : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  have av : ∀ i < 4, s.mem.readW (argAddr s₀ i) 32 = VG.X86.arg s₀ i := fun i hi => hp.keep h.frame hi
  refine VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀) h.esp (by rw [rw₀]; exact hp.arg_in (by decide)) (av 2 (by decide)) fun s₁ u₁ => ?_
  refine VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀) (by rw [u₁.other _ (by decide), h.esp])
    (by rw [u₁.rd, u₁.wr, rw₀]; exact hp.arg_in (by decide)) (by rw [u₁.mem]; exact av 1 (by decide))
    fun s₂ u₂ => ?_
  refine wp_shr (by decide) fun s₃ u₃ => wp_addi fun s₄ u₄ => wp_mov fun s₅ u₅ => wp_addi fun s₆ u₆ => ?_
  refine VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀)
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h.esp])
    (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, rw₀]
        exact hp.arg_in (by decide))
    (by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]; exact av 3 (by decide)) fun s₇ u₇ => WP.block_nil ?_
  have esp₇ : s₇.gpr .esp = VG.Proof.AesSiv.X86.iE s₀ := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.esp]
  have m₇ : s₇.mem = s.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have rd₇ : s₇.rd = s₀.rd := by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd]
  have wr₇ : s₇.wr = s₀.wr := by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]
  have kC : Region.Sub ⟨(VG.Proof.AesSiv.X86.iCt s₀ + BitVec.ofNat 32 240).setWidth 64, 32⟩ (VG.Proof.AesSiv.X86.ictR s₀) := by
    rw [add_setWidth (by omega)]; exact Offset.sub_base _ (by decide)
  have hR : VG.Proof.AesSiv.X86.iKL s₀ / 8 + 6 = 10 ∨ VG.Proof.AesSiv.X86.iKL s₀ / 8 + 6 = 12 ∨ VG.Proof.AesSiv.X86.iKL s₀ / 8 + 6 = 14 := by
    rcases hp.klen with h | h | h <;> rw [h] <;> decide
  refine ⟨⟨?_, ⟨esp₇, rd₇, wr₇, by rw [m₇]; exact h.frame⟩⟩, m₇⟩
  exact
  { eax := by
      rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
    ecx := by
      rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.gpr,
        arg_ofNat s₀ 1]
      exact VG.Proof.AesSiv.X86.rounds32 hp.klen
    edx := by
      rw [u₇.other _ (by decide), u₆.gpr, u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.gpr]
    ebx := u₇.gpr
    rounds := hR
    esp := by rw [esp₇]; exact e48
    wk := by
      rw [add_setWidth (by omega)]; exact Offset.base_disjoint _ (by decide) (by omega)
    ws := (hp.c_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    ks := (hp.c_s.sub_left kC).sub_right (Region.sub_prefix (by decide))
    bW := by rw [esp₇]; exact hp.b_c.sub_right (Region.sub_prefix (by decide))
    bK := by rw [esp₇]; exact hp.b_c.sub_right kC
    bS := by rw [esp₇]; exact hp.b_s.sub_right (Region.sub_prefix (by decide))
    fW := by omega
    fK := by rw [add_toNat (by omega)]; omega
    fS := by omega
    reads := by
      rw [rd₇, wr₇, hp.rd, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.AesSiv.X86.ictR s₀, by simp, 0, by simp, by simp⟩
    writes := by
      rw [wr₇, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨VG.Proof.AesSiv.X86.ictR s₀, by simp, 240, add_setWidth (by omega), by simp⟩
      · exact ⟨VG.Proof.AesSiv.X86.iscR s₀, by simp, 0, by simp, by simp⟩ }

theorem IMid₂.after {s₀ s s' : State} (hp : VG.Proof.AesSiv.X86.IPre s₀) (h : VG.Proof.AesSiv.X86.IMid₂ s₀ s)
    (h' : SPost s (VG.Proof.AesSiv.X86.iCt s₀) (VG.Proof.AesSiv.X86.iCt s₀ + BitVec.ofNat 32 240) (VG.Proof.AesSiv.X86.iSc s₀) (VG.Proof.AesSiv.X86.iKL s₀ / 8 + 6) s') : VG.Proof.AesSiv.X86.IAft s₀ s' := by
  have fr := h'.frame
  rw [h.aft.esp] at fr
  have fC := hp.fC
  refine ⟨by rw [h'.saved .esp (by simp [calleeSaved]), h.aft.esp], by rw [h'.rd, h.aft.rd],
    by rw [h'.wr, h.aft.wr], h.aft.frame.trans (fr.sub fun r hr => ?_)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · refine ⟨VG.Proof.AesSiv.X86.ictR s₀, by simp, ?_⟩
    rw [add_setWidth (by omega)]; exact Offset.sub_base _ (by decide)
  · exact ⟨VG.Proof.AesSiv.X86.iscR s₀, by simp, Region.sub_prefix (by decide)⟩
  · exact ⟨below (VG.Proof.AesSiv.X86.iE s₀) 48, by simp, fun _ h => h⟩

/-! ## Between the last two calls -/

/-- What the code between the last two calls leaves. -/
structure IMid₃ (s₀ s : State) : Prop where
  args : EArgs s (VG.Proof.AesSiv.X86.iKp s₀ + BitVec.ofNat 32 (VG.Proof.AesSiv.X86.iKL s₀ / 2)) (VG.Proof.AesSiv.X86.iCt s₀ + BitVec.ofNat 32 272) (VG.Proof.AesSiv.X86.iSc s₀) (VG.Proof.AesSiv.X86.iKL s₀ / 2)
  aft : VG.Proof.AesSiv.X86.IAft s₀ s

theorem initMid₂_wp {s₀ s : State} (hp : VG.Proof.AesSiv.X86.IPre s₀) (h : VG.Proof.AesSiv.X86.IAft s₀ s) :
    WP isa (.block initMid₂) s fun s' => VG.Proof.AesSiv.X86.IMid₃ s₀ s' ∧ s'.mem = s.mem := by
  have fS := hp.fS
  have fC := hp.fC
  have fK := hp.fK
  have e48 := hp.esp48
  have kl := hp.klen
  have rw₀ : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  have av : ∀ i < 4, s.mem.readW (argAddr s₀ i) 32 = VG.X86.arg s₀ i := fun i hi => hp.keep h.frame hi
  refine VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀) h.esp (by rw [rw₀]; exact hp.arg_in (by decide)) (av 1 (by decide)) fun s₁ u₁ => ?_
  refine wp_shr (by decide) fun s₂ u₂ => ?_
  refine VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀) (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h.esp])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, rw₀]; exact hp.arg_in (by decide))
    (by rw [u₂.mem, u₁.mem]; exact av 0 (by decide)) fun s₃ u₃ => ?_
  refine wp_add fun s₄ u₄ => ?_
  refine VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.esp])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, rw₀]; exact hp.arg_in (by decide))
    (by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]; exact av 2 (by decide)) fun s₅ u₅ => ?_
  refine wp_addi fun s₆ u₆ => ?_
  refine VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀)
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h.esp])
    (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, rw₀]
        exact hp.arg_in (by decide))
    (by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]; exact av 3 (by decide)) fun s₇ u₇ => WP.block_nil ?_
  have esp₇ : s₇.gpr .esp = VG.Proof.AesSiv.X86.iE s₀ := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.esp]
  have m₇ : s₇.mem = s.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have rd₇ : s₇.rd = s₀.rd := by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd]
  have wr₇ : s₇.wr = s₀.wr := by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]
  have b20 : Region.Sub (below (VG.Proof.AesSiv.X86.iE s₀) 20) (below (VG.Proof.AesSiv.X86.iE s₀) 48) := VG.X86.below_sub (by decide) e48
  have aK : (VG.Proof.AesSiv.X86.iKp s₀ + BitVec.ofNat 32 (VG.Proof.AesSiv.X86.iKL s₀ / 2)).setWidth 64 =
      (VG.Proof.AesSiv.X86.iKp s₀).setWidth 64 + BitVec.ofNat 64 (VG.Proof.AesSiv.X86.iKL s₀ / 2) := add_setWidth (by omega)
  have aC : (VG.Proof.AesSiv.X86.iCt s₀ + BitVec.ofNat 32 272).setWidth 64 = (VG.Proof.AesSiv.X86.iCt s₀).setWidth 64 + BitVec.ofNat 64 272 :=
    add_setWidth (by omega)
  have hk : Region.Sub ⟨(VG.Proof.AesSiv.X86.iKp s₀ + BitVec.ofNat 32 (VG.Proof.AesSiv.X86.iKL s₀ / 2)).setWidth 64, VG.Proof.AesSiv.X86.iKL s₀ / 2⟩ (VG.Proof.AesSiv.X86.ikR s₀) := by
    rw [aK]; exact Offset.sub_base _ (by omega)
  have hc : Region.Sub ⟨(VG.Proof.AesSiv.X86.iCt s₀ + BitVec.ofNat 32 272).setWidth 64, 240⟩ (VG.Proof.AesSiv.X86.ictR s₀) := by
    rw [aC]; exact Offset.sub_base _ (by decide)
  refine ⟨⟨?_, ⟨esp₇, rd₇, wr₇, by rw [m₇]; exact h.frame⟩⟩, m₇⟩
  exact
  { eax := by
      rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr,
        u₃.other _ (by decide), u₂.gpr, u₁.gpr, VG.Proof.AesSiv.X86.shr_ofNat]
    ecx := by
      rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.gpr, u₁.gpr, VG.Proof.AesSiv.X86.shr_ofNat]
    edx := by rw [u₇.other _ (by decide), u₆.gpr, u₅.gpr]
    ebx := u₇.gpr
    klen := by omega
    esp := by rw [esp₇]; omega
    kw := (hp.k_c.sub_left hk).sub_right hc
    ks := (hp.k_s.sub_left hk).sub_right (Region.sub_prefix (by decide))
    ws := (hp.c_s.sub_left hc).sub_right (Region.sub_prefix (by decide))
    bK := by rw [esp₇]; exact (hp.b_k.sub_left b20).sub_right hk
    bW := by rw [esp₇]; exact (hp.b_c.sub_left b20).sub_right hc
    bS := by rw [esp₇]; exact (hp.b_s.sub_left b20).sub_right (Region.sub_prefix (by decide))
    fK := by rw [add_toNat (by omega)]; omega
    fW := by rw [add_toNat (by omega)]; omega
    fS := by omega
    reads := by
      rw [rd₇, wr₇, hp.rd, hp.wr, aK]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨VG.Proof.AesSiv.X86.ikR s₀, by simp, VG.Proof.AesSiv.X86.iKL s₀ / 2, rfl, by simp only; omega⟩
    writes := by
      rw [wr₇, hp.wr, aC]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨VG.Proof.AesSiv.X86.ictR s₀, by simp, 272, rfl, by simp⟩
      · exact ⟨VG.Proof.AesSiv.X86.iscR s₀, by simp, 0, by simp, by simp⟩ }

theorem IMid₃.after {s₀ s s' : State} (hp : VG.Proof.AesSiv.X86.IPre s₀) (h : VG.Proof.AesSiv.X86.IMid₃ s₀ s)
    (h' : EPost s (VG.Proof.AesSiv.X86.iKp s₀ + BitVec.ofNat 32 (VG.Proof.AesSiv.X86.iKL s₀ / 2)) (VG.Proof.AesSiv.X86.iCt s₀ + BitVec.ofNat 32 272) (VG.Proof.AesSiv.X86.iSc s₀) (VG.Proof.AesSiv.X86.iKL s₀ / 2) s') :
    VG.Proof.AesSiv.X86.IAft s₀ s' := by
  have fr := h'.frame
  rw [h.aft.esp] at fr
  have fC := hp.fC
  refine ⟨by rw [h'.saved .esp (by simp [calleeSaved]), h.aft.esp], by rw [h'.rd, h.aft.rd],
    by rw [h'.wr, h.aft.wr], h.aft.frame.trans (fr.sub fun r hr => ?_)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · refine ⟨VG.Proof.AesSiv.X86.ictR s₀, by simp, ?_⟩
    rw [add_setWidth (by omega)]; exact Offset.sub_base _ (by decide)
  · exact ⟨VG.Proof.AesSiv.X86.iscR s₀, by simp, Region.sub_prefix (by decide)⟩
  · exact ⟨below (VG.Proof.AesSiv.X86.iE s₀) 48, by simp, VG.X86.below_sub (by decide) hp.esp48⟩

/-! ## The whole code -/

theorem initCore_eq : initCore v.expand v.callee v.suffix =
    .seq (.block VG.Impl.AesSiv.X86.initPre) (.seq (call4 v.expand.name v.expand.code) (.seq (.block initMid₁)
      (.seq (call4 ("vg_cmac_aes_subkeys" ++ v.suffix) (Impl.CmacAes.X86.subkeys v.callee))
        (.seq (.block initMid₂) (.seq (call4 v.expand.name v.expand.code) (.block (restore 3))))))) := rfl

theorem init_wp {s₀ : State} (h0 : initX86.pre s₀) :
    WP isa (initCore v.expand v.callee v.suffix) s₀ fun s' => abiPreserved s₀ s' ∧ initX86.post s₀ s' := by
  have hp := IPre.of h0
  have fS := hp.fS
  have fC := hp.fC
  have fK := hp.fK
  have kl := hp.klen
  have e48 := hp.esp48
  rw [VG.Proof.AesSiv.X86.initCore_eq]
  refine WP.seq (WP.mono (VG.Proof.AesSiv.X86.initPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono ((ek_call v) h₁.args) fun s₂ h₂ => ?_)
  have a₂ := h₁.after hp h₂
  refine WP.seq (WP.mono (VG.Proof.AesSiv.X86.initMid₁_wp hp a₂) fun s₃ ⟨h₃, m₃⟩ => ?_)
  refine WP.seq (WP.mono ((sub_call v) h₃.args) fun s₄ h₄ => ?_)
  have a₄ := h₃.after hp h₄
  refine WP.seq (WP.mono (VG.Proof.AesSiv.X86.initMid₂_wp hp a₄) fun s₅ ⟨h₅, m₅⟩ => ?_)
  refine WP.seq (WP.mono ((ek_call v) h₅.args) fun s₆ h₆ => ?_)
  have a₆ := h₅.after hp h₆
  have aC : ∀ d, d ≤ 272 → (VG.Proof.AesSiv.X86.iCt s₀ + BitVec.ofNat 32 d).setWidth 64 = (VG.Proof.AesSiv.X86.iCt s₀).setWidth 64 + BitVec.ofNat 64 d :=
    fun d hd => add_setWidth (by omega)
  have aK : (VG.Proof.AesSiv.X86.iKp s₀ + BitVec.ofNat 32 (VG.Proof.AesSiv.X86.iKL s₀ / 2)).setWidth 64 =
      (VG.Proof.AesSiv.X86.iKp s₀).setWidth 64 + BitVec.ofNat 64 (VG.Proof.AesSiv.X86.iKL s₀ / 2) := add_setWidth (by omega)
  have f₂ : Frame [⟨(VG.Proof.AesSiv.X86.iCt s₀).setWidth 64, 240⟩, ⟨(VG.Proof.AesSiv.X86.iSc s₀).setWidth 64, 512⟩, below (VG.Proof.AesSiv.X86.iE s₀) 48] s₁.mem s₂.mem := by
    have := h₂.frame
    rw [h₁.esp] at this
    refine this.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨below (VG.Proof.AesSiv.X86.iE s₀) 48, by simp, VG.X86.below_sub (by decide) e48⟩
  have f₄ : Frame [⟨(VG.Proof.AesSiv.X86.iCt s₀).setWidth 64 + BitVec.ofNat 64 240, 32⟩, ⟨(VG.Proof.AesSiv.X86.iSc s₀).setWidth 64, 2176⟩,
      below (VG.Proof.AesSiv.X86.iE s₀) 48] s₂.mem s₄.mem := by
    have := h₄.frame; rw [h₃.aft.esp, m₃, aC 240 (by decide)] at this; exact this
  have f₆ : Frame [⟨(VG.Proof.AesSiv.X86.iCt s₀).setWidth 64 + BitVec.ofNat 64 272, 240⟩, ⟨(VG.Proof.AesSiv.X86.iSc s₀).setWidth 64, 512⟩,
      below (VG.Proof.AesSiv.X86.iE s₀) 48] s₄.mem s₆.mem := by
    have := h₆.frame
    rw [h₅.aft.esp, m₅, aC 272 (by decide)] at this
    refine this.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨below (VG.Proof.AesSiv.X86.iE s₀) 48, by simp, VG.X86.below_sub (by decide) e48⟩
  -- The saved registers.
  have dSlot : ∀ d, 2176 ≤ d → d + 4 ≤ 2192 → ∀ r ∈ [⟨(VG.Proof.AesSiv.X86.iCt s₀).setWidth 64, 240⟩, ⟨(VG.Proof.AesSiv.X86.iSc s₀).setWidth 64, 512⟩,
      below (VG.Proof.AesSiv.X86.iE s₀) 48, ⟨(VG.Proof.AesSiv.X86.iCt s₀).setWidth 64 + BitVec.ofNat 64 240, 32⟩, ⟨(VG.Proof.AesSiv.X86.iSc s₀).setWidth 64, 2176⟩,
      ⟨(VG.Proof.AesSiv.X86.iCt s₀).setWidth 64 + BitVec.ofNat 64 272, 240⟩],
      (⟨(VG.Proof.AesSiv.X86.iSc s₀).setWidth 64 + BitVec.ofNat 64 d, 4⟩ : Region).Disjoint r := fun d h₁ h₂ r hr => by
    have sub : Region.Sub ⟨(VG.Proof.AesSiv.X86.iSc s₀).setWidth 64 + BitVec.ofNat 64 d, 4⟩ (VG.Proof.AesSiv.X86.iscR s₀) := Offset.sub_base _ (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hp.c_s.sub_left (Region.sub_prefix (by decide))).symm.sub_left sub
    · exact Offset.disjoint_base _ (by omega) (by omega)
    · exact hp.b_s.symm.sub_left sub
    · exact (hp.c_s.sub_left (Offset.sub_base _ (by decide))).symm.sub_left sub
    · exact Offset.disjoint_base _ (by omega) (by omega)
    · exact (hp.c_s.sub_left (Offset.sub_base _ (by decide))).symm.sub_left sub
  have slots : ∀ r d, (r, d) ∈ saved →
      s₆.mem.readW ((VG.Proof.AesSiv.X86.iSc s₀).setWidth 64 + BitVec.ofNat 64 d) 32 = s₀.gpr r := fun r d hrd => by
    have hb := saved_bound _ hrd
    have c := Region.contains_self ((VG.Proof.AesSiv.X86.iSc s₀).setWidth 64 + BitVec.ofNat 64 d) 4
    rw [f₆.readW c (fun q hq => dSlot d hb.1 hb.2 q (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq ⊢; rcases hq with h | h | h <;> simp [h]))
        (by decide),
      f₄.readW c (fun q hq => dSlot d hb.1 hb.2 q (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq ⊢; rcases hq with h | h | h <;> simp [h]))
        (by decide),
      f₂.readW c (fun q hq => dSlot d hb.1 hb.2 q (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq ⊢; rcases hq with h | h | h <;> simp [h]))
        (by decide), h₁.mem]
    exact saveMem_slot _ _ _ hrd
  refine WP.mono (restore_wp (s₀ := s₀) (i := 3) (Sc := VG.Proof.AesSiv.X86.iSc s₀) a₆.esp
    (by rw [a₆.rd, a₆.wr]; exact hp.arg_in (by decide)) (hp.keep a₆.frame (by decide)) (by omega)
    (by
      rw [a₆.rd, a₆.wr, hp.rd, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.AesSiv.X86.iscR s₀, by simp, 0, by simp, by simp⟩)
    slots) fun s₇ ⟨hcs, m₇⟩ => ?_
  have F₇ : Frame (VG.Proof.AesSiv.X86.IBig s₀) s₀.mem s₇.mem := by rw [m₇]; exact a₆.frame
  refine ⟨⟨hcs, F₇.readW (r := ⟨(VG.Proof.AesSiv.X86.iE s₀).setWidth 64, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)⟩, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.ret_c
    · exact hp.ret_s
    · exact VG.Proof.CmacAes.Stream.X86.ret_below e48
  -- The key context.
  show Spec.Siv.KeyRepr s₇.mem ((VG.Proof.AesSiv.X86.iCt s₀).setWidth 64) (Spec.Aes.bytesAt s₀.mem ((VG.Proof.AesSiv.X86.iKp s₀).setWidth 64) (VG.Proof.AesSiv.X86.iKL s₀))
  have hKL : ∀ {m : Mem}, Frame (VG.Proof.AesSiv.X86.IBig s₀) s₀.mem m → ∀ {d n : Nat}, d + n ≤ VG.Proof.AesSiv.X86.iKL s₀ →
      Spec.Aes.bytesAt m ((VG.Proof.AesSiv.X86.iKp s₀).setWidth 64 + BitVec.ofNat 64 d) n =
        Spec.Aes.bytesAt s₀.mem ((VG.Proof.AesSiv.X86.iKp s₀).setWidth 64 + BitVec.ofNat 64 d) n := fun hf d n hd =>
    Proof.Cmac.bytesAt_frame hf (fun r hr => by
      have sub : Region.Sub ⟨(VG.Proof.AesSiv.X86.iKp s₀).setWidth 64 + BitVec.ofNat 64 d, n⟩ (VG.Proof.AesSiv.X86.ikR s₀) := Offset.sub_base _ hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.k_c.sub_left sub
      · exact hp.k_s.sub_left sub
      · exact hp.b_k.symm.sub_left sub) (by omega)
  have k0 : ∀ p : Addr, p + BitVec.ofNat 64 0 = p := fun p => BitVec.add_zero p
  have hkey₁ : Spec.Aes.bytesAt s₁.mem ((VG.Proof.AesSiv.X86.iKp s₀).setWidth 64) (VG.Proof.AesSiv.X86.iKL s₀ / 2) =
      Spec.Aes.bytesAt s₀.mem ((VG.Proof.AesSiv.X86.iKp s₀).setWidth 64) (VG.Proof.AesSiv.X86.iKL s₀ / 2) := by
    have := hKL (m := s₁.mem) (by rw [h₁.mem]; exact hp.savedMem_big) (d := 0) (n := VG.Proof.AesSiv.X86.iKL s₀ / 2) (by omega)
    rwa [k0] at this
  have hkey₅ : Spec.Aes.bytesAt s₅.mem ((VG.Proof.AesSiv.X86.iKp s₀).setWidth 64 + BitVec.ofNat 64 (VG.Proof.AesSiv.X86.iKL s₀ / 2)) (VG.Proof.AesSiv.X86.iKL s₀ / 2) =
      Spec.Aes.bytesAt s₀.mem ((VG.Proof.AesSiv.X86.iKp s₀).setWidth 64 + BitVec.ofNat 64 (VG.Proof.AesSiv.X86.iKL s₀ / 2)) (VG.Proof.AesSiv.X86.iKL s₀ / 2) := by
    rw [m₅]; exact hKL a₄.frame (by omega)
  have hR : Spec.Aes.rounds (VG.Proof.AesSiv.X86.iKL s₀ / 2 / 4) = VG.Proof.AesSiv.X86.iKL s₀ / 8 + 6 := by simp only [Spec.Aes.rounds]; omega
  have hRb : 16 * (VG.Proof.AesSiv.X86.iKL s₀ / 8 + 6 + 1) ≤ 240 := by omega
  have o₂ := h₂.out
  rw [hkey₁, hR] at o₂
  -- `K1`'s schedule, kept by the later calls.
  have sch₁ : Spec.Aes.bytesAt s₇.mem ((VG.Proof.AesSiv.X86.iCt s₀).setWidth 64) (16 * (VG.Proof.AesSiv.X86.iKL s₀ / 8 + 6 + 1)) =
      Spec.Aes.bytesAt s₂.mem ((VG.Proof.AesSiv.X86.iCt s₀).setWidth 64) (16 * (VG.Proof.AesSiv.X86.iKL s₀ / 8 + 6 + 1)) := by
    rw [m₇, Proof.Cmac.bytesAt_frame f₆ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact Offset.base_disjoint _ (by omega) (by omega)
        · exact (hp.c_s.sub_left (Region.sub_prefix (by omega))).sub_right (Region.sub_prefix (by decide))
        · exact (hp.b_c.sub_right (Region.sub_prefix (by omega))).symm) (by omega),
      Proof.Cmac.bytesAt_frame f₄ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact Offset.base_disjoint _ (by omega) (by omega)
        · exact (hp.c_s.sub_left (Region.sub_prefix (by omega))).sub_right (Region.sub_prefix (by decide))
        · exact (hp.b_c.sub_right (Region.sub_prefix (by omega))).symm) (by omega)]
  refine Proof.AesSiv.keyRepr_of kl (by rw [hR, sch₁, o₂]) ?_ ?_
  · -- The subkeys, kept by the last call.
    have e : Spec.Aes.bytesAt s₇.mem ((VG.Proof.AesSiv.X86.iCt s₀).setWidth 64 + BitVec.ofNat 64 240) 32 =
        Spec.Aes.bytesAt s₄.mem ((VG.Proof.AesSiv.X86.iCt s₀).setWidth 64 + BitVec.ofNat 64 240) 32 := by
      rw [m₇]
      exact Proof.Cmac.bytesAt_frame f₆ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact Offset.disjoint _ (by omega) (by omega) (by omega)
        · exact (hp.c_s.sub_left (Offset.sub_base _ (by decide))).sub_right (Region.sub_prefix (by decide))
        · exact (hp.b_c.sub_right (Offset.sub_base _ (by decide))).symm) (by decide)
    have o₄ := h₄.out
    rw [aC 240 (by decide), m₃, o₂] at o₄
    rw [e, o₄]
  · have o₆ := h₆.out
    rw [aC 272 (by decide), aK, hkey₅, hR] at o₆
    rw [hR, m₇, o₆]

/-! ## Constant time -/

theorem ek_after₁ {s₀ s : State} (hp : VG.Proof.AesSiv.X86.IPre s₀) (h : VG.Proof.AesSiv.X86.IMid₁ s₀ s) :
    WP isa (call4 v.expand.name v.expand.code) s (VG.Proof.AesSiv.X86.IAft s₀) :=
  WP.mono ((ek_call v) h.args) fun _ h' => h.after hp h'

theorem sub_after {s₀ s : State} (hp : VG.Proof.AesSiv.X86.IPre s₀) (h : VG.Proof.AesSiv.X86.IMid₂ s₀ s) :
    WP isa (call4 ("vg_cmac_aes_subkeys" ++ v.suffix) (Impl.CmacAes.X86.subkeys v.callee)) s (VG.Proof.AesSiv.X86.IAft s₀) :=
  WP.mono ((sub_call v) h.args) fun _ h' => h.after hp h'

theorem ek_after₂ {s₀ s : State} (hp : VG.Proof.AesSiv.X86.IPre s₀) (h : VG.Proof.AesSiv.X86.IMid₃ s₀ s) :
    WP isa (call4 v.expand.name v.expand.code) s (VG.Proof.AesSiv.X86.IAft s₀) :=
  WP.mono ((ek_call v) h.args) fun _ h' => h.after hp h'

theorem init_rel {s₀ s₀' : State} (h0 : initX86.pre s₀) (h0' : initX86.pre s₀') (hq : initX86.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (initCore v.expand v.callee v.suffix) fun _ _ => True := by
  have hp := IPre.of h0
  have hp' := IPre.of h0'
  obtain ⟨qE, qa⟩ := hq
  have e0 : VG.Proof.AesSiv.X86.iKp s₀ = VG.Proof.AesSiv.X86.iKp s₀' := qa 0 (by decide)
  have e1 : VG.Proof.AesSiv.X86.iKL s₀ = VG.Proof.AesSiv.X86.iKL s₀' := by rw [VG.Proof.AesSiv.X86.iKL, VG.Proof.AesSiv.X86.iKL, qa 1 (by decide)]
  have e2 : VG.Proof.AesSiv.X86.iCt s₀ = VG.Proof.AesSiv.X86.iCt s₀' := qa 2 (by decide)
  have e3 : VG.Proof.AesSiv.X86.iSc s₀ = VG.Proof.AesSiv.X86.iSc s₀' := qa 3 (by decide)
  have ag : ∀ {a b : State}, Pt 4 s₀ a → Pt 4 s₀' b → VG.X86.Taint.Agree (argTaint [] (4 + 4 * 4)) a b :=
    fun h₁ h₂ => Pt.agree qE qa hp.argsOut hp'.argsOut h₁ h₂ fun r hr => by simp at hr
  have a := ((RelCT.taint (A := VG.X86.taint) (P := fun a b => a = s₀ ∧ b = s₀') (argTaint [] (4 + 4 * 4))
    (fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ag (Pt.refl _ _) (Pt.refl _ _))
    (c := .block VG.Impl.AesSiv.X86.initPre) (by taint_decide)).wp (F₁ := VG.Proof.AesSiv.X86.IMid₁ s₀) (F₂ := VG.Proof.AesSiv.X86.IMid₁ s₀')
    fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨VG.Proof.AesSiv.X86.initPre_wp hp, VG.Proof.AesSiv.X86.initPre_wp hp'⟩).mono (fun _ _ h => h)
    fun _ _ h => h.2
  have e := ((ek_rel v (E := VG.Proof.AesSiv.X86.iE s₀) (P := fun a b => VG.Proof.AesSiv.X86.IMid₁ s₀ a ∧ VG.Proof.AesSiv.X86.IMid₁ s₀' b) fun a b h =>
      ⟨h.1.args, by rw [e0, e1, e2, e3]; exact h.2.args, h.1.esp, by rw [h.2.esp]; exact qE.symm⟩).wp
      (F₁ := VG.Proof.AesSiv.X86.IAft s₀) (F₂ := VG.Proof.AesSiv.X86.IAft s₀') fun _ _ h => ⟨(VG.Proof.AesSiv.X86.ek_after₁ v) hp h.1, (VG.Proof.AesSiv.X86.ek_after₁ v) hp' h.2⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  have m := ((RelCT.taint (A := VG.X86.taint) (P := fun a b => VG.Proof.AesSiv.X86.IAft s₀ a ∧ VG.Proof.AesSiv.X86.IAft s₀' b) (argTaint [] (4 + 4 * 4))
    (fun _ _ h => ag (h.1.pt hp) (h.2.pt hp')) (c := .block initMid₁) (by taint_decide)).wp
    (F₁ := fun s => VG.Proof.AesSiv.X86.IMid₂ s₀ s) (F₂ := fun s => VG.Proof.AesSiv.X86.IMid₂ s₀' s)
    fun _ _ h => ⟨WP.mono (VG.Proof.AesSiv.X86.initMid₁_wp hp h.1) fun _ h => h.1, WP.mono (VG.Proof.AesSiv.X86.initMid₁_wp hp' h.2) fun _ h => h.1⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2
  have sk := ((sub_rel v (E := VG.Proof.AesSiv.X86.iE s₀) (P := fun a b => VG.Proof.AesSiv.X86.IMid₂ s₀ a ∧ VG.Proof.AesSiv.X86.IMid₂ s₀' b) fun a b h =>
      ⟨h.1.args, by rw [e1, e2, e3]; exact h.2.args, h.1.aft.esp, by rw [h.2.aft.esp]; exact qE.symm⟩).wp
      (F₁ := VG.Proof.AesSiv.X86.IAft s₀) (F₂ := VG.Proof.AesSiv.X86.IAft s₀') fun _ _ h => ⟨(VG.Proof.AesSiv.X86.sub_after v) hp h.1, (VG.Proof.AesSiv.X86.sub_after v) hp' h.2⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  have m₂ := ((RelCT.taint (A := VG.X86.taint) (P := fun a b => VG.Proof.AesSiv.X86.IAft s₀ a ∧ VG.Proof.AesSiv.X86.IAft s₀' b) (argTaint [] (4 + 4 * 4))
    (fun _ _ h => ag (h.1.pt hp) (h.2.pt hp')) (c := .block initMid₂) (by taint_decide)).wp
    (F₁ := fun s => VG.Proof.AesSiv.X86.IMid₃ s₀ s) (F₂ := fun s => VG.Proof.AesSiv.X86.IMid₃ s₀' s)
    fun _ _ h => ⟨WP.mono (VG.Proof.AesSiv.X86.initMid₂_wp hp h.1) fun _ h => h.1, WP.mono (VG.Proof.AesSiv.X86.initMid₂_wp hp' h.2) fun _ h => h.1⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2
  have e' := ((ek_rel v (E := VG.Proof.AesSiv.X86.iE s₀) (P := fun a b => VG.Proof.AesSiv.X86.IMid₃ s₀ a ∧ VG.Proof.AesSiv.X86.IMid₃ s₀' b) fun a b h =>
      ⟨h.1.args, by rw [e0, e1, e2, e3]; exact h.2.args, h.1.aft.esp, by rw [h.2.aft.esp]; exact qE.symm⟩).wp
      (F₁ := VG.Proof.AesSiv.X86.IAft s₀) (F₂ := VG.Proof.AesSiv.X86.IAft s₀') fun _ _ h => ⟨(VG.Proof.AesSiv.X86.ek_after₂ v) hp h.1, (VG.Proof.AesSiv.X86.ek_after₂ v) hp' h.2⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  have p := RelCT.taint (A := VG.X86.taint) (P := fun a b => VG.Proof.AesSiv.X86.IAft s₀ a ∧ VG.Proof.AesSiv.X86.IAft s₀' b) (argTaint [] (4 + 4 * 4))
    (fun _ _ h => ag (h.1.pt hp) (h.2.pt hp')) (c := .block (restore 3)) (by taint_decide)
  rw [VG.Proof.AesSiv.X86.initCore_eq]
  exact a.seq (e.seq (m.seq (sk.seq (m₂.seq (e'.seq p)))))

theorem init_ct : ConstantTime isa initX86.pre initX86.pub (initCore v.expand v.callee v.suffix) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => ((VG.Proof.AesSiv.X86.init_rel v) h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesSiv.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.X86.Verified`. -/
section

namespace VG.Proof.AesSiv.X86

open VG VG.X86 VG.Impl.AesSiv.X86
open VG.Proof.AesGcm.X86 (w64 ofNat_toNat32 argsR)

theorem filter_true' (l : List Region) : l.filter (fun _ => true) = l := List.filter_eq_self.mpr (by simp)

theorem filter_false' (l : List Region) : l.filter (fun _ => false) = [] := List.filter_eq_nil_iff.mpr (by simp)

theorem filterMap_some' {β : Type} (f : Region → β) (l : List Region) :
    l.filterMap (fun x => some (f x)) = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem filterMap_none' {β : Type} (l : List Region) : l.filterMap (fun _ => (none : Option β)) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem cov_mem {r : Region} {ts : List Region} (h : r ∈ ts) : Covers [r] ts := by
  intro a n ⟨x, hx, hc⟩
  simp only [List.mem_singleton] at hx; subst hx; exact ⟨x, h, hc⟩

theorem below_eq56 {SP : BitVec 32} (h : 56 ≤ SP.toNat) : below SP 56 = ⟨w64 SP - BitVec.ofNat 64 56, 56⟩ := by
  simp only [below, Region.mk.injEq, and_true]
  exact VG.X86.Taint.sub_setWidth h

/-- The entry's public values, from the shared contracts' precondition. -/
abbrev ETopS (s : State) : Prop :=
  ETop (arg s 0) (arg s 7) (s.gpr .esp) (arg s 2) (arg s 4) (arg s 6) (arg s 1).toNat (arg s 3).toNat
    (arg s 5).toNat (compA s.mem (arg s 2)) (compL s.mem (arg s 2)) s

set_option linter.unusedSimpArgs false in
/-- The precondition of `encrypt`'s shared contract with the working space:
the entry's invariant, and `siv` writable and apart from the data. -/
theorem encPre_of {s : State} (h : (Proof.AesSiv.encryptScratchContract X86.abi 56).pre s) :
    ETopS s ∧ Covers [⟨w64 (arg s 6), 16⟩] s.wr ∧
      (⟨w64 (arg s 6), 16⟩ : Region).Disjoint ⟨w64 (arg s 4), (arg s 5).toNat⟩ := by
  sig_pre [Proof.AesSiv.encryptScratchContract, Proof.AesSiv.encryptScratchSig, Spec.Siv.encryptPre, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes] at h
  sig_split h
  simp only [List.map_append, List.filter_append, List.filter_map, List.map_map, List.filterMap_append,
    List.filterMap_map, List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, Function.comp_def,
    Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false, List.map_id', Sig.conj_cons,
    Sig.conj_append, Sig.conj_map, Bool.cond_false, Bool.cond_true, List.filterMap_cons, List.filterMap_nil,
    List.append_nil, Sig.conj, List.append_eq, VG.Proof.AesSiv.X86.filter_true', VG.Proof.AesSiv.X86.filter_false', VG.Proof.AesSiv.X86.filterMap_some', VG.Proof.AesSiv.X86.filterMap_none',
    List.filter_map] at *
  rename_i sp56 fa cd cT rc rd rT rw fc fd fT fw hrd hwr hc1 hc2 hc3
  obtain ⟨cW, ⟨-, cA⟩, dT, dW, dDesc, ⟨dL, dA⟩, tW, -, ⟨-, -⟩, wDesc, ⟨wL, wA⟩, ⟨-, descA⟩, -⟩ := hc1
  obtain ⟨retDesc, ⟨retL, retA⟩, sC, sD, sT, sW, sDesc, sL, sA⟩ := hc2
  obtain ⟨descFit, lFit⟩ := hc3
  have bE := VG.Proof.AesSiv.X86.below_eq56 sp56
  have inRd {r : Region} (hr : r ∈ s.rd) : r ∈ s.rd ++ s.wr := List.mem_append_left _ hr
  have inWr {r : Region} (hr : r ∈ s.wr) : r ∈ s.rd ++ s.wr := List.mem_append_right _ hr
  have mC : (⟨w64 (VG.X86.arg s 0), 512⟩ : Region) ∈ s.rd := by rw [hrd]; exact List.mem_cons_self
  have mA : (⟨w64 (VG.X86.arg s 2), 8 * (VG.X86.arg s 3).toNat⟩ : Region) ∈ s.rd := by
    rw [hrd, Nat.mul_comm]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have mD : (⟨w64 (arg s 4), (arg s 5).toNat⟩ : Region) ∈ s.wr := by rw [hwr]; exact List.mem_cons_self
  have mT : (⟨w64 (arg s 6), 16⟩ : Region) ∈ s.wr := by
    rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have mW : (⟨w64 (arg s 7), 2576⟩ : Region) ∈ s.wr := by
    rw [hwr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have mR : (⟨argAddr s 0, 32⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  have L : Lay (arg s 0) (arg s 7) (s.gpr .esp) := ⟨fc, fw, sp56, cW, by rw [bE]; exact sC, by rw [bE]; exact sW⟩
  refine ⟨⟨⟨⟨L, h, ⟨cov_mem (inRd mA), by rw [Nat.mul_comm]; exact descFit,
      by rw [Nat.mul_comm]; exact wDesc.symm, by rw [bE, Nat.mul_comm]; exact sDesc⟩, fun i hi => ?_, BitVec.isLt _⟩,
    ⟨⟨cov_mem (inWr mD), fd, dW, by rw [bE]; exact sD⟩, cov_mem mD, cd⟩,
    ⟨cov_mem (inRd mC), cov_mem mW⟩, rfl, rfl, (ofNat_toNat32 _).symm, rfl, (ofNat_toNat32 _).symm, rfl,
    (ofNat_toNat32 _).symm, rfl, rfl, by rw [Proof.AesGcm.X86.argsR_eq]; exact cov_mem (inWr mR),
    by rw [Proof.AesGcm.X86.argsR_eq]; exact wA.symm, by rw [Proof.AesGcm.X86.argsR_eq]; exact dA.symm,
    by rw [bE, Proof.AesGcm.X86.argsR_eq]; exact sA, by omega, rw, rd, rT, BitVec.isLt _, fT, cov_mem (inWr mT),
    tW, by rw [bE]; exact sT⟩, fun j hj => ⟨rfl, rfl⟩⟩, cov_mem mT, dT.symm⟩
  have hm := comp_mem s.mem (arg s 2) hi
  exact ⟨cov_mem (inRd (by rw [hrd]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm))),
    by have := lFit _ hm; rwa [Proof.AesGcm.X86.toNat_w64] at this, (wL _ hm).symm, by rw [bE]; exact sL _ hm⟩

set_option linter.unusedSimpArgs false in
/-- The precondition of `decrypt`'s shared contract with the working space:
the entry's invariant. -/
theorem decPre_of {s : State} (h : (Proof.AesSiv.decryptScratchContract X86.abi 56).pre s) : ETopS s := by
  sig_pre [Proof.AesSiv.decryptScratchContract, Proof.AesSiv.decryptScratchSig, Spec.Siv.decryptPre, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes] at h
  sig_split h
  simp only [List.map_append, List.filter_append, List.filter_map, List.map_map, List.filterMap_append,
    List.filterMap_map, List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, Function.comp_def,
    Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false, List.map_id', Sig.conj_cons,
    Sig.conj_append, Sig.conj_map, Bool.cond_false, Bool.cond_true, List.filterMap_cons, List.filterMap_nil,
    List.append_nil, Sig.conj, List.append_eq, filter_true', filter_false', filterMap_some', filterMap_none',
    List.filter_map] at *
  rename_i sp56 fa cd rc rd rT rw fc fd fT fw hrd hwr hc1 hc2 hc3
  obtain ⟨cW, ⟨-, cA⟩, -, dW, dDesc, ⟨dL, dA⟩, tW, ⟨-, -⟩, wDesc, ⟨wL, wA⟩, ⟨-, descA⟩, -⟩ := hc1
  obtain ⟨retDesc, ⟨retL, retA⟩, sC, sD, sT, sW, sDesc, sL, sA⟩ := hc2
  obtain ⟨descFit, lFit⟩ := hc3
  have bE := below_eq56 sp56
  have inRd {r : Region} (hr : r ∈ s.rd) : r ∈ s.rd ++ s.wr := List.mem_append_left _ hr
  have inWr {r : Region} (hr : r ∈ s.wr) : r ∈ s.rd ++ s.wr := List.mem_append_right _ hr
  have mC : (⟨w64 (arg s 0), 512⟩ : Region) ∈ s.rd := by rw [hrd]; exact List.mem_cons_self
  have mT : (⟨w64 (arg s 6), 16⟩ : Region) ∈ s.rd := by
    rw [hrd]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have mA : (⟨w64 (arg s 2), 8 * (arg s 3).toNat⟩ : Region) ∈ s.rd := by
    rw [hrd, Nat.mul_comm]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have mD : (⟨w64 (arg s 4), (arg s 5).toNat⟩ : Region) ∈ s.wr := by rw [hwr]; exact List.mem_cons_self
  have mW : (⟨w64 (arg s 7), 2576⟩ : Region) ∈ s.wr := by
    rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have mR : (⟨argAddr s 0, 32⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  have L : Lay (arg s 0) (arg s 7) (s.gpr .esp) := ⟨fc, fw, sp56, cW, by rw [bE]; exact sC, by rw [bE]; exact sW⟩
  refine ⟨⟨⟨L, h, ⟨cov_mem (inRd mA), by rw [Nat.mul_comm]; exact descFit,
      by rw [Nat.mul_comm]; exact wDesc.symm, by rw [bE, Nat.mul_comm]; exact sDesc⟩, fun i hi => ?_, BitVec.isLt _⟩,
    ⟨⟨cov_mem (inWr mD), fd, dW, by rw [bE]; exact sD⟩, cov_mem mD, cd⟩,
    ⟨cov_mem (inRd mC), cov_mem mW⟩, rfl, rfl, (ofNat_toNat32 _).symm, rfl, (ofNat_toNat32 _).symm, rfl,
    (ofNat_toNat32 _).symm, rfl, rfl, by rw [Proof.AesGcm.X86.argsR_eq]; exact cov_mem (inWr mR),
    by rw [Proof.AesGcm.X86.argsR_eq]; exact wA.symm, by rw [Proof.AesGcm.X86.argsR_eq]; exact dA.symm,
    by rw [bE, Proof.AesGcm.X86.argsR_eq]; exact sA, by omega, rw, rd, rT, BitVec.isLt _, fT, cov_mem (inRd mT),
    tW, by rw [bE]; exact sT⟩, fun j hj => ⟨rfl, rfl⟩⟩
  have hm := comp_mem s.mem (arg s 2) hi
  exact ⟨cov_mem (inRd (by rw [hrd]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ hm)))),
    by have := lFit _ hm; rwa [Proof.AesGcm.X86.toNat_w64] at this, (wL _ hm).symm, by rw [bE]; exact sL _ hm⟩

/-- Descriptors whose bytes are the same in two memories list the same
components. -/
theorem comp_eq {m₁ m₂ : Mem} {A : BitVec 32} {N : Nat}
    (h : ∀ i < N * 8, m₁ (w64 A + BitVec.ofNat 64 i) = m₂ (w64 A + BitVec.ofNat 64 i)) {j : Nat} (hj : j < N) :
    VG.Proof.AesSiv.X86.compA m₂ A j = VG.Proof.AesSiv.X86.compA m₁ A j ∧ VG.Proof.AesSiv.X86.compL m₂ A j = VG.Proof.AesSiv.X86.compL m₁ A j := by
  have r {d : Nat} (hd : d + 4 ≤ N * 8) : m₂.readW (w64 A + BitVec.ofNat 64 d) 32 =
      m₁.readW (w64 A + BitVec.ofNat 64 d) 32 := by
    have e := Mem.read_congr (m := m₂) (m' := m₁) (a := w64 A + BitVec.ofNat 64 d) (n := 32 / 8)
      fun k hk => by rw [Offset.add_add]; exact (h _ (by omega)).symm
    simp only [Mem.readW, e]
  exact ⟨r (by omega), by simp only [VG.Proof.AesSiv.X86.compL]; rw [r (by omega)]⟩

/-- What two runs of `encrypt` or `decrypt` agree on: the stack pointer, the
arguments and the descriptors. -/
def EncPub (s₁ s₂ : State) : Prop :=
  (s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1 ∧ arg s₁ 2 = arg s₂ 2 ∧
    arg s₁ 3 = arg s₂ 3 ∧ arg s₁ 4 = arg s₂ 4 ∧ arg s₁ 5 = arg s₂ 5 ∧ arg s₁ 6 = arg s₂ 6 ∧ arg s₁ 7 = arg s₂ 7) ∧
  ∀ i < (arg s₁ 3).toNat * 8, s₁.mem (w64 (arg s₁ 2) + BitVec.ofNat 64 i) =
    s₂.mem (w64 (arg s₁ 2) + BitVec.ofNat 64 i)

/-- The second run's entry invariant, with the first run's public values. -/
theorem encPre_pub {X : BitVec 32 → State → Prop} {s₁ s₂ : State} (E : ETopS s₂) (hX : X (arg s₂ 6) s₂)
    (hq : EncPub s₁ s₂) :
    ETop (arg s₁ 0) (arg s₁ 7) (s₁.gpr .esp) (arg s₁ 2) (arg s₁ 4) (arg s₁ 6) (arg s₁ 1).toNat (arg s₁ 3).toNat
      (arg s₁ 5).toNat (compA s₁.mem (arg s₁ 2)) (compL s₁.mem (arg s₁ 2)) s₂ ∧ X (arg s₁ 6) s₂ := by
  obtain ⟨⟨q0, q1, q2, q3, q4, q5, q6, q7, q8⟩, hd⟩ := hq
  refine ⟨⟨?_, fun j hj => comp_eq hd hj⟩, by rw [q7]; exact hX⟩
  rw [q0, q1, q2, q3, q4, q5, q6, q7, q8]
  exact E.pre

/-- A state satisfying the precondition of `vg_aes_siv_encrypt` and
`vg_aes_siv_decrypt`: the key context at `0x1000`, 10 rounds, no associated
data (descriptors at `0x2000`), no data (at `0x3000`), `siv` at `0x5000` and
`work` at `0x4000`, as stack arguments at `0x8004`. -/
def encSat (rd wr : List Region) : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 10 else if a = 0x800d then 0x20
    else if a = 0x8015 then 0x30 else if a = 0x801d then 0x50 else if a = 0x8021 then 0x40 else 0
  rd := rd
  wr := wr

theorem encSat_args (rd wr : List Region) : arg (encSat rd wr) 0 = 0x1000 ∧ arg (encSat rd wr) 1 = 10 ∧
    arg (encSat rd wr) 2 = 0x2000 ∧ arg (encSat rd wr) 3 = 0 ∧ arg (encSat rd wr) 4 = 0x3000 ∧
    arg (encSat rd wr) 5 = 0 ∧ arg (encSat rd wr) 6 = 0x5000 ∧ arg (encSat rd wr) 7 = 0x4000 ∧
    argAddr (encSat rd wr) 0 = 0x8004 := by
  have h : arg (encSat [] []) 0 = 0x1000 ∧ arg (encSat [] []) 1 = 10 ∧ arg (encSat [] []) 2 = 0x2000 ∧
      arg (encSat [] []) 3 = 0 ∧ arg (encSat [] []) 4 = 0x3000 ∧ arg (encSat [] []) 5 = 0 ∧
      arg (encSat [] []) 6 = 0x5000 ∧ arg (encSat [] []) 7 = 0x4000 ∧ argAddr (encSat [] []) 0 = 0x8004 := by
    decide
  exact h

theorem encSat_pre : ∃ s, (Proof.AesSiv.encryptScratchContract X86.abi 56).pre s := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, e⟩ := encSat_args [⟨0x1000, 512⟩, ⟨0x2000, 0⟩]
    [⟨0x3000, 0⟩, ⟨0x5000, 16⟩, ⟨0x4000, 2576⟩, ⟨0x8004, 32⟩]
  have esp : (encSat [⟨0x1000, 512⟩, ⟨0x2000, 0⟩]
    [⟨0x3000, 0⟩, ⟨0x5000, 16⟩, ⟨0x4000, 2576⟩, ⟨0x8004, 32⟩]).gpr .esp = 0x8000 := rfl
  sig_implies_sat [Proof.AesSiv.encryptScratchContract, Proof.AesSiv.encryptScratchSig, Spec.Siv.encryptPre,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes] [a0, a1, a2, a3, a4, a5, a6, a7, e, esp]
    using encSat [⟨0x1000, 512⟩, ⟨0x2000, 0⟩] [⟨0x3000, 0⟩, ⟨0x5000, 16⟩, ⟨0x4000, 2576⟩, ⟨0x8004, 32⟩]

theorem decSat_pre : ∃ s, (Proof.AesSiv.decryptScratchContract X86.abi 56).pre s := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, e⟩ := encSat_args [⟨0x1000, 512⟩, ⟨0x5000, 16⟩, ⟨0x2000, 0⟩]
    [⟨0x3000, 0⟩, ⟨0x4000, 2576⟩, ⟨0x8004, 32⟩]
  have esp : (encSat [⟨0x1000, 512⟩, ⟨0x5000, 16⟩, ⟨0x2000, 0⟩]
    [⟨0x3000, 0⟩, ⟨0x4000, 2576⟩, ⟨0x8004, 32⟩]).gpr .esp = 0x8000 := rfl
  sig_implies_sat [Proof.AesSiv.decryptScratchContract, Proof.AesSiv.decryptScratchSig, Spec.Siv.decryptPre,
    Spec.Siv.decryptLeak, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] [a0, a1, a2, a3, a4, a5, a6, a7, e, esp]
    using encSat [⟨0x1000, 512⟩, ⟨0x5000, 16⟩, ⟨0x2000, 0⟩] [⟨0x3000, 0⟩, ⟨0x4000, 2576⟩, ⟨0x8004, 32⟩]

theorem noEsp_of {c : Prog isa} (h : NoSp c) :
    c.allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  rw [Code.allInstrs_eq]
  exact List.all_eq_true.mpr fun i hi => by simp [h i hi]

variable (v : Proof.Aes.X86.Ctr32Impl)

theorem encrypt_verified :
    Verified X86.target (encrypt v.callee v.suffix) (Proof.AesSiv.encryptScratchContract X86.abi 56) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, encSat_pre⟩
  · obtain ⟨E, hTw, hTd⟩ := encPre_of hs
    obtain ⟨t, s', he, hq⟩ := encrypt_wp v E.pre hTw hTd
    refine ⟨t, s', he, hq.1, ?_⟩
    sig_post [Proof.AesSiv.encryptScratchContract, Proof.AesSiv.encryptScratchSig, Spec.Siv.encryptPost,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    exact fun _ => hq.2
  · sig_pub [Proof.AesSiv.encryptScratchContract, Proof.AesSiv.encryptScratchSig, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes] at hp
    sig_split hp
    rename_i q0 q1 q2 q3 q4 q5 q6 q7 q8
    obtain ⟨E₁, W₁, -⟩ := encPre_of h₁
    obtain ⟨E₂, W₂, -⟩ := encPre_of h₂
    exact (encrypt_top_ct v s₁ E₁ _ _ _ _ _ _
      ⟨⟨E₁, W₁⟩, encPre_pub (X := fun T s => Covers [⟨w64 T, 16⟩] s.wr) E₂ W₂
        ⟨⟨q0, q1, q2, q3, q4, q5, q6, q7, q8⟩, hp⟩⟩ e₁ e₂).1

/-- The return value: the low word of `edx:eax`. -/
theorem setWidth_ret (a b : BitVec 32) : (a ++ b).setWidth 32 = b := BitVec.setWidth_append_eq_right

theorem decrypt_verified :
    Verified X86.target (decrypt v.callee v.suffix) (Proof.AesSiv.decryptScratchContract X86.abi 56) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, decSat_pre⟩
  · obtain ⟨t, s', he, hq⟩ := decrypt_wp v (decPre_of hs).pre
    refine ⟨t, s', he, hq.1, ?_⟩
    sig_post [Proof.AesSiv.decryptScratchContract, Proof.AesSiv.decryptScratchSig, Spec.Siv.decryptPost,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [setWidth_ret]
    exact fun _ => hq.2
  · sig_pub [Proof.AesSiv.decryptScratchContract, Proof.AesSiv.decryptScratchSig, Spec.Siv.decryptLeak, X86.abi,
      X86.argSlots, X86.argVal, X86.argBytes] at hp
    sig_split hp
    rename_i q0 _ q1 q2 q3 q4 q5 q6 q7 q8
    exact (decrypt_top_ct v s₁ (decPre_of h₁) _ _ _ _ _ _
      ⟨decPre_of h₁, (encPre_pub (X := fun _ _ => True) (decPre_of h₂) trivial
        ⟨⟨q0, q1, q2, q3, q4, q5, q6, q7, q8⟩, hp⟩).1⟩ e₁ e₂).1

/-! ## The working space on the stack -/

theorem encrypt_noEsp : (encrypt v.callee v.suffix).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [encrypt, encS2v, sivEntry, Impl.AesGcm.X86.entry, start, s2vAds, cmacOf, cmacPre, updCall, finCall,
    Impl.CmacAes.Stream.X86.call6, finish, shortTail, copyN, shortMac, longTail, longMac, ctr, ctrWhole, ctrTail,
    ctrCall, sivOut, Code.allInstrs, noEsp_of (Proof.CmacAes.X86.update_nosp v),
    noEsp_of (Proof.CmacAes.X86.finalize_nosp v), noEsp_of v.nosp]
  decide +kernel

theorem decrypt_noEsp : (decrypt v.callee v.suffix).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [decrypt, encS2v, sivEntry, Impl.AesGcm.X86.entry, start, s2vAds, cmacOf, cmacPre, updCall, finCall,
    Impl.CmacAes.Stream.X86.call6, finish, shortTail, copyN, shortMac, longTail, longMac, ctr, ctrWhole, ctrTail,
    ctrCall, mask, sivIn, Code.allInstrs, noEsp_of (Proof.CmacAes.X86.update_nosp v),
    noEsp_of (Proof.CmacAes.X86.finalize_nosp v), noEsp_of v.nosp]
  decide +kernel

theorem encrypt_stackUse : stackUse (encrypt v.callee v.suffix) ≤ 56 := by
  simp only [encrypt, encS2v, sivEntry, Impl.AesGcm.X86.entry, start, s2vAds, cmacOf, cmacPre, updCall, finCall,
    Impl.CmacAes.Stream.X86.call6, finish, shortTail, copyN, shortMac, longTail, longMac, ctr, ctrWhole, ctrTail,
    ctrCall, sivOut, stackUse, Proof.CmacAes.X86.update_stack v, Proof.CmacAes.X86.finalize_stack v, v.stack]
  decide +kernel

theorem decrypt_stackUse : stackUse (decrypt v.callee v.suffix) ≤ 56 := by
  simp only [decrypt, encS2v, sivEntry, Impl.AesGcm.X86.entry, start, s2vAds, cmacOf, cmacPre, updCall, finCall,
    Impl.CmacAes.Stream.X86.call6, finish, shortTail, copyN, shortMac, longTail, longMac, ctr, ctrWhole, ctrTail,
    ctrCall, mask, sivIn, stackUse, Proof.CmacAes.X86.update_stack v, Proof.CmacAes.X86.finalize_stack v, v.stack]
  decide +kernel

theorem encFrameSat_pre : ∃ s, (Spec.Siv.encryptContract X86.abi 2668).pre s := by
  implies_sat [Spec.Siv.encryptContract, Spec.Siv.encryptSig, Spec.Siv.encryptPre, Spec.Siv.encryptPost,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [encSat, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using encSat [⟨0x1000, 512⟩, ⟨0x2000, 0⟩] [⟨0x3000, 0⟩, ⟨0x5000, 16⟩, ⟨0x8004, 28⟩]

theorem decFrameSat_pre : ∃ s, (Spec.Siv.decryptContract X86.abi 2668).pre s := by
  implies_sat [Spec.Siv.decryptContract, Spec.Siv.decryptSig, Spec.Siv.decryptPre, Spec.Siv.decryptPost,
    Spec.Siv.decryptLeak, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [encSat, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using encSat [⟨0x1000, 512⟩, ⟨0x5000, 16⟩, ⟨0x2000, 0⟩] [⟨0x3000, 0⟩, ⟨0x8004, 28⟩]

/-- `encrypt` in a frame of 2612 bytes: the return address, the seven
argument slots, the working space's address and its 2576 bytes. -/
theorem encrypt_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2612 7 (encrypt v.callee v.suffix))
      (Spec.Siv.encryptContract X86.abi 2668) :=
  X86.Verified.stackScratchL (sig := Spec.Siv.encryptSig) (nm := "work") (e := .u64) (n := 322)
    (pre := Spec.Siv.encryptPre X86.abi.ptrBits) (post := Spec.Siv.encryptPost X86.abi.ptrBits)
    (wa := true) (stack := 56) (bytes := 2612) (encrypt_verified v) (by decide) (encrypt_noEsp v)
    (encrypt_stackUse v) (Proof.AesSiv.encryptPre_local _) (Proof.AesSiv.encryptPost_local _) encFrameSat_pre

/-- `decrypt` in a frame of 2612 bytes, as `encrypt`. -/
theorem decrypt_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2612 7 (decrypt v.callee v.suffix))
      (Spec.Siv.decryptContract X86.abi 2668) :=
  X86.Verified.stackScratchL (sig := Spec.Siv.decryptSig) (nm := "work") (e := .u64) (n := 322)
    (pre := Spec.Siv.decryptPre X86.abi.ptrBits) (post := Spec.Siv.decryptPost X86.abi.ptrBits)
    (wa := true) (stack := 56) (leak := some (Spec.Siv.decryptLeak X86.abi.ptrBits)) (bytes := 2612)
    (decrypt_verified v) (by decide) (decrypt_noEsp v) (decrypt_stackUse v) (Proof.AesSiv.decryptPre_local _)
    (Proof.AesSiv.decryptPost_local _) decFrameSat_pre (hleak := Proof.AesSiv.decryptLeak_local _)

/-! ## `vg_aes_siv_init` -/

/-- The regions of `initX86`: the key and the stack arguments read-only. -/
def initRd (s : State) : List Region := [⟨w64 (VG.X86.arg s 0), (VG.X86.arg s 1).toNat⟩, ⟨argAddr s 0, 16⟩]
def initWr (s : State) : List Region := [⟨w64 (VG.X86.arg s 2), 512⟩, ⟨w64 (VG.X86.arg s 3), 2560⟩]

theorem initPre_of {s : State} (h : (Proof.AesSiv.initScratchContract X86.abi 48).pre s) :
    initX86.pre (s.withRegions (VG.Proof.AesSiv.X86.initRd s) (VG.Proof.AesSiv.X86.initWr s)) ∧ s.rd = [⟨w64 (VG.X86.arg s 0), (VG.X86.arg s 1).toNat⟩] ∧
      s.wr = [⟨w64 (VG.X86.arg s 2), 512⟩, ⟨w64 (VG.X86.arg s 3), 2560⟩, ⟨argAddr s 0, 16⟩] := by
  sig_pre [Proof.AesSiv.initScratchContract, Proof.AesSiv.initScratchSig, Spec.Siv.initPre, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes] at h
  sig_split h
  rename_i sp48 fa hrd hwr kc ks ka cs ca sa rk rc rs ra stk stc sts sta fk fc fs
  exact ⟨⟨rfl, rfl, kc, ks, ka, cs, ca, sa, rk, rc, rs, ra, stk, stc, sts, sta, fk, fc, fs, sp48, (by omega : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32), h⟩,
    hrd, hwr⟩

/-- A state satisfying `vg_aes_siv_init`'s precondition: a key of 32 bytes
at `0x1000`, the context at `0x2000` and the scratch buffer at `0x4000`, as
stack arguments at `0x8004`. -/
def initSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 32 else if a = 0x800d then 0x20
    else if a = 0x8011 then 0x40 else 0
  rd := [⟨0x1000, 32⟩]
  wr := [⟨0x2000, 512⟩, ⟨0x4000, 2560⟩, ⟨0x8004, 16⟩]

theorem initSat_pre : ∃ s, (Proof.AesSiv.initScratchContract X86.abi 48).pre s := by
  have a0 : VG.X86.arg VG.Proof.AesSiv.X86.initSat 0 = 0x1000 := by decide
  have a1 : VG.X86.arg VG.Proof.AesSiv.X86.initSat 1 = 32 := by decide
  have a2 : VG.X86.arg VG.Proof.AesSiv.X86.initSat 2 = 0x2000 := by decide
  have a3 : VG.X86.arg VG.Proof.AesSiv.X86.initSat 3 = 0x4000 := by decide
  have e : argAddr VG.Proof.AesSiv.X86.initSat 0 = 0x8004 := by decide
  have esp : initSat.gpr .esp = 0x8000 := rfl
  sig_implies_sat [Proof.AesSiv.initScratchContract, Proof.AesSiv.initScratchSig, Spec.Siv.initPre,
    Spec.Siv.initPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] [a0, a1, a2, a3, e, esp] using VG.Proof.AesSiv.X86.initSat

theorem init_verified :
    Verified X86.target (initCore v.expand v.callee v.suffix) (Proof.AesSiv.initScratchContract X86.abi 48) := by
  refine X86.Verified.narrowTo (k := VG.Proof.AesSiv.X86.initX86)
    ⟨fun s hs => VG.Proof.AesSiv.X86.init_wp v hs, VG.Proof.AesSiv.X86.init_ct v, initSat_pre.elim fun s hs => ⟨_, (VG.Proof.AesSiv.X86.initPre_of hs).1⟩⟩
    VG.Proof.AesSiv.X86.initRd VG.Proof.AesSiv.X86.initWr (fun s hs => (VG.Proof.AesSiv.X86.initPre_of hs).1) (fun s hs => ?_) (fun s hs => ?_) (fun s s' hs hq => ?_)
    (fun s₁ s₂ h₁ h₂ hp => ?_) VG.Proof.AesSiv.X86.initSat_pre
  · obtain ⟨-, hrd, hwr⟩ := VG.Proof.AesSiv.X86.initPre_of hs
    rw [hrd, hwr]
    exact Covers.of_mem fun r hr => by
      simp only [VG.Proof.AesSiv.X86.initRd, VG.Proof.AesSiv.X86.initWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp
  · obtain ⟨-, -, hwr⟩ := VG.Proof.AesSiv.X86.initPre_of hs
    rw [hwr]
    exact Covers.of_mem fun r hr => by
      simp only [VG.Proof.AesSiv.X86.initWr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp
  · sig_post [Proof.AesSiv.initScratchContract, Proof.AesSiv.initScratchSig, Spec.Siv.initPost, X86.abi,
      X86.argSlots, X86.argVal, X86.argBytes]
    exact hq
  · sig_pub [Proof.AesSiv.initScratchContract, Proof.AesSiv.initScratchSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes] at hp
    sig_split hp
    rename_i q0 q1 q2 q3
    refine ⟨q0, fun i hi => ?_⟩
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
    · exact q1
    · exact q2
    · exact q3
    · exact hp

theorem init_noEsp : (initCore v.expand v.callee v.suffix).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [initCore, Impl.CmacAes.Stream.X86.call4, Code.allInstrs, VG.Proof.AesSiv.X86.noEsp_of v.expandNosp,
    VG.Proof.AesSiv.X86.noEsp_of (Proof.CmacAes.X86.subkeys_nosp v)]
  decide +kernel

theorem init_stackUse : stackUse (initCore v.expand v.callee v.suffix) ≤ 48 := by
  simp only [initCore, Impl.CmacAes.Stream.X86.call4, stackUse, v.expandStack, Proof.CmacAes.X86.subkeys_stack v]
  decide +kernel

/-- A state satisfying `vg_aes_siv_init`'s precondition, without the
working space. -/
def initFrameSat : State := { VG.Proof.AesSiv.X86.initSat with
                                           rd := [⟨0x1000, 32⟩], wr := [⟨0x2000, 512⟩, ⟨0x8004, 12⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Siv.initContract X86.abi 2628).pre s := by
  implies_sat [Spec.Siv.initContract, Spec.Siv.initSig, Spec.Siv.initPre, Spec.Siv.initPost,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [initFrameSat, initSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using VG.Proof.AesSiv.X86.initFrameSat

/-- `initCore` in a frame of 2580 bytes: the return address, the three
argument slots and the 2560 bytes of working space. -/
theorem init_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2580 3 (initCore v.expand v.callee v.suffix))
      (Spec.Siv.initContract X86.abi 2628) :=
  X86.Verified.stackScratch (sig := Spec.Siv.initSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Spec.Siv.initPre X86.abi.ptrBits) (post := Spec.Siv.initPost X86.abi.ptrBits)
    (wa := true) (stack := 48) (bytes := 2580) (VG.Proof.AesSiv.X86.init_verified v) (by decide) (VG.Proof.AesSiv.X86.init_noEsp v)
    (VG.Proof.AesSiv.X86.init_stackUse v) (Proof.AesSiv.initPre_local _) (Proof.AesSiv.initPost_local _) VG.Proof.AesSiv.X86.initFrameSat_pre

/-! ## The stack pointer -/

theorem init_spSafe : (initCore v.expand v.callee v.suffix).all (fun i => !isa.writesSp i) = true := by
  simp only [initCore, Impl.CmacAes.Stream.X86.call4, Code.all, v.expandSpSafe, Proof.CmacAes.X86.subkeys_spSafe v,
    Bool.and_true]
  decide +kernel

theorem encrypt_spSafe : (encrypt v.callee v.suffix).all (fun i => !isa.writesSp i) = true := by
  simp only [encrypt, encS2v, sivEntry, Impl.AesGcm.X86.entry, start, s2vAds, cmacOf, cmacPre, updCall, finCall,
    Impl.CmacAes.Stream.X86.call6, finish, shortTail, copyN, shortMac, longTail, longMac, ctr, ctrWhole, ctrTail,
    ctrCall, sivOut, Code.all, Proof.CmacAes.X86.update_spSafe v, Proof.CmacAes.X86.finalize_spSafe v, v.spSafe,
    Bool.and_true]
  decide +kernel

theorem decrypt_spSafe : (decrypt v.callee v.suffix).all (fun i => !isa.writesSp i) = true := by
  simp only [decrypt, encS2v, sivEntry, Impl.AesGcm.X86.entry, start, s2vAds, cmacOf, cmacPre, updCall, finCall,
    Impl.CmacAes.Stream.X86.call6, finish, shortTail, copyN, shortMac, longTail, longMac, ctr, ctrWhole, ctrTail,
    ctrCall, mask, sivIn, Code.all, Proof.CmacAes.X86.update_spSafe v, Proof.CmacAes.X86.finalize_spSafe v, v.spSafe,
    Bool.and_true]
  decide +kernel

end VG.Proof.AesSiv.X86

end
