module

import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Arm.Dispatch
import VerifiedGarbage.Proof.Dsa.OutputBytes
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Dsa.Arm.Body
public import VerifiedGarbage.Proof.Dsa.Arm.Shape
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Weierstrass.Words
public import VerifiedGarbage.Impl.Dsa.Arm.Entry
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Ws
public import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Arm.Reduce
public import VerifiedGarbage.Spec.Dsa.SignVerify
public import VerifiedGarbage.Proof.Framework.PowLit

/-! ### `Dsa.Arm.Env`, which this module and modules that import it used -/

section

/-! ### `Dsa.Arm.Contract`, which this module and modules that import it used -/

section

/-!
# DSA on 32-bit ARM: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The facts of
`Spec.Dsa.signContract` and `Spec.Dsa.verifyContract` for 32-bit ARM, by
name. `vg_dsa_sign(out, out_len, key, key_len, p_len, nonce, q_len, digest,
digest_len, scratch, scratch_len)` has its first four arguments in `r0`–`r3`
and the others on the stack (`arg`, AAPCS); `vg_dsa_verify(key, key_len,
p_len, q_len, signature, signature_len, digest, digest_len, scratch,
scratch_len)` likewise. The result is in `r0` (the low word of `r1:r0`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm

/-- The `i`-th argument on the stack. -/
abbrev arg (s : State) (i : Nat) : BitVec 32 := stackArg s i

/-! ## Signing -/

/-- What `vg_dsa_sign` needs: `(out = r0, out_len = r1, key = r2, key_len = r3,
p_len = [sp], nonce = [sp + 4], q_len = [sp + 8], digest = [sp + 12],
digest_len = [sp + 16], scratch = [sp + 20], scratch_len = [sp + 24])`. -/
def signPre (s : State) : Prop :=
  let out : Region := ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
  let key : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
  let nonce : Region := ⟨State.addr (arg s 1), (arg s 2).toNat⟩
  let digest : Region := ⟨State.addr (arg s 3), (arg s 4).toNat⟩
  let scratch : Region := ⟨State.addr (arg s 5), (arg s 6).toNat * 8⟩
  let args : Region := ⟨State.addr s.sp, 28⟩
  s.sp.toNat + 28 ≤ 2 ^ 32 ∧ s.rd = [key, nonce, digest, args] ∧ s.wr = [out, scratch] ∧
    out.Disjoint key ∧ out.Disjoint nonce ∧ out.Disjoint digest ∧ out.Disjoint scratch ∧ out.Disjoint args ∧
    key.Disjoint scratch ∧ nonce.Disjoint scratch ∧ digest.Disjoint scratch ∧ scratch.Disjoint args ∧
    (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32 ∧
    (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 32 ∧ (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧
    (arg s 5).toNat + (arg s 6).toNat * 8 ≤ 2 ^ 32 ∧
    Spec.Dsa.lengthsValid (arg s 0).toNat (arg s 2).toNat ∧ (s.gpr .r1).toNat = 2 * (arg s 2).toNat ∧
    (s.gpr .r3).toNat = 3 * (arg s 0).toNat + 2 * (arg s 2).toNat ∧
    Spec.Dsa.scratchWords (arg s 0).toNat ≤ (arg s 6).toNat

/-- The result of a signing attempt in a state. -/
abbrev signRes (s : State) : Option (List Byte) :=
  Spec.Dsa.signBytes (arg s 0).toNat (arg s 2).toNat
    (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
    (Spec.Rsa.bytesAt s.mem (State.addr (arg s 1)) (arg s 2).toNat)
    (Spec.Rsa.bytesAt s.mem (State.addr (arg s 3)) (arg s 4).toNat)

/-- What signing may leak: the public bytes of the key and whether it succeeds. -/
abbrev signLeak (s : State) : List Nat :=
  Spec.Dsa.publicBytesLeak (arg s 0).toNat (arg s 2).toNat
      (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat) ++
    [Spec.Dsa.signStatus (signRes s)]

def signArm : Contract isa where
  pre := signPre
  post s s' := (BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0)).toNat = Spec.Dsa.signStatus (signRes s) ∧
    Spec.Rsa.bytesAt s'.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat =
      (signRes s).getD (List.replicate (s.gpr .r1).toNat 0)
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ signLeak s₁ = signLeak s₂ ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧
    s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ ∀ i < 7, arg s₁ i = arg s₂ i

/-! ## Verification -/

/-- What `vg_dsa_verify` needs: `(key = r0, key_len = r1, p_len = r2,
q_len = r3, signature = [sp], signature_len = [sp + 4], digest = [sp + 8],
digest_len = [sp + 12], scratch = [sp + 16], scratch_len = [sp + 20])`. -/
def verifyPre (s : State) : Prop :=
  let key : Region := ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
  let sig : Region := ⟨State.addr (arg s 0), (arg s 1).toNat⟩
  let digest : Region := ⟨State.addr (arg s 2), (arg s 3).toNat⟩
  let scratch : Region := ⟨State.addr (arg s 4), (arg s 5).toNat * 8⟩
  let args : Region := ⟨State.addr s.sp, 24⟩
  s.sp.toNat + 24 ≤ 2 ^ 32 ∧ s.rd = [key, sig, digest, args] ∧ s.wr = [scratch] ∧
    key.Disjoint scratch ∧ sig.Disjoint scratch ∧ digest.Disjoint scratch ∧ scratch.Disjoint args ∧
    (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32 ∧ (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32 ∧
    (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32 ∧ (arg s 4).toNat + (arg s 5).toNat * 8 ≤ 2 ^ 32 ∧
    Spec.Dsa.lengthsValid (s.gpr .r2).toNat (s.gpr .r3).toNat ∧
    (s.gpr .r1).toNat = 3 * (s.gpr .r2).toNat + (s.gpr .r3).toNat ∧ (arg s 1).toNat = 2 * (s.gpr .r3).toNat ∧
    Spec.Dsa.scratchWords (s.gpr .r2).toNat ≤ (arg s 5).toNat

/-- The result of a verification in a state. -/
abbrev verifyRes (s : State) : Bool :=
  Spec.Dsa.verifyBytes (s.gpr .r2).toNat (s.gpr .r3).toNat
    (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat)
    (Spec.Rsa.bytesAt s.mem (State.addr (arg s 0)) (arg s 1).toNat)
    (Spec.Rsa.bytesAt s.mem (State.addr (arg s 2)) (arg s 3).toNat)

/-- What verification may leak: the public key's bytes and the result. -/
abbrev verifyLeak (s : State) : List Nat :=
  Spec.Dsa.publicBytesLeak (s.gpr .r2).toNat (s.gpr .r3).toNat
      (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat) ++
    [if verifyRes s then 1 else 0]

def verifyArm : Contract isa where
  pre := verifyPre
  post s s' := (BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0)).toNat = if verifyRes s then 1 else 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ verifyLeak s₁ = verifyLeak s₂ ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧
    s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ ∀ i < 6, arg s₁ i = arg s₂ i

end VG.Proof.Dsa.Arm

end

end

/-! ### `Dsa.Arm.Install`, which this module and modules that import it used -/

section

/-! ### `Dsa.Arm.EntrySave`, which this module and modules that import it used -/

section

/-!
# DSA on 32-bit ARM: saving the registers and the arguments

The entry saves `r4`–`r11` and `lr` at offset 128 of the working space
(`save_ok`), the arguments the bodies use at their fields (`signArgs_ok`,
`verifyArgs_ok`), and the pointers to the key's components, each after the
one before (`keyPointers_ok`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov wp_str wp_ldr wp_dp wp_movw op2_imm op2_reg dpVal)

/-- `t = ` the stack argument `i`. -/
theorem wp_ldrSp {s : State} {is : List Instr} {Q : State → Prop} {t : Reg} {i : Nat} (hi : 4 * i < 4096)
    (hin : InRegions (s.rd ++ s.wr) (stackArgAddr s i) 4)
    (k : ∀ s', Upd s s' t (stackArg s i) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldrSp t (4 * i) :: is)) s Q := by
  have e : stackArgAddr s i = State.addr (s.sp + BitVec.ofNat 32 (4 * i)) := rfl
  rw [e] at hin
  exact VG.Proof.X25519.Arm.WP.cons (by simp only [reduceExec, hi, ite_true, State.load32, hin, Option.map_some]; rfl)
    (k _ (VG.Proof.X25519.Arm.Upd.setReg _ _ _))

/-- `[r12 + d] = r`. -/
theorem wp_str12 {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {is : List Instr}
    {Q : State → Prop} {r : Reg} {d : Nat} (hd : d < 4096) (hd' : d + 4 ≤ size)
    (k : ∀ s', Mupd s s' (s.mem.writeW (off base d) (s.gpr r)) → WP isa (.block is) s' Q) :
    WP isa (.block (.str r .r12 d :: is)) s Q :=
  wp_str hd (hs.ea12 (by omega_arith)) (hs.write hd') k

theorem readW_off_ne {m : Mem} {base : Addr} {d e : Nat} (h : d + 4 ≤ e ∨ e + 4 ≤ d) (hd : d + 4 ≤ 2 ^ 64)
    (he : e + 4 ≤ 2 ^ 64) (v : BitVec 32) :
    (m.writeW (off base e) v).readW (off base d) 32 = m.readW (off base d) 32 :=
  Mem.readW_writeW_sep (Offset.sep base h hd he) (by decide)

theorem readW_off_self (m : Mem) (base : Addr) (d : Nat) (v : BitVec 32) :
    (m.writeW (off base d) v).readW (off base d) 32 = v :=
  Mem.readW_writeW_self32 _ _ _

/-- The registers saved by `save`, at `[128 + 4i]`. -/
theorem save_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (hz : 164 ≤ size) :
    WP isa (.block Entry.save) s fun t =>
      (∀ i < 9, t.mem.readW (off base (128 + 4 * i)) 32 = s.gpr (Entry.savedRegs.getD i .r0)) ∧
      Rest [] s t ∧ Outside base 128 36 s.mem t.mem := by
  have nw := hs.nowrap
  show WP isa (.block [.str .r4 .r12 128, .str .r5 .r12 132, .str .r6 .r12 136, .str .r7 .r12 140,
    .str .r8 .r12 144, .str .r9 .r12 148, .str .r10 .r12 152, .str .r11 .r12 156, .str .lr .r12 160]) s _
  refine wp_str12 hs (by decide) (by omega_arith) fun s₁ m₁ => ?_
  obtain w₁ := hs.of_mupd m₁
  refine wp_str12 w₁ (by decide) (by omega_arith) fun s₂ m₂ => ?_
  obtain w₂ := w₁.of_mupd m₂
  refine wp_str12 w₂ (by decide) (by omega_arith) fun s₃ m₃ => ?_
  obtain w₃ := w₂.of_mupd m₃
  refine wp_str12 w₃ (by decide) (by omega_arith) fun s₄ m₄ => ?_
  obtain w₄ := w₃.of_mupd m₄
  refine wp_str12 w₄ (by decide) (by omega_arith) fun s₅ m₅ => ?_
  obtain w₅ := w₄.of_mupd m₅
  refine wp_str12 w₅ (by decide) (by omega_arith) fun s₆ m₆ => ?_
  obtain w₆ := w₅.of_mupd m₆
  refine wp_str12 w₆ (by decide) (by omega_arith) fun s₇ m₇ => ?_
  obtain w₇ := w₆.of_mupd m₇
  refine wp_str12 w₇ (by decide) (by omega_arith) fun s₈ m₈ => ?_
  obtain w₈ := w₇.of_mupd m₈
  refine wp_str12 w₈ (by decide) (by omega_arith) fun t m₉ => WP.block_nil ⟨?_, ?_, ?_⟩
  · have mt : t.mem = ((((((((s.mem.writeW (off base 128) (s.gpr .r4)).writeW (off base 132) (s.gpr .r5)).writeW
        (off base 136) (s.gpr .r6)).writeW (off base 140) (s.gpr .r7)).writeW (off base 144) (s.gpr .r8)).writeW
        (off base 148) (s.gpr .r9)).writeW (off base 152) (s.gpr .r10)).writeW (off base 156) (s.gpr .r11)).writeW
        (off base 160) (s.gpr .lr) := by
      rw [m₉.mem, m₈.mem, m₇.mem, m₆.mem, m₅.mem, m₄.mem, m₃.mem, m₂.mem, m₁.mem, m₈.gpr, m₇.gpr, m₆.gpr, m₅.gpr,
        m₄.gpr, m₃.gpr, m₂.gpr, m₁.gpr]
    intro i hi
    rw [mt]
    rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := omega_arith) only [readW_off_ne, readW_off_self, Entry.savedRegs, List.getD_cons_zero,
      List.getD_cons_succ, Nat.mul_zero, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd]
  · exact ((((((((m₁.rest _).trans (m₂.rest _)).trans (m₃.rest _)).trans (m₄.rest _)).trans (m₅.rest _)).trans
      (m₆.rest _)).trans (m₇.rest _)).trans (m₈.rest _)).trans (m₉.rest _)
  · have o : ∀ {m : Mem} {d : Nat} (v : BitVec 32), 128 ≤ d → d + 4 ≤ 164 → Outside base 128 36 m (m.writeW (off base d) v) :=
      fun v h₁ h₂ => (writeW32_outside _ _ _ (by omega_arith)).mono h₁ (by omega_arith)
    rw [m₉.mem]
    refine (Outside.trans ?_ (o _ (by decide) (by decide)))
    rw [m₈.mem]; refine (Outside.trans ?_ (o _ (by decide) (by decide)))
    rw [m₇.mem]; refine (Outside.trans ?_ (o _ (by decide) (by decide)))
    rw [m₆.mem]; refine (Outside.trans ?_ (o _ (by decide) (by decide)))
    rw [m₅.mem]; refine (Outside.trans ?_ (o _ (by decide) (by decide)))
    rw [m₄.mem]; refine (Outside.trans ?_ (o _ (by decide) (by decide)))
    rw [m₃.mem]; refine (Outside.trans ?_ (o _ (by decide) (by decide)))
    rw [m₂.mem]; refine (Outside.trans ?_ (o _ (by decide) (by decide)))
    rw [m₁.mem]; exact o _ (by decide) (by decide)

/-- The stack arguments are apart from the header. -/
def ArgsApart (s : State) (base : Addr) (n : Nat) : Prop :=
  ∀ i < n, ∀ d, d + 4 ≤ 164 → Mem.Sep (stackArgAddr s i) 4 (off base d) 4

theorem stackArg_mupd {s s' : State} {base : Addr} {d n i : Nat} {v : BitVec 32}
    (m : Mupd s s' (s.mem.writeW (off base d) v)) (ha : ArgsApart s base n) (hi : i < n) (hd : d + 4 ≤ 164) :
    stackArg s' i = stackArg s i := by
  unfold stackArg
  rw [show stackArgAddr s' i = stackArgAddr s i by simp only [stackArgAddr, m.sp], m.mem]
  exact Mem.readW_writeW_sep (ha i hi d hd) (by decide)

theorem ArgsApart.mupd {s s' : State} {base : Addr} {d n : Nat} {v : BitVec 32}
    (m : Mupd s s' (s.mem.writeW (off base d) v)) (ha : ArgsApart s base n) : ArgsApart s' base n :=
  fun i hi e he => by rw [show stackArgAddr s' i = stackArgAddr s i by simp only [stackArgAddr, m.sp]]; exact ha i hi e he

theorem ArgsApart.upd {s s' : State} {base : Addr} {n : Nat} {r : Reg} {v : BitVec 32}
    (u : Upd s s' r v) (ha : ArgsApart s base n) : ArgsApart s' base n :=
  fun i hi e he => by rw [show stackArgAddr s' i = stackArgAddr s i by simp only [stackArgAddr, u.sp]]; exact ha i hi e he

theorem stackArg_upd {s s' : State} {r : Reg} {v : BitVec 32} (u : Upd s s' r v) (i : Nat) :
    stackArg s' i = stackArg s i := by
  unfold stackArg; rw [show stackArgAddr s' i = stackArgAddr s i by simp only [stackArgAddr, u.sp], u.mem]

/-- The readable stack arguments. -/
def ArgsRead (s : State) (n : Nat) : Prop := ∀ i < n, InRegions (s.rd ++ s.wr) (stackArgAddr s i) 4

theorem ArgsRead.keep {s s' : State} {n : Nat} (h : ArgsRead s n) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) : ArgsRead s' n :=
  fun i hi => by rw [hrd, hwr, show stackArgAddr s' i = stackArgAddr s i by simp only [stackArgAddr, hsp]]; exact h i hi

/-- A stored word, then one stored apart. -/
theorem stored {m : Mem} {base : Addr} {d e : Nat} (h : d + 4 ≤ e ∨ e + 4 ≤ d) (hd : d + 4 ≤ 2 ^ 64)
    (he : e + 4 ≤ 2 ^ 64) {v : BitVec 32} (hm : m.readW (off base d) 32 = v) (w : BitVec 32) :
    (m.writeW (off base e) w).readW (off base d) 32 = v := by
  rw [readW_off_ne h hd he, hm]

theorem outside_word {m : Mem} {base : Addr} {o n d : Nat} (h₁ : o ≤ d) (h₂ : d + 4 ≤ o + n) (hb : o + n ≤ 2 ^ 64)
    (v : BitVec 32) : Outside base o n m (m.writeW (off base d) v) :=
  (writeW32_outside _ _ _ (by omega_arith)).mono h₁ h₂

/-- The arguments of signing at their fields. -/
theorem signArgs_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (hz : 164 ≤ size)
    (hr : ArgsRead s 7) (ha : ArgsApart s base 7) :
    WP isa (.block (Entry.signArguments.flatMap Entry.saveArgument)) s fun t =>
      t.mem.readW (off base 96) 32 = s.gpr .r0 ∧ t.mem.readW (off base 64) 32 = s.gpr .r2 ∧
      t.mem.readW (off base 100) 32 = stackArg s 0 ∧ t.mem.readW (off base 88) 32 = stackArg s 1 ∧
      t.mem.readW (off base 104) 32 = stackArg s 2 ∧ t.mem.readW (off base 92) 32 = stackArg s 3 ∧
      t.mem.readW (off base 108) 32 = stackArg s 4 ∧
      Rest [.r4] s t ∧ Outside base 64 48 s.mem t.mem ∧ ∀ i < 7, stackArg t i = stackArg s i := by
  have nw := hs.nowrap
  show WP isa (.block [.str .r0 .r12 96, .str .r2 .r12 64, .ldrSp .r4 (4 * 0), .str .r4 .r12 100,
    .ldrSp .r4 (4 * 1), .str .r4 .r12 88, .ldrSp .r4 (4 * 2), .str .r4 .r12 104,
    .ldrSp .r4 (4 * 3), .str .r4 .r12 92, .ldrSp .r4 (4 * 4), .str .r4 .r12 108]) s _
  refine wp_str12 hs (by decide) (by omega_arith) fun s₁ m₁ => ?_
  obtain a₁ := ha.mupd m₁
  refine wp_str12 (hs.of_mupd m₁) (by decide) (by omega_arith) fun s₂ m₂ => ?_
  obtain a₂ := a₁.mupd m₂
  obtain w₂ := (hs.of_mupd m₁).of_mupd m₂
  obtain r₂ : ArgsRead s₂ 7 := (hr.keep m₁.rd m₁.wr m₁.sp).keep m₂.rd m₂.wr m₂.sp
  obtain A₂ : ∀ i < 7, stackArg s₂ i = stackArg s i := fun i hi => by
    rw [stackArg_mupd m₂ a₁ hi (by decide), stackArg_mupd m₁ ha hi (by decide)]
  refine wp_ldrSp (by decide) (r₂ 0 (by decide)) fun s₃ u₃ => wp_str12 (w₂.of_upd u₃ (by decide)) (by decide)
    (by omega_arith) fun s₄ m₄ => ?_
  obtain a₄ := (a₂.upd u₃).mupd m₄
  obtain w₄ := (w₂.of_upd u₃ (by decide)).of_mupd m₄
  obtain r₄ : ArgsRead s₄ 7 := (r₂.keep u₃.rd u₃.wr u₃.sp).keep m₄.rd m₄.wr m₄.sp
  obtain A₄ : ∀ i < 7, stackArg s₄ i = stackArg s i := fun i hi => by
    rw [stackArg_mupd m₄ (a₂.upd u₃) hi (by decide), stackArg_upd u₃, A₂ i hi]
  refine wp_ldrSp (by decide) (r₄ 1 (by decide)) fun s₅ u₅ => wp_str12 (w₄.of_upd u₅ (by decide)) (by decide)
    (by omega_arith) fun s₆ m₆ => ?_
  obtain a₆ := (a₄.upd u₅).mupd m₆
  obtain w₆ := (w₄.of_upd u₅ (by decide)).of_mupd m₆
  obtain r₆ : ArgsRead s₆ 7 := (r₄.keep u₅.rd u₅.wr u₅.sp).keep m₆.rd m₆.wr m₆.sp
  obtain A₆ : ∀ i < 7, stackArg s₆ i = stackArg s i := fun i hi => by
    rw [stackArg_mupd m₆ (a₄.upd u₅) hi (by decide), stackArg_upd u₅, A₄ i hi]
  refine wp_ldrSp (by decide) (r₆ 2 (by decide)) fun s₇ u₇ => wp_str12 (w₆.of_upd u₇ (by decide)) (by decide)
    (by omega_arith) fun s₈ m₈ => ?_
  obtain a₈ := (a₆.upd u₇).mupd m₈
  obtain w₈ := (w₆.of_upd u₇ (by decide)).of_mupd m₈
  obtain r₈ : ArgsRead s₈ 7 := (r₆.keep u₇.rd u₇.wr u₇.sp).keep m₈.rd m₈.wr m₈.sp
  obtain A₈ : ∀ i < 7, stackArg s₈ i = stackArg s i := fun i hi => by
    rw [stackArg_mupd m₈ (a₆.upd u₇) hi (by decide), stackArg_upd u₇, A₆ i hi]
  refine wp_ldrSp (by decide) (r₈ 3 (by decide)) fun s₉ u₉ => wp_str12 (w₈.of_upd u₉ (by decide)) (by decide)
    (by omega_arith) fun s₁₀ m₁₀ => ?_
  obtain a₁₀ := (a₈.upd u₉).mupd m₁₀
  obtain w₁₀ := (w₈.of_upd u₉ (by decide)).of_mupd m₁₀
  obtain r₁₀ : ArgsRead s₁₀ 7 := (r₈.keep u₉.rd u₉.wr u₉.sp).keep m₁₀.rd m₁₀.wr m₁₀.sp
  obtain A₁₀ : ∀ i < 7, stackArg s₁₀ i = stackArg s i := fun i hi => by
    rw [stackArg_mupd m₁₀ (a₈.upd u₉) hi (by decide), stackArg_upd u₉, A₈ i hi]
  refine wp_ldrSp (by decide) (r₁₀ 4 (by decide)) fun s₁₁ u₁₁ => wp_str12 (w₁₀.of_upd u₁₁ (by decide)) (by decide)
    (by omega_arith) fun t m₁₂ => WP.block_nil ?_
  obtain A : ∀ i < 7, stackArg t i = stackArg s i := fun i hi => by
    rw [stackArg_mupd m₁₂ (a₁₀.upd u₁₁) hi (by decide), stackArg_upd u₁₁, A₁₀ i hi]
  -- The words, each stored once.
  obtain v₁ : s₁.mem.readW (off base 96) 32 = s.gpr .r0 := by rw [m₁.mem]; exact readW_off_self _ _ _ _
  obtain v₂ : s₂.mem.readW (off base 64) 32 = s.gpr .r2 := by rw [m₂.mem, m₁.gpr]; exact readW_off_self _ _ _ _
  obtain v₄ : s₄.mem.readW (off base 100) 32 = stackArg s 0 := by
    rw [m₄.mem, u₃.gpr, A₂ 0 (by decide)]; exact readW_off_self _ _ _ _
  obtain v₆ : s₆.mem.readW (off base 88) 32 = stackArg s 1 := by
    rw [m₆.mem, u₅.gpr, A₄ 1 (by decide)]; exact readW_off_self _ _ _ _
  obtain v₈ : s₈.mem.readW (off base 104) 32 = stackArg s 2 := by
    rw [m₈.mem, u₇.gpr, A₆ 2 (by decide)]; exact readW_off_self _ _ _ _
  obtain v₁₀ : s₁₀.mem.readW (off base 92) 32 = stackArg s 3 := by
    rw [m₁₀.mem, u₉.gpr, A₈ 3 (by decide)]; exact readW_off_self _ _ _ _
  obtain v₁₂ : t.mem.readW (off base 108) 32 = stackArg s 4 := by
    rw [m₁₂.mem, u₁₁.gpr, A₁₀ 4 (by decide)]; exact readW_off_self _ _ _ _
  -- Later stores keep them.
  obtain k₁₂ : ∀ {d v}, d + 4 ≤ 108 → s₁₀.mem.readW (off base d) 32 = v → t.mem.readW (off base d) 32 = v :=
    fun hd h => by rw [m₁₂.mem, u₁₁.mem]; exact stored (.inl hd) (by omega_arith) (by omega_arith) h _
  obtain k₁₀ : ∀ {d v}, (d + 4 ≤ 92 ∨ 96 ≤ d) → d + 4 ≤ 164 → s₈.mem.readW (off base d) 32 = v →
      s₁₀.mem.readW (off base d) 32 = v :=
    fun hd hd' h => by rw [m₁₀.mem, u₉.mem]; exact stored hd (by omega_arith) (by omega_arith) h _
  obtain k₈ : ∀ {d v}, (d + 4 ≤ 104 ∨ 108 ≤ d) → d + 4 ≤ 164 → s₆.mem.readW (off base d) 32 = v →
      s₈.mem.readW (off base d) 32 = v :=
    fun hd hd' h => by rw [m₈.mem, u₇.mem]; exact stored hd (by omega_arith) (by omega_arith) h _
  obtain k₆ : ∀ {d v}, (d + 4 ≤ 88 ∨ 92 ≤ d) → d + 4 ≤ 164 → s₄.mem.readW (off base d) 32 = v →
      s₆.mem.readW (off base d) 32 = v :=
    fun hd hd' h => by rw [m₆.mem, u₅.mem]; exact stored hd (by omega_arith) (by omega_arith) h _
  obtain k₄ : ∀ {d v}, (d + 4 ≤ 100 ∨ 104 ≤ d) → d + 4 ≤ 164 → s₂.mem.readW (off base d) 32 = v →
      s₄.mem.readW (off base d) 32 = v :=
    fun hd hd' h => by rw [m₄.mem, u₃.mem]; exact stored hd (by omega_arith) (by omega_arith) h _
  obtain k₂ : ∀ {d v}, (d + 4 ≤ 64 ∨ 68 ≤ d) → d + 4 ≤ 164 → s₁.mem.readW (off base d) 32 = v →
      s₂.mem.readW (off base d) 32 = v :=
    fun hd hd' h => by rw [m₂.mem]; exact stored hd (by omega_arith) (by omega_arith) h _
  refine ⟨k₁₂ (by decide) (k₁₀ (by decide) (by decide) (k₈ (by decide) (by decide) (k₆ (by decide) (by decide)
      (k₄ (by decide) (by decide) (k₂ (by decide) (by decide) v₁))))),
    k₁₂ (by decide) (k₁₀ (by decide) (by decide) (k₈ (by decide) (by decide) (k₆ (by decide) (by decide)
      (k₄ (by decide) (by decide) v₂)))),
    k₁₂ (by decide) (k₁₀ (by decide) (by decide) (k₈ (by decide) (by decide) (k₆ (by decide) (by decide) v₄))),
    k₁₂ (by decide) (k₁₀ (by decide) (by decide) (k₈ (by decide) (by decide) v₆)),
    k₁₂ (by decide) (k₁₀ (by decide) (by decide) v₈), k₁₂ (by decide) v₁₀, v₁₂, ?_, ?_, A⟩
  · exact (((((((((((m₁.rest _).trans (m₂.rest _)).trans (u₃.rest (by decide))).trans (m₄.rest _)).trans
      (u₅.rest (by decide))).trans (m₆.rest _)).trans (u₇.rest (by decide))).trans (m₈.rest _)).trans
      (u₉.rest (by decide))).trans (m₁₀.rest _)).trans (u₁₁.rest (by decide))).trans (m₁₂.rest _)
  · rw [m₁₂.mem, u₁₁.mem, m₁₀.mem, u₉.mem, m₈.mem, u₇.mem, m₆.mem, u₅.mem, m₄.mem, u₃.mem, m₂.mem, m₁.mem]
    exact (((((((outside_word (by decide) (by decide) (by omega_arith) _).trans
      (outside_word (by decide) (by decide) (by omega_arith) _)).trans (outside_word (by decide) (by decide) (by omega_arith) _)).trans
      (outside_word (by decide) (by decide) (by omega_arith) _)).trans (outside_word (by decide) (by decide) (by omega_arith) _)).trans
      (outside_word (by decide) (by decide) (by omega_arith) _)).trans (outside_word (by decide) (by decide) (by omega_arith) _))

/-- The arguments of verification at their fields. -/
theorem verifyArgs_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (hz : 164 ≤ size)
    (hr : ArgsRead s 6) (ha : ArgsApart s base 6) :
    WP isa (.block (Entry.verifyArguments.flatMap Entry.saveArgument)) s fun t =>
      t.mem.readW (off base 64) 32 = s.gpr .r0 ∧ t.mem.readW (off base 100) 32 = s.gpr .r2 ∧
      t.mem.readW (off base 104) 32 = s.gpr .r3 ∧ t.mem.readW (off base 84) 32 = stackArg s 0 ∧
      t.mem.readW (off base 92) 32 = stackArg s 2 ∧ t.mem.readW (off base 108) 32 = stackArg s 3 ∧
      Rest [.r4] s t ∧ Outside base 64 48 s.mem t.mem ∧ ∀ i < 6, stackArg t i = stackArg s i := by
  have nw := hs.nowrap
  show WP isa (.block [.str .r0 .r12 64, .str .r2 .r12 100, .str .r3 .r12 104, .ldrSp .r4 (4 * 0), .str .r4 .r12 84,
    .ldrSp .r4 (4 * 2), .str .r4 .r12 92, .ldrSp .r4 (4 * 3), .str .r4 .r12 108]) s _
  refine wp_str12 hs (by decide) (by omega_arith) fun s₁ m₁ => ?_
  refine wp_str12 (hs.of_mupd m₁) (by decide) (by omega_arith) fun s₂ m₂ => ?_
  refine wp_str12 ((hs.of_mupd m₁).of_mupd m₂) (by decide) (by omega_arith) fun s₃ m₃ => ?_
  obtain a₃ := ((ha.mupd m₁).mupd m₂).mupd m₃
  obtain w₃ := ((hs.of_mupd m₁).of_mupd m₂).of_mupd m₃
  obtain r₃ : ArgsRead s₃ 6 := ((hr.keep m₁.rd m₁.wr m₁.sp).keep m₂.rd m₂.wr m₂.sp).keep m₃.rd m₃.wr m₃.sp
  obtain A₃ : ∀ i < 6, stackArg s₃ i = stackArg s i := fun i hi => by
    rw [stackArg_mupd m₃ ((ha.mupd m₁).mupd m₂) hi (by decide), stackArg_mupd m₂ (ha.mupd m₁) hi (by decide),
      stackArg_mupd m₁ ha hi (by decide)]
  refine wp_ldrSp (by decide) (r₃ 0 (by decide)) fun s₄ u₄ => wp_str12 (w₃.of_upd u₄ (by decide)) (by decide)
    (by omega_arith) fun s₅ m₅ => ?_
  obtain a₅ := (a₃.upd u₄).mupd m₅
  obtain w₅ := (w₃.of_upd u₄ (by decide)).of_mupd m₅
  obtain r₅ : ArgsRead s₅ 6 := (r₃.keep u₄.rd u₄.wr u₄.sp).keep m₅.rd m₅.wr m₅.sp
  obtain A₅ : ∀ i < 6, stackArg s₅ i = stackArg s i := fun i hi => by
    rw [stackArg_mupd m₅ (a₃.upd u₄) hi (by decide), stackArg_upd u₄, A₃ i hi]
  refine wp_ldrSp (by decide) (r₅ 2 (by decide)) fun s₆ u₆ => wp_str12 (w₅.of_upd u₆ (by decide)) (by decide)
    (by omega_arith) fun s₇ m₇ => ?_
  obtain a₇ := (a₅.upd u₆).mupd m₇
  obtain w₇ := (w₅.of_upd u₆ (by decide)).of_mupd m₇
  obtain r₇ : ArgsRead s₇ 6 := (r₅.keep u₆.rd u₆.wr u₆.sp).keep m₇.rd m₇.wr m₇.sp
  obtain A₇ : ∀ i < 6, stackArg s₇ i = stackArg s i := fun i hi => by
    rw [stackArg_mupd m₇ (a₅.upd u₆) hi (by decide), stackArg_upd u₆, A₅ i hi]
  refine wp_ldrSp (by decide) (r₇ 3 (by decide)) fun s₈ u₈ => wp_str12 (w₇.of_upd u₈ (by decide)) (by decide)
    (by omega_arith) fun t m₉ => WP.block_nil ?_
  obtain A : ∀ i < 6, stackArg t i = stackArg s i := fun i hi => by
    rw [stackArg_mupd m₉ (a₇.upd u₈) hi (by decide), stackArg_upd u₈, A₇ i hi]
  obtain v₁ : s₁.mem.readW (off base 64) 32 = s.gpr .r0 := by rw [m₁.mem]; exact readW_off_self _ _ _ _
  obtain v₂ : s₂.mem.readW (off base 100) 32 = s.gpr .r2 := by rw [m₂.mem, m₁.gpr]; exact readW_off_self _ _ _ _
  obtain v₃ : s₃.mem.readW (off base 104) 32 = s.gpr .r3 := by
    rw [m₃.mem, m₂.gpr, m₁.gpr]; exact readW_off_self _ _ _ _
  obtain v₅ : s₅.mem.readW (off base 84) 32 = stackArg s 0 := by
    rw [m₅.mem, u₄.gpr, A₃ 0 (by decide)]; exact readW_off_self _ _ _ _
  obtain v₇ : s₇.mem.readW (off base 92) 32 = stackArg s 2 := by
    rw [m₇.mem, u₆.gpr, A₅ 2 (by decide)]; exact readW_off_self _ _ _ _
  obtain v₉ : t.mem.readW (off base 108) 32 = stackArg s 3 := by
    rw [m₉.mem, u₈.gpr, A₇ 3 (by decide)]; exact readW_off_self _ _ _ _
  obtain k₉ : ∀ {d v}, (d + 4 ≤ 108 ∨ 112 ≤ d) → d + 4 ≤ 164 → s₇.mem.readW (off base d) 32 = v →
      t.mem.readW (off base d) 32 = v :=
    fun hd hd' h => by rw [m₉.mem, u₈.mem]; exact stored hd (by omega_arith) (by omega_arith) h _
  obtain k₇ : ∀ {d v}, (d + 4 ≤ 92 ∨ 96 ≤ d) → d + 4 ≤ 164 → s₅.mem.readW (off base d) 32 = v →
      s₇.mem.readW (off base d) 32 = v :=
    fun hd hd' h => by rw [m₇.mem, u₆.mem]; exact stored hd (by omega_arith) (by omega_arith) h _
  obtain k₅ : ∀ {d v}, (d + 4 ≤ 84 ∨ 88 ≤ d) → d + 4 ≤ 164 → s₃.mem.readW (off base d) 32 = v →
      s₅.mem.readW (off base d) 32 = v :=
    fun hd hd' h => by rw [m₅.mem, u₄.mem]; exact stored hd (by omega_arith) (by omega_arith) h _
  obtain k₃ : ∀ {d v}, (d + 4 ≤ 104 ∨ 108 ≤ d) → d + 4 ≤ 164 → s₂.mem.readW (off base d) 32 = v →
      s₃.mem.readW (off base d) 32 = v :=
    fun hd hd' h => by rw [m₃.mem]; exact stored hd (by omega_arith) (by omega_arith) h _
  obtain k₂ : ∀ {d v}, (d + 4 ≤ 100 ∨ 104 ≤ d) → d + 4 ≤ 164 → s₁.mem.readW (off base d) 32 = v →
      s₂.mem.readW (off base d) 32 = v :=
    fun hd hd' h => by rw [m₂.mem]; exact stored hd (by omega_arith) (by omega_arith) h _
  refine ⟨k₉ (by decide) (by decide) (k₇ (by decide) (by decide) (k₅ (by decide) (by decide)
      (k₃ (by decide) (by decide) (k₂ (by decide) (by decide) v₁)))),
    k₉ (by decide) (by decide) (k₇ (by decide) (by decide) (k₅ (by decide) (by decide) (k₃ (by decide) (by decide) v₂))),
    k₉ (by decide) (by decide) (k₇ (by decide) (by decide) (k₅ (by decide) (by decide) v₃)),
    k₉ (by decide) (by decide) (k₇ (by decide) (by decide) v₅), k₉ (by decide) (by decide) v₇, v₉, ?_, ?_, A⟩
  · exact (m₁.rest _).trans (m₂.rest _) |>.trans (m₃.rest _) |>.trans (u₄.rest (by decide)) |>.trans (m₅.rest _)
      |>.trans (u₆.rest (by decide)) |>.trans (m₇.rest _) |>.trans (u₈.rest (by decide)) |>.trans (m₉.rest _)
  · rw [m₉.mem, u₈.mem, m₇.mem, u₆.mem, m₅.mem, u₄.mem, m₃.mem, m₂.mem, m₁.mem]
    exact ((((((outside_word (by decide) (by decide) (by omega_arith) _).trans
      (outside_word (by decide) (by decide) (by omega_arith) _)).trans (outside_word (by decide) (by decide) (by omega_arith) _)).trans
      (outside_word (by decide) (by decide) (by omega_arith) _)).trans (outside_word (by decide) (by decide) (by omega_arith) _)).trans
      (outside_word (by decide) (by decide) (by omega_arith) _))

/-- The pointers to the key's components, each after the one before. -/
theorem keyPointers_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (hz : 164 ≤ size)
    {K PL QL : BitVec 32} (hK : s.mem.readW (off base 64) 32 = K) (hP : s.mem.readW (off base 100) 32 = PL)
    (hQ : s.mem.readW (off base 104) 32 = QL) :
    WP isa (.block Entry.keyPointers) s fun t =>
      t.mem.readW (off base 68) 32 = K + PL ∧ t.mem.readW (off base 72) 32 = K + PL + QL ∧
      t.mem.readW (off base 76) 32 = K + PL + QL + PL ∧ t.mem.readW (off base 80) 32 = K + PL + QL + PL + PL ∧
      Rest [.r4, .r5] s t ∧ Outside base 68 16 s.mem t.mem := by
  have nw := hs.nowrap
  show WP isa (.block [.ldr .r4 .r12 64, .ldr .r5 .r12 100, .dp .add .r4 .r4 (.reg .r5), .str .r4 .r12 68,
    .ldr .r5 .r12 104, .dp .add .r4 .r4 (.reg .r5), .str .r4 .r12 72,
    .ldr .r5 .r12 100, .dp .add .r4 .r4 (.reg .r5), .str .r4 .r12 76,
    .ldr .r5 .r12 100, .dp .add .r4 .r4 (.reg .r5), .str .r4 .r12 80]) s _
  refine wp_ldr12 hs (by decide) (by omega_arith) fun s₁ u₁ => ?_
  obtain w₁ := hs.of_upd u₁ (by decide)
  refine wp_ldr12 w₁ (by decide) (by omega_arith) fun s₂ u₂ => wp_dp (op2_reg _ _) fun s₃ u₃ => ?_
  obtain w₃ := (w₁.of_upd u₂ (by decide)).of_upd u₃ (by decide)
  refine wp_str12 w₃ (by decide) (by omega_arith) fun s₄ m₄ => ?_
  obtain w₄ := w₃.of_mupd m₄
  -- Reads of words below 68 and at 100 and 104 are kept by the stores.
  obtain k₄ : ∀ d, (d + 4 ≤ 68 ∨ 72 ≤ d) → d + 4 ≤ 164 → s₄.mem.readW (off base d) 32 = s.mem.readW (off base d) 32 :=
    fun d hd hd' => by rw [m₄.mem, u₃.mem, u₂.mem, u₁.mem]; exact readW_off_ne hd (by omega_arith) (by omega_arith) _
  refine wp_ldr12 w₄ (by decide) (by omega_arith) fun s₅ u₅ => wp_dp (op2_reg _ _) fun s₆ u₆ => ?_
  obtain w₆ := (w₄.of_upd u₅ (by decide)).of_upd u₆ (by decide)
  refine wp_str12 w₆ (by decide) (by omega_arith) fun s₇ m₇ => ?_
  obtain w₇ := w₆.of_mupd m₇
  obtain k₇ : ∀ d, (d + 4 ≤ 72 ∨ 76 ≤ d) → d + 4 ≤ 164 → s₇.mem.readW (off base d) 32 = s₄.mem.readW (off base d) 32 :=
    fun d hd hd' => by rw [m₇.mem, u₆.mem, u₅.mem]; exact readW_off_ne hd (by omega_arith) (by omega_arith) _
  refine wp_ldr12 w₇ (by decide) (by omega_arith) fun s₈ u₈ => wp_dp (op2_reg _ _) fun s₉ u₉ => ?_
  obtain w₉ := (w₇.of_upd u₈ (by decide)).of_upd u₉ (by decide)
  refine wp_str12 w₉ (by decide) (by omega_arith) fun s₁₀ m₁₀ => ?_
  obtain w₁₀ := w₉.of_mupd m₁₀
  obtain k₁₀ : ∀ d, (d + 4 ≤ 76 ∨ 80 ≤ d) → d + 4 ≤ 164 → s₁₀.mem.readW (off base d) 32 = s₇.mem.readW (off base d) 32 :=
    fun d hd hd' => by rw [m₁₀.mem, u₉.mem, u₈.mem]; exact readW_off_ne hd (by omega_arith) (by omega_arith) _
  refine wp_ldr12 w₁₀ (by decide) (by omega_arith) fun s₁₁ u₁₁ => wp_dp (op2_reg _ _) fun s₁₂ u₁₂ => ?_
  obtain w₁₂ := (w₁₀.of_upd u₁₁ (by decide)).of_upd u₁₂ (by decide)
  refine wp_str12 w₁₂ (by decide) (by omega_arith) fun t m₁₃ => WP.block_nil ?_
  obtain k₁₃ : ∀ d, (d + 4 ≤ 80 ∨ 84 ≤ d) → d + 4 ≤ 164 → t.mem.readW (off base d) 32 = s₁₀.mem.readW (off base d) 32 :=
    fun d hd hd' => by rw [m₁₃.mem, u₁₂.mem, u₁₁.mem]; exact readW_off_ne hd (by omega_arith) (by omega_arith) _
  obtain r4₃ : s₃.gpr .r4 = K + PL := by
    rw [u₃.gpr, dpVal, u₂.other .r4 (by decide), u₁.gpr, u₂.gpr]
    simp only [hdr]
    rw [u₁.mem, hK, hP]
  obtain r4₆ : s₆.gpr .r4 = K + PL + QL := by
    rw [u₆.gpr, dpVal, u₅.other .r4 (by decide), m₄.gpr, r4₃, u₅.gpr]
    simp only [hdr]
    rw [k₄ 104 (by decide) (by decide), hQ]
  obtain r4₉ : s₉.gpr .r4 = K + PL + QL + PL := by
    rw [u₉.gpr, dpVal, u₈.other .r4 (by decide), m₇.gpr, r4₆, u₈.gpr]
    simp only [hdr]
    rw [k₇ 100 (by decide) (by decide), k₄ 100 (by decide) (by decide), hP]
  obtain r4₁₂ : s₁₂.gpr .r4 = K + PL + QL + PL + PL := by
    rw [u₁₂.gpr, dpVal, u₁₁.other .r4 (by decide), m₁₀.gpr, r4₉, u₁₁.gpr]
    simp only [hdr]
    rw [k₁₀ 100 (by decide) (by decide), k₇ 100 (by decide) (by decide), k₄ 100 (by decide) (by decide), hP]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [k₁₃ 68 (by decide) (by decide), k₁₀ 68 (by decide) (by decide), k₇ 68 (by decide) (by decide), m₄.mem,
      r4₃]; exact readW_off_self _ _ _ _
  · rw [k₁₃ 72 (by decide) (by decide), k₁₀ 72 (by decide) (by decide), m₇.mem, r4₆]; exact readW_off_self _ _ _ _
  · rw [k₁₃ 76 (by decide) (by decide), m₁₀.mem, r4₉]; exact readW_off_self _ _ _ _
  · rw [m₁₃.mem, r4₁₂]; exact readW_off_self _ _ _ _
  · exact (u₁.rest (by decide)).trans (u₂.rest (by decide)) |>.trans (u₃.rest (by decide)) |>.trans (m₄.rest _)
      |>.trans (u₅.rest (by decide)) |>.trans (u₆.rest (by decide)) |>.trans (m₇.rest _) |>.trans (u₈.rest (by decide))
      |>.trans (u₉.rest (by decide)) |>.trans (m₁₀.rest _) |>.trans (u₁₁.rest (by decide)) |>.trans
      (u₁₂.rest (by decide)) |>.trans (m₁₃.rest _)
  · rw [m₁₃.mem, u₁₂.mem, u₁₁.mem, m₁₀.mem, u₉.mem, u₈.mem, m₇.mem, u₆.mem, u₅.mem, m₄.mem, u₃.mem, u₂.mem, u₁.mem]
    exact (((outside_word (by decide) (by decide) (by omega_arith) _).trans
      (outside_word (by decide) (by decide) (by omega_arith) _)).trans (outside_word (by decide) (by decide) (by omega_arith) _)).trans
      (outside_word (by decide) (by decide) (by omega_arith) _)

end VG.Proof.Dsa.Arm

end

end

/-!
# DSA on 32-bit ARM: the entries

From the precondition of the contract, the entry of signing (`signEntry_ok`)
and of verification (`verifyEntry_ok`) leaves `r12` at `scratch`, the
registers to restore at its offset 128 and the arguments and the key's
component pointers at their fields (`Installed`), and has changed nothing
else but its header.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd)

/-- The fields of the entry: `(offset, value)`. -/
abbrev Fields := List (Nat × BitVec 32)

/-- What the entry leaves, from `s₀`. -/
structure Installed (s₀ : State) (base : Addr) (size : Nat) (fields : Fields) (u : State) : Prop where
  ws : Ws u base size
  fields : ∀ f ∈ fields, u.mem.readW (off base f.1) 32 = f.2
  saved : ∀ i < 9, u.mem.readW (off base (128 + 4 * i)) 32 = s₀.gpr (Entry.savedRegs.getD i .r0)
  mem : Outside base 64 100 s₀.mem u.mem
  rest : Rest [.r4, .r5, .r12] s₀ u

/-- The scratch region, and `r12` set to it. -/
theorem openScratch_ws {s u : State} {i : Nat} (hu : Upd s u .r12 (stackArg s i)) (size : Nat)
    (hr : ⟨State.addr (stackArg s i), size⟩ ∈ s.wr) (hb : (stackArg s i).toNat + size ≤ 2 ^ 32) :
    Ws u (State.addr (stackArg s i)) size :=
  ⟨by rw [hu.gpr], ⟨size, Nat.le_refl _, by omega_arith, by rw [hu.wr]; exact hr⟩,
    by rw [VG.Proof.X25519.Arm.addr_toNat]; exact hb⟩

theorem args_read {s : State} {n : Nat} (h : ⟨State.addr s.sp, 4 * n⟩ ∈ s.rd) (hb : s.sp.toNat + 4 * n ≤ 2 ^ 32) :
    ArgsRead s n := fun i hi =>
  ⟨_, List.mem_append_left _ h, by
    rw [stackArgAddr, VG.Arm.addr_add (by omega_arith)]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩

theorem args_apart {s : State} {base : Addr} {n size : Nat} (h : Region.Disjoint ⟨State.addr s.sp, 4 * n⟩ ⟨base, size⟩)
    (hb : s.sp.toNat + 4 * n ≤ 2 ^ 32) (hz : 164 ≤ size) :
    ArgsApart s base n := fun i hi d hd =>
  Region.Disjoint.sep h (by rw [stackArgAddr, VG.Arm.addr_add (by omega_arith)]; exact Offset.contains_base _ (by omega_arith) (by omega_arith))
    (Offset.contains_base base (by omega_arith) (by omega_arith))

/-- The fields of signing. -/
abbrev signFields (s : State) : Fields :=
  [(96, s.gpr .r0), (64, s.gpr .r2), (100, arg s 0), (88, arg s 1), (104, arg s 2), (92, arg s 3), (108, arg s 4),
    (68, s.gpr .r2 + arg s 0), (72, s.gpr .r2 + arg s 0 + arg s 2), (76, s.gpr .r2 + arg s 0 + arg s 2 + arg s 0),
    (80, s.gpr .r2 + arg s 0 + arg s 2 + arg s 0 + arg s 0)]

/-- The fields of verification. -/
abbrev verifyFields (s : State) : Fields :=
  [(64, s.gpr .r0), (100, s.gpr .r2), (104, s.gpr .r3), (84, arg s 0), (92, arg s 2), (108, arg s 3),
    (68, s.gpr .r0 + s.gpr .r2), (72, s.gpr .r0 + s.gpr .r2 + s.gpr .r3),
    (76, s.gpr .r0 + s.gpr .r2 + s.gpr .r3 + s.gpr .r2), (80, s.gpr .r0 + s.gpr .r2 + s.gpr .r3 + s.gpr .r2 + s.gpr .r2)]

/-- A word stored by the entry and kept since. -/
theorem keep_word {m m' : Mem} {base : Addr} {o n d : Nat} {v : BitVec 32} (O : Outside base o n m m')
    (hd : d + 4 ≤ o ∨ o + n ≤ d) (hb : d + 4 ≤ 2 ^ 64) (h : m.readW (off base d) 32 = v) :
    m'.readW (off base d) 32 = v := by
  rw [← h]
  exact BitVec.eq_of_toNat_eq (O.w32 hd hb)

/-- A word apart from the working space, which only changed inside it. -/
theorem readW_apart {m m' : Mem} {base p : Addr} {o n size : Nat} (O : Outside base o n m m')
    (hd : Region.Disjoint ⟨p, 4⟩ ⟨base, size⟩) (ho : o + n ≤ size) (hs : size ≤ 2 ^ 64) :
    m'.readW p 32 = m.readW p 32 :=
  Mem.readW_congr fun i hi =>
    (VG.Proof.Weierstrass.keep_of_disjoint O (hd.sub_right (Offset.sub_base base ho)) (by omega_arith) hi (by decide))

theorem stackArg_apart {s s' : State} {base : Addr} {o n size k i : Nat} (O : Outside base o n s.mem s'.mem)
    (hsp : s'.sp = s.sp) (hd : Region.Disjoint ⟨State.addr s.sp, 4 * k⟩ ⟨base, size⟩) (hi : i < k)
    (hb : s.sp.toNat + 4 * k ≤ 2 ^ 32) (ho : o + n ≤ size) (hs : size ≤ 2 ^ 64) :
    stackArg s' i = stackArg s i := by
  unfold stackArg
  rw [show stackArgAddr s' i = stackArgAddr s i by simp only [stackArgAddr, hsp]]
  refine readW_apart O (hd.sub_left ?_) ho hs
  rw [stackArgAddr, VG.Arm.addr_add (by omega_arith)]
  exact Offset.sub_base _ (by omega_arith)

theorem ArgsApart.sp {s s' : State} {base : Addr} {n : Nat} (h : ArgsApart s base n) (hsp : s'.sp = s.sp) :
    ArgsApart s' base n :=
  fun i hi d hd => by rw [show stackArgAddr s' i = stackArgAddr s i by simp only [stackArgAddr, hsp]]; exact h i hi d hd

theorem saved_ne : ∀ i < 9, Entry.savedRegs.getD i .r0 ≠ .r12 := by decide

theorem signEntry_ok {s : State} (h : signPre s) :
    WP isa (.block Entry.signEntry) s
      (Installed s (State.addr (arg s 5)) ((arg s 6).toNat * 8) (signFields s)) := by
  obtain ⟨hsp, hrd, hwr, _, _, _, _, _, _, _, _, hsa, _, _, _, _, hsb, hv, _, _, hsw⟩ := h
  have v := hv
  unfold Spec.Dsa.lengthsValid at v
  obtain hs16 : 16384 ≤ (arg s 6).toNat * 8 := by unfold Spec.Dsa.scratchWords at hsw; omega_arith
  have hd : Region.Disjoint ⟨State.addr s.sp, 4 * 7⟩ ⟨State.addr (arg s 5), (arg s 6).toNat * 8⟩ := hsa.symm
  show WP isa (.block (((Entry.openScratch 5) ++ Entry.signArguments.flatMap Entry.saveArgument) ++
    Entry.keyPointers)) s _
  simp only [Entry.openScratch, List.append_assoc, List.singleton_append]
  refine wp_ldrSp (i := 5) (by decide) (args_read (n := 7) (by rw [hrd]; simp) hsp 5 (by decide)) fun u₁ v₁ => ?_
  obtain w₁ := openScratch_ws v₁ ((arg s 6).toNat * 8) (by rw [hwr]; simp) hsb
  have nw := w₁.nowrap
  obtain aa : ArgsApart s (State.addr (arg s 5)) 7 := args_apart hd hsp (by omega_arith)
  refine VG.Proof.X25519.Arm.WP.append (save_ok w₁ (by omega_arith)) fun u₂ ⟨S₂, R₂, O₂⟩ => ?_
  obtain w₂ := w₁.of_rest R₂ (by decide)
  obtain hsp₂ : u₂.sp = s.sp := by rw [R₂.sp, v₁.sp]
  rw [v₁.mem] at O₂
  obtain A₂ : ∀ i < 7, stackArg u₂ i = stackArg s i := fun i hi =>
    stackArg_apart O₂ hsp₂ hd hi hsp (by omega_arith) (by omega_arith)
  obtain r₂ : ArgsRead u₂ 7 := (args_read (n := 7) (by rw [hrd]; simp) hsp).keep (by rw [R₂.rd, v₁.rd])
    (by rw [R₂.wr, v₁.wr]) hsp₂
  refine VG.Proof.X25519.Arm.WP.append (signArgs_ok w₂ (by omega_arith) r₂ (aa.sp hsp₂))
    fun u₃ ⟨F₁, F₂, F₃, F₄, F₅, F₆, F₇, R₃, O₃, A₃⟩ => ?_
  obtain w₃ := w₂.of_rest R₃ (by decide)
  obtain g0 : u₂.gpr .r0 = s.gpr .r0 := by rw [R₂.gpr _ (by decide), v₁.other _ (by decide)]
  obtain g2 : u₂.gpr .r2 = s.gpr .r2 := by rw [R₂.gpr _ (by decide), v₁.other _ (by decide)]
  rw [g0] at F₁
  rw [g2] at F₂
  rw [A₂ 0 (by decide)] at F₃
  rw [A₂ 1 (by decide)] at F₄
  rw [A₂ 2 (by decide)] at F₅
  rw [A₂ 3 (by decide)] at F₆
  rw [A₂ 4 (by decide)] at F₇
  refine WP.mono (keyPointers_ok w₃ (by omega_arith) F₂ F₃ F₅) fun u ⟨K₁, K₂, K₃, K₄, R₄, O₄⟩ => ⟨w₃.of_rest R₄ (by decide), ?_, ?_, ?_, ?_⟩
  · intro f hf
    obtain k : ∀ {d} {x : BitVec 32}, (d + 4 ≤ 68 ∨ 84 ≤ d) → d + 4 ≤ 164 → u₃.mem.readW (off (State.addr (arg s 5)) d) 32 = x →
        u.mem.readW (off (State.addr (arg s 5)) d) 32 = x := fun hd' hd'' h => keep_word O₄ hd' (by omega_arith) h
    simp only [signFields, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact k (d := 96) (by decide) (by decide) F₁
    · exact k (d := 64) (by decide) (by decide) F₂
    · exact k (d := 100) (by decide) (by decide) F₃
    · exact k (d := 88) (by decide) (by decide) F₄
    · exact k (d := 104) (by decide) (by decide) F₅
    · exact k (d := 92) (by decide) (by decide) F₆
    · exact k (d := 108) (by decide) (by decide) F₇
    · exact K₁
    · exact K₂
    · exact K₃
    · exact K₄
  · intro i hi
    obtain g : u₁.gpr (Entry.savedRegs.getD i .r0) = s.gpr (Entry.savedRegs.getD i .r0) :=
      v₁.other _ (saved_ne i hi)
    rw [← g]
    exact keep_word O₄ (.inr (by omega_arith)) (by omega_arith) (keep_word O₃ (.inr (by omega_arith)) (by omega_arith) (S₂ i hi))
  · exact ((O₂.mono (by decide) (by decide)).trans (O₃.mono (by decide) (by decide))).trans
      (O₄.mono (by decide) (by decide))
  · exact (((v₁.rest (by decide)).trans (R₂.mono (by decide))).trans (R₃.mono (by decide))).trans (R₄.mono (by decide))

theorem verifyEntry_ok {s : State} (h : verifyPre s) :
    WP isa (.block Entry.verifyEntry) s
      (Installed s (State.addr (arg s 4)) ((arg s 5).toNat * 8) (verifyFields s)) := by
  obtain ⟨hsp, hrd, hwr, _, _, _, hsa, _, _, _, hsb, hv, _, _, hsw⟩ := h
  have v := hv
  unfold Spec.Dsa.lengthsValid at v
  obtain hs16 : 16384 ≤ (arg s 5).toNat * 8 := by unfold Spec.Dsa.scratchWords at hsw; omega_arith
  have hd : Region.Disjoint ⟨State.addr s.sp, 4 * 6⟩ ⟨State.addr (arg s 4), (arg s 5).toNat * 8⟩ := hsa.symm
  show WP isa (.block (((Entry.openScratch 4) ++ Entry.verifyArguments.flatMap Entry.saveArgument) ++
    Entry.keyPointers)) s _
  simp only [Entry.openScratch, List.append_assoc, List.singleton_append]
  refine wp_ldrSp (i := 4) (by decide) (args_read (n := 6) (by rw [hrd]; simp) hsp 4 (by decide)) fun u₁ v₁ => ?_
  obtain w₁ := openScratch_ws v₁ ((arg s 5).toNat * 8) (by rw [hwr]; simp) hsb
  obtain aa : ArgsApart s (State.addr (arg s 4)) 6 := args_apart hd hsp (by omega_arith)
  refine VG.Proof.X25519.Arm.WP.append (save_ok w₁ (by omega_arith)) fun u₂ ⟨S₂, R₂, O₂⟩ => ?_
  obtain w₂ := w₁.of_rest R₂ (by decide)
  obtain hsp₂ : u₂.sp = s.sp := by rw [R₂.sp, v₁.sp]
  rw [v₁.mem] at O₂
  obtain A₂ : ∀ i < 6, stackArg u₂ i = stackArg s i := fun i hi =>
    stackArg_apart O₂ hsp₂ hd hi hsp (by omega_arith) (by omega_arith)
  obtain r₂ : ArgsRead u₂ 6 := (args_read (n := 6) (by rw [hrd]; simp) hsp).keep (by rw [R₂.rd, v₁.rd])
    (by rw [R₂.wr, v₁.wr]) hsp₂
  refine VG.Proof.X25519.Arm.WP.append (verifyArgs_ok w₂ (by omega_arith) r₂ (aa.sp hsp₂))
    fun u₃ ⟨F₁, F₂, F₃, F₄, F₅, F₆, R₃, O₃, A₃⟩ => ?_
  obtain w₃ := w₂.of_rest R₃ (by decide)
  obtain g0 : u₂.gpr .r0 = s.gpr .r0 := by rw [R₂.gpr _ (by decide), v₁.other _ (by decide)]
  obtain g2 : u₂.gpr .r2 = s.gpr .r2 := by rw [R₂.gpr _ (by decide), v₁.other _ (by decide)]
  obtain g3 : u₂.gpr .r3 = s.gpr .r3 := by rw [R₂.gpr _ (by decide), v₁.other _ (by decide)]
  rw [g0] at F₁
  rw [g2] at F₂
  rw [g3] at F₃
  rw [A₂ 0 (by decide)] at F₄
  rw [A₂ 2 (by decide)] at F₅
  rw [A₂ 3 (by decide)] at F₆
  refine WP.mono (keyPointers_ok w₃ (by omega_arith) F₁ F₂ F₃) fun u ⟨K₁, K₂, K₃, K₄, R₄, O₄⟩ => ⟨w₃.of_rest R₄ (by decide), ?_, ?_, ?_, ?_⟩
  · intro f hf
    obtain k : ∀ {d} {x : BitVec 32}, (d + 4 ≤ 68 ∨ 84 ≤ d) → d + 4 ≤ 164 → u₃.mem.readW (off (State.addr (arg s 4)) d) 32 = x →
        u.mem.readW (off (State.addr (arg s 4)) d) 32 = x := fun hd' hd'' h => keep_word O₄ hd' (by omega_arith) h
    simp only [verifyFields, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact k (d := 64) (by decide) (by decide) F₁
    · exact k (d := 100) (by decide) (by decide) F₂
    · exact k (d := 104) (by decide) (by decide) F₃
    · exact k (d := 84) (by decide) (by decide) F₄
    · exact k (d := 92) (by decide) (by decide) F₅
    · exact k (d := 108) (by decide) (by decide) F₆
    · exact K₁
    · exact K₂
    · exact K₃
    · exact K₄
  · intro i hi
    obtain g : u₁.gpr (Entry.savedRegs.getD i .r0) = s.gpr (Entry.savedRegs.getD i .r0) :=
      v₁.other _ (saved_ne i hi)
    rw [← g]
    exact keep_word O₄ (.inr (by omega_arith)) (by omega_arith) (keep_word O₃ (.inr (by omega_arith)) (by omega_arith) (S₂ i hi))
  · exact ((O₂.mono (by decide) (by decide)).trans (O₃.mono (by decide) (by decide))).trans
      (O₄.mono (by decide) (by decide))
  · exact (((v₁.rest (by decide)).trans (R₂.mono (by decide))).trans (R₃.mono (by decide))).trans (R₄.mono (by decide))

end VG.Proof.Dsa.Arm

end

end

/-!
# DSA on 32-bit ARM: the caller's buffers, and the exit

From the entry until a body starts, memory has changed only inside the
working space, whose header still holds the fields and the saved registers
(`Env`). The operands of the bodies are then slices of the caller's buffers
(`input_of`), and the exit restores the saved registers (`restore_ok`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm
open VG.Proof.X25519.Arm (Rest Upd)

/-- Memory changed only inside the working space, whose header keeps the fields. -/
structure Env (s₀ : State) (base : Addr) (size : Nat) (fields : Fields) (t : State) : Prop where
  ws : Ws t base size
  fields : ∀ f ∈ fields, t.mem.readW (off base f.1) 32 = f.2
  saved : ∀ i < 9, t.mem.readW (off base (128 + 4 * i)) 32 = s₀.gpr (Entry.savedRegs.getD i .r0)
  mem : Outside base 0 size s₀.mem t.mem
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  sp : t.sp = s₀.sp

/-- The header's fields lie in `[64, 112)`. -/
abbrev FieldsOk (fields : Fields) : Prop := ∀ f ∈ fields, 64 ≤ f.1 ∧ f.1 + 4 ≤ 112

theorem Env.of_installed {s₀ u : State} {base : Addr} {size : Nat} {fields : Fields}
    (I : Installed s₀ base size fields u) (hz : 164 ≤ size) : Env s₀ base size fields u :=
  ⟨I.ws, I.fields, I.saved, I.mem.mono (Nat.zero_le _) (by omega_arith), I.rest.rd, I.rest.wr, I.rest.sp⟩

/-- A step that changes registers but `r12`, and memory in ranges of the working space
apart from the fields and the saved registers. -/
theorem Env.keep {s₀ t t' : State} {base : Addr} {size : Nat} {fields : Fields} {ws : List Reg}
    {rs : List (Nat × Nat)} (E : Env s₀ base size fields t) (hf : FieldsOk fields)
    (R : Rest ws t t') (hr : .r12 ∉ ws) (O : Outs base rs t.mem t'.mem)
    (hrs : ∀ r ∈ rs, r.1 + r.2 ≤ size ∧ (r.1 + r.2 ≤ 64 ∨ 164 ≤ r.1 ∨ (112 ≤ r.1 ∧ r.1 + r.2 ≤ 128))) :
    Env s₀ base size fields t' := by
  have nw := E.ws.nowrap
  refine ⟨E.ws.of_rest R hr, fun f h => ?_, fun i hi => ?_, fun x hx => ?_, R.rd.trans E.rd, R.wr.trans E.wr,
    R.sp.trans E.sp⟩
  · have := hf f h
    rw [← E.fields f h]
    exact hdr_keep (s := t) (t := t') O (fun r hr' => by have := hrs r hr'; omega_arith) (by omega_arith)
  · rw [← E.saved i hi]
    exact hdr_keep (s := t) (t := t') O (fun r hr' => by have := hrs r hr'; omega_arith) (by omega_arith)
  · rw [← E.mem x hx]
    exact O x fun r hr' => .inr (by have := hrs r hr'; omega_arith)

theorem Env.of_mem {s₀ t t' : State} {base : Addr} {size : Nat} {fields : Fields} {ws : List Reg}
    (E : Env s₀ base size fields t) (R : Rest ws t t') (hr : .r12 ∉ ws) (M : t'.mem = t.mem) :
    Env s₀ base size fields t' :=
  ⟨E.ws.of_rest R hr, fun f h => by rw [M]; exact E.fields f h, fun i hi => by rw [M]; exact E.saved i hi,
    by rw [M]; exact E.mem, R.rd.trans E.rd, R.wr.trans E.wr, R.sp.trans E.sp⟩

theorem Env.field {s₀ t : State} {base : Addr} {size : Nat} {fields : Fields} (E : Env s₀ base size fields t)
    {d : Nat} {v : BitVec 32} (h : (d, v) ∈ fields) : hdr base t d = v :=
  E.fields (d, v) h

/-- A byte of the working space is not one of a range apart from it. -/
theorem ofs_apart {base P x : Addr} {L size : Nat} (hd : Region.Disjoint ⟨P, L⟩ ⟨base, size⟩)
    (hx : ofs base x < size) : L ≤ ofs P x := by
  by_contra h
  exact hd x (by simp only [Region.Contains, ofs] at h ⊢; omega_arith) (by simp only [Region.Contains, ofs] at hx ⊢; omega_arith)

/-- The saved registers through a body. -/
theorem Env.saved_body {s₀ t t' : State} {base P : Addr} {size L : Nat} {fields : Fields}
    (E : Env s₀ base size fields t) (B : Body base P L t t') (hd : Region.Disjoint ⟨P, L⟩ ⟨base, size⟩)
    (hz : 164 ≤ size) :
    ∀ i < 9, t'.mem.readW (off base (128 + 4 * i)) 32 = s₀.gpr (Entry.savedRegs.getD i .r0) := by
  have nw := E.ws.nowrap
  intro i hi
  rw [← E.saved i hi]
  refine Mem.readW_congr fun j hj => B.mem _ (fun r hr => ?_) (ofs_apart hd ?_)
  · simp only [runRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [ofs_off base (by omega_arith)]
    rcases hr with rfl | rfl | rfl | rfl <;> simp only <;> omega_arith
  · rw [ofs_off base (by omega_arith)]
    omega_arith

/-- The saved registers past a range of the caller. -/
theorem Env.saved_outside {s₀ t t' : State} {base P : Addr} {size L : Nat} {fields : Fields}
    (E : Env s₀ base size fields t) (O : Outside P 0 L t.mem t'.mem) (hd : Region.Disjoint ⟨P, L⟩ ⟨base, size⟩)
    (hz : 164 ≤ size) :
    ∀ i < 9, t'.mem.readW (off base (128 + 4 * i)) 32 = s₀.gpr (Entry.savedRegs.getD i .r0) := by
  have nw := E.ws.nowrap
  intro i hi
  rw [← E.saved i hi]
  refine Mem.readW_congr fun j hj => O _ (.inr ?_)
  have := ofs_apart hd (x := off base (128 + 4 * i) + BitVec.ofNat 64 j) (by rw [ofs_off base (by omega_arith)]; omega_arith)
  omega_arith

/-! ## The operands -/

/-- An operand that is a slice of one of the caller's buffers. -/
theorem input_of {s₀ t : State} {base : Addr} {size : Nat} {fields : Fields} (E : Env s₀ base size fields t)
    {p : Impl.Dsa.Layout.Pointer} (hp : PtrOk p) {P₀ : BitVec 32} {L₀ o len : Nat}
    (hv : pointerValue base t p = P₀ + BitVec.ofNat 32 o)
    (hr : ⟨State.addr P₀, L₀⟩ ∈ s₀.rd ++ s₀.wr) (hfit : P₀.toNat + L₀ ≤ 2 ^ 32) (ho : o + len ≤ L₀) (hl : 0 < len ∨ o = 0)
    (hd : Region.Disjoint ⟨State.addr P₀, L₀⟩ ⟨base, size⟩) (hz : 12016 ≤ size) :
    Input t base size p len (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s₀.mem (State.addr P₀ + BitVec.ofNat 64 o) len)) := by
  have nw := E.ws.nowrap
  have P₀lt := P₀.isLt
  have A : State.addr (pointerValue base t p) = State.addr P₀ + BitVec.ofNat 64 o := by
    rw [hv, VG.Arm.addr_add (by omega_arith)]
  have D : Region.Disjoint ⟨State.addr (pointerValue base t p), len⟩ ⟨base, size⟩ := by
    rw [A]; exact hd.sub_left (Offset.sub_base _ ho)
  refine ⟨⟨hp, ?_, fun e k hek => ?_, D.sub_right (Region.sub_prefix hz)⟩, D, ?_⟩
  · rw [hv, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith : o < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith
  · rw [A, Offset.add_add, E.rd, E.wr]
    exact ⟨_, hr, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  · simp only [operand, A]
    rw [bytes_keep E.mem (by rw [← A]; exact D) (by omega_arith) (by omega_arith)]

/-! ## The exit -/

theorem restore_ok {t : State} {base : Addr} {size : Nat} (hs : Ws t base size) (hz : 164 ≤ size)
    {v : Nat → BitVec 32} (hv : ∀ i < 9, t.mem.readW (off base (128 + 4 * i)) 32 = v i) :
    WP isa (.block Entry.restore) t fun u =>
      (∀ i < 9, u.gpr (Entry.savedRegs.getD i .r0) = v i) ∧ Rest Entry.savedRegs t u ∧ u.mem = t.mem := by
  have nw := hs.nowrap
  show WP isa (.block [.ldr .r4 .r12 128, .ldr .r5 .r12 132, .ldr .r6 .r12 136, .ldr .r7 .r12 140,
    .ldr .r8 .r12 144, .ldr .r9 .r12 148, .ldr .r10 .r12 152, .ldr .r11 .r12 156, .ldr .lr .r12 160]) t _
  refine wp_ldr12 hs (by decide) (by omega_arith) fun u₁ v₁ => ?_
  have w₁ := hs.of_upd v₁ (by decide)
  refine wp_ldr12 w₁ (by decide) (by omega_arith) fun u₂ v₂ => ?_
  have w₂ := w₁.of_upd v₂ (by decide)
  refine wp_ldr12 w₂ (by decide) (by omega_arith) fun u₃ v₃ => ?_
  have w₃ := w₂.of_upd v₃ (by decide)
  refine wp_ldr12 w₃ (by decide) (by omega_arith) fun u₄ v₄ => ?_
  have w₄ := w₃.of_upd v₄ (by decide)
  refine wp_ldr12 w₄ (by decide) (by omega_arith) fun u₅ v₅ => ?_
  have w₅ := w₄.of_upd v₅ (by decide)
  refine wp_ldr12 w₅ (by decide) (by omega_arith) fun u₆ v₆ => ?_
  have w₆ := w₅.of_upd v₆ (by decide)
  refine wp_ldr12 w₆ (by decide) (by omega_arith) fun u₇ v₇ => ?_
  have w₇ := w₆.of_upd v₇ (by decide)
  refine wp_ldr12 w₇ (by decide) (by omega_arith) fun u₈ v₈ => ?_
  have w₈ := w₇.of_upd v₈ (by decide)
  refine wp_ldr12 w₈ (by decide) (by omega_arith) fun u v₉ => WP.block_nil ⟨?_, ?_, ?_⟩
  · have m : ∀ d, hdr base u₈ d = hdr base t d := fun d => by
      simp only [hdr, v₈.mem, v₇.mem, v₆.mem, v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem]
    have m' : ∀ d, hdr base u₇ d = hdr base t d := fun d => by
      simp only [hdr, v₇.mem, v₆.mem, v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem]
    have m6 : ∀ d, hdr base u₆ d = hdr base t d := fun d => by
      simp only [hdr, v₆.mem, v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem]
    have m5 : ∀ d, hdr base u₅ d = hdr base t d := fun d => by
      simp only [hdr, v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem]
    have m4 : ∀ d, hdr base u₄ d = hdr base t d := fun d => by simp only [hdr, v₄.mem, v₃.mem, v₂.mem, v₁.mem]
    have m3 : ∀ d, hdr base u₃ d = hdr base t d := fun d => by simp only [hdr, v₃.mem, v₂.mem, v₁.mem]
    have m2 : ∀ d, hdr base u₂ d = hdr base t d := fun d => by simp only [hdr, v₂.mem, v₁.mem]
    have m1 : ∀ d, hdr base u₁ d = hdr base t d := fun d => by simp only [hdr, v₁.mem]
    intro i hi
    rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp (disch := decide) only [List.getD, Entry.savedRegs, List.getElem?_cons_zero, Option.getD_some, v₉.other, v₈.other, v₇.other, v₆.other, v₅.other, v₄.other, v₃.other, v₂.other, v₁.gpr]
      exact hv 0 (by decide)
    · simp (disch := decide) only [List.getD, Entry.savedRegs, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, v₉.other, v₈.other, v₇.other, v₆.other, v₅.other, v₄.other, v₃.other, v₂.gpr, m1]
      exact hv 1 (by decide)
    · simp (disch := decide) only [List.getD, Entry.savedRegs, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, v₉.other, v₈.other, v₇.other, v₆.other, v₅.other, v₄.other, v₃.gpr, m2]
      exact hv 2 (by decide)
    · simp (disch := decide) only [List.getD, Entry.savedRegs, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, v₉.other, v₈.other, v₇.other, v₆.other, v₅.other, v₄.gpr, m3]
      exact hv 3 (by decide)
    · simp (disch := decide) only [List.getD, Entry.savedRegs, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, v₉.other, v₈.other, v₇.other, v₆.other, v₅.gpr, m4]
      exact hv 4 (by decide)
    · simp (disch := decide) only [List.getD, Entry.savedRegs, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, v₉.other, v₈.other, v₇.other, v₆.gpr, m5]
      exact hv 5 (by decide)
    · simp (disch := decide) only [List.getD, Entry.savedRegs, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, v₉.other, v₈.other, v₇.gpr, m6]
      exact hv 6 (by decide)
    · simp (disch := decide) only [List.getD, Entry.savedRegs, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, v₉.other, v₈.gpr, m']
      exact hv 7 (by decide)
    · simp (disch := decide) only [List.getD, Entry.savedRegs, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, v₉.gpr, m]
      exact hv 8 (by decide)
  · exact (((((((((v₁.rest (by decide)).trans (v₂.rest (by decide))).trans (v₃.rest (by decide))).trans
      (v₄.rest (by decide))).trans (v₅.rest (by decide))).trans (v₆.rest (by decide))).trans
      (v₇.rest (by decide))).trans (v₈.rest (by decide))).trans (v₉.rest (by decide)))
  · rw [v₉.mem, v₈.mem, v₇.mem, v₆.mem, v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem]

/-- The registers the ABI preserves, from their saved words. -/
theorem abi_of_restored {s u : State} (h : ∀ i < 9, u.gpr (Entry.savedRegs.getD i .r0) = s.gpr (Entry.savedRegs.getD i .r0))
    (hsp : u.sp = s.sp) : abiPreserved s u := by
  refine ⟨fun r hr => ?_, hsp⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h 0 (by decide)
  · exact h 1 (by decide)
  · exact h 2 (by decide)
  · exact h 3 (by decide)
  · exact h 4 (by decide)
  · exact h 5 (by decide)
  · exact h 6 (by decide)
  · exact h 7 (by decide)
  · exact h 8 (by decide)

/-- The exit, from a state whose header still holds the saved registers. -/
theorem finish_ok {s t : State} {base : Addr} {size : Nat} (hs : Ws t base size) (hz : 164 ≤ size)
    (hv : ∀ i < 9, t.mem.readW (off base (128 + 4 * i)) 32 = s.gpr (Entry.savedRegs.getD i .r0))
    (hsp : t.sp = s.sp) {Q : State → Prop}
    (hQ : ∀ u, abiPreserved s u → u.gpr .r0 = t.gpr .r0 → u.mem = t.mem → Q u) :
    WP isa (.seq (.block Entry.restore) (.block [])) t Q :=
  WP.seq (WP.mono (restore_ok hs hz hv) fun u ⟨G, R, M⟩ =>
    WP.block_nil (hQ u (abi_of_restored G (R.sp.trans hsp)) (R.gpr .r0 (by decide)) M))

end VG.Proof.Dsa.Arm

end

end

/-!
# DSA on 32-bit ARM: signing is correct

`sign_correct`: from `signArm`'s precondition, `vg_dsa_sign` returns the
status of `Spec.Dsa.signBytes` and writes its signature (or zeros), and
restores the registers the ABI preserves.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm
open VG.Proof.Ecdsa.Arm (mask32)
open VG.Proof.X25519.Arm (Rest)

variable {umaal : Bool}

theorem qWidth_of_shape {P Q : Nat} (h : shapeValid P Q) : qWidth Q = Spec.Dsa.bitLength Q / 8 := by
  have S := h.1
  unfold Spec.Dsa.supportedSizes at S
  unfold qWidth
  rcases S with ⟨_, h₁⟩ | ⟨_, h₁ | h₁ | h₁⟩ | ⟨_, h₁⟩ <;> simp [h₁]

theorem shape_bounds {P Q : Nat} (h : shapeValid P Q) : 1 < P ∧ P % 2 = 1 ∧ 255 < Q ∧ Q % 2 = 1 := by
  have B := VG.Proof.Dsa.supported_bounds h.1
  exact ⟨B.1, h.2.2, B.2.1, h.2.1⟩

theorem width_of {pLen qLen : Nat} (h : Spec.Dsa.lengthsValid pLen qLen) :
    Width pLen ((pLen + 7) / 8) ∧ Width qLen ((qLen + 7) / 8) ∧ qLen ≤ pLen ∧ qLen ≤ 32 ∧ 0 < qLen ∧
      128 ≤ pLen := by
  unfold Spec.Dsa.lengthsValid at h
  refine ⟨⟨rfl, by omega_arith, by omega_arith, by omega_arith⟩, ⟨rfl, by omega_arith, by omega_arith, by omega_arith⟩, by omega_arith, by omega_arith, by omega_arith,
    by omega_arith⟩

theorem widths_mem {pLen qLen : Nat} (h : Spec.Dsa.lengthsValid pLen qLen) :
    (pLen, qLen) ∈ [(128, 20), (256, 28), (256, 32), (384, 32), (256, 20)] := by
  unfold Spec.Dsa.lengthsValid at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem signFields_ok (s : State) : FieldsOk (signFields s) := by
  intro f hf
  simp only [signFields, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem sum_ofNat (K : BitVec 32) (xs : List (BitVec 32)) :
    xs.foldl (· + ·) K = K + BitVec.ofNat 32 (xs.map BitVec.toNat).sum := by
  induction xs generalizing K with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih, List.map_cons, List.sum_cons, ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc,
      BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem signKey (m : Mem) (A : Addr) {pLen qLen total : Nat} (h : 3 * pLen + 2 * qLen ≤ total) :
    Spec.Dsa.privateKeyBytes pLen qLen (Spec.Rsa.bytesAt m A total) =
      ⟨⟨Spec.Dsa.decodeBE (Spec.Rsa.bytesAt m A pLen),
        Spec.Dsa.decodeBE (Spec.Rsa.bytesAt m (A + BitVec.ofNat 64 pLen) qLen),
        Spec.Dsa.decodeBE (Spec.Rsa.bytesAt m (A + BitVec.ofNat 64 (pLen + qLen)) pLen)⟩,
        Spec.Dsa.decodeBE (Spec.Rsa.bytesAt m (A + BitVec.ofNat 64 (2 * pLen + qLen)) pLen),
        some (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt m (A + BitVec.ofNat 64 (3 * pLen + qLen)) qLen))⟩ := by
  rw [VG.Proof.Dsa.privateKeyBytes_at m A h, VG.Proof.Dsa.publicKeyBytes_at m A (by omega_arith)]

/-- A signing attempt, by the checks and values the body computes. -/
theorem signBytes_eq {pLen qLen P Q G Y X K : Nat} {key nonce digest : List Byte}
    (hv : Spec.Dsa.lengthsValid pLen qLen) (valid : shapeValid P Q)
    (hk : key.length = 3 * pLen + 2 * qLen) (hn : nonce.length = qLen)
    (kv : Spec.Dsa.privateKeyBytes pLen qLen key = ⟨⟨P, Q, G⟩, Y, some X⟩) (nv : Spec.Dsa.decodeBE nonce = K) :
    Spec.Dsa.signBytes pLen qLen key nonce digest =
      if signChecks P Q G Y X K (Spec.Dsa.decodeBE (digest.take (Spec.Dsa.bitLength Q / 8))) then
        some (Spec.Dsa.encodeBE qLen (rValue P Q G K) ++
          Spec.Dsa.encodeBE qLen (sValue P Q G X K (Spec.Dsa.decodeBE (digest.take (Spec.Dsa.bitLength Q / 8)))))
      else none := by
  rw [VG.Proof.Dsa.signBytes_compute hv valid hk hn kv nv (VG.Proof.Dsa.shape_digest_width valid).1]
  simp only [signChecks, rValue, sValue, and_assoc]

/-- The status word of a result in `r0`. -/
theorem status_toNat {u : State} {b : Prop} [Decidable b] (h : u.gpr .r0 = if b then 1 else 0) :
    (BitVec.setWidth 32 (u.gpr .r1 ++ u.gpr .r0)).toNat = if b then 1 else 0 := by
  rw [BitVec.setWidth_append_eq_right, h]
  by_cases hb : b <;> simp [hb]

/-- The key's components, at a state with the environment of signing. -/
theorem signKeyIn {s t : State} {base : Addr} {size : Nat} (h : signPre s) (hb : State.addr (arg s 5) = base)
    (hsz : (arg s 6).toNat * 8 = size) (E : Env s base size (signFields s) t) :
    Input t base size (.input .p) (arg s 0).toNat
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (arg s 0).toNat)) ∧
      Input t base size (.input .q) (arg s 2).toNat
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2) + BitVec.ofNat 64 (arg s 0).toNat)
          (arg s 2).toNat)) ∧
      Input t base size (.input .g) (arg s 0).toNat
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
          (State.addr (s.gpr .r2) + BitVec.ofNat 64 ((arg s 0).toNat + (arg s 2).toNat)) (arg s 0).toNat)) ∧
      Input t base size (.input .y) (arg s 0).toNat
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
          (State.addr (s.gpr .r2) + BitVec.ofNat 64 (2 * (arg s 0).toNat + (arg s 2).toNat)) (arg s 0).toNat)) ∧
      Input t base size (.input .x) (arg s 2).toNat
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
          (State.addr (s.gpr .r2) + BitVec.ofNat 64 (3 * (arg s 0).toNat + (arg s 2).toNat)) (arg s 2).toNat)) := by
  subst hb hsz
  obtain ⟨_, hrd, _, _, _, _, _, _, dKS, _, _, _, _, fK, _, _, _, hv, _, hr3, hsw⟩ := h
  have v := hv
  unfold Spec.Dsa.lengthsValid at v
  have hz : 12016 ≤ (arg s 6).toNat * 8 := by unfold Spec.Dsa.scratchWords at hsw; omega_arith
  have kr : (⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  have ip := input_of E (p := .input .p) (by decide : Impl.Dsa.Layout.Field.p ≠ .mask) (o := 0)
    (len := (arg s 0).toNat) (by rw [BitVec.add_zero]; exact E.field (d := 64) (v := s.gpr .r2) (by simp))
    kr fK (by omega_arith) (.inr rfl) dKS hz
  rw [BitVec.add_zero] at ip
  have cg := fun {a : Nat} {xs : List (BitVec 32)} (h : (xs.map BitVec.toNat).sum = a) =>
    (sum_ofNat (s.gpr .r2) xs).trans (congrArg (fun n => s.gpr .r2 + BitVec.ofNat 32 n) h)
  refine ⟨ip, input_of E (p := .input .q) (by decide : Impl.Dsa.Layout.Field.q ≠ .mask) ?_ kr fK (by omega_arith)
      (.inl (by omega_arith)) dKS hz,
    input_of E (p := .input .g) (by decide : Impl.Dsa.Layout.Field.g ≠ .mask) ?_ kr fK (by omega_arith)
      (.inl (by omega_arith)) dKS hz,
    input_of E (p := .input .y) (by decide : Impl.Dsa.Layout.Field.y ≠ .mask) ?_ kr fK (by omega_arith)
      (.inl (by omega_arith)) dKS hz,
    input_of E (p := .input .x) (by decide : Impl.Dsa.Layout.Field.x ≠ .mask) ?_ kr fK (by omega_arith)
      (.inl (by omega_arith)) dKS hz⟩
  · exact (E.field (d := 68) (v := s.gpr .r2 + arg s 0) (by simp)).trans (cg (xs := [arg s 0]) (by simp))
  · exact (E.field (d := 72) (v := s.gpr .r2 + arg s 0 + arg s 2) (by simp)).trans
      (cg (xs := [arg s 0, arg s 2]) (by simp))
  · exact (E.field (d := 76) (v := s.gpr .r2 + arg s 0 + arg s 2 + arg s 0) (by simp)).trans
      (cg (xs := [arg s 0, arg s 2, arg s 0]) (by simp; omega_arith))
  · exact (E.field (d := 80) (v := s.gpr .r2 + arg s 0 + arg s 2 + arg s 0 + arg s 0) (by simp)).trans
      (cg (xs := [arg s 0, arg s 2, arg s 0, arg s 0]) (by simp; omega_arith))

theorem signNonceIn {s t : State} {base : Addr} {size : Nat} (h : signPre s) (hb : State.addr (arg s 5) = base)
    (hsz : (arg s 6).toNat * 8 = size) (E : Env s base size (signFields s) t) :
    Input t base size (.input .nonce) (arg s 2).toNat
      (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (arg s 1)) (arg s 2).toNat)) := by
  subst hb hsz
  obtain ⟨_, hrd, _, _, _, _, _, _, _, dNS, _, _, _, _, fN, _, _, hv, _, _, hsw⟩ := h
  have v := hv
  unfold Spec.Dsa.lengthsValid at v
  have hz : 12016 ≤ (arg s 6).toNat * 8 := by unfold Spec.Dsa.scratchWords at hsw; omega_arith
  have nr : (⟨State.addr (arg s 1), (arg s 2).toNat⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  have In := input_of E (p := .input .nonce) (by decide : Impl.Dsa.Layout.Field.nonce ≠ .mask) (o := 0)
    (len := (arg s 2).toNat) (by rw [BitVec.add_zero]; exact E.field (d := 88) (v := arg s 1) (by simp))
    nr fN (by omega_arith) (.inr rfl) dNS hz
  rwa [BitVec.add_zero] at In

theorem signDigestIn {s t : State} {base : Addr} {size : Nat} (h : signPre s) (hb : State.addr (arg s 5) = base)
    (hsz : (arg s 6).toNat * 8 = size) (E : Env s base size (signFields s) t) {c : Nat}
    (hc : c ≤ (arg s 4).toNat) :
    Input t base size (.input .digest) c
      (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (arg s 3)) c)) := by
  subst hb hsz
  obtain ⟨_, hrd, _, _, _, _, _, _, _, _, dDS, _, _, _, _, fD, _, hv, _, _, hsw⟩ := h
  have v := hv
  unfold Spec.Dsa.lengthsValid at v
  have hz : 12016 ≤ (arg s 6).toNat * 8 := by unfold Spec.Dsa.scratchWords at hsw; omega_arith
  have dr : (⟨State.addr (arg s 3), (arg s 4).toNat⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  have Id := input_of E (p := .input .digest) (by decide : Impl.Dsa.Layout.Field.digest ≠ .mask) (o := 0)
    (len := c) (by rw [BitVec.add_zero]; exact E.field (d := 92) (v := arg s 3) (by simp))
    dr fD (by omega_arith) (.inr rfl) dDS hz
  rwa [BitVec.add_zero] at Id

theorem signOutput {s t : State} {base : Addr} {size : Nat} (h : signPre s) (hb : State.addr (arg s 5) = base)
    (hsz : (arg s 6).toNat * 8 = size) (E : Env s base size (signFields s) t) :
    Output t base size (2 * (arg s 2).toNat) := by
  subst hb hsz
  obtain ⟨_, _, hwr, _, _, _, dOS, _, _, _, _, _, fO, _, _, _, _, _, hr1, _, _⟩ := h
  have po : pointerValue (State.addr (arg s 5)) t (.input .out) = s.gpr .r0 :=
    E.field (d := 96) (v := s.gpr .r0) (by simp)
  refine ⟨by rw [po]; omega_arith, fun e k hek => ?_, by rw [po, ← hr1]; exact dOS⟩
  rw [po, E.wr, hwr]
  exact ⟨⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩

theorem sign_correct {s : State} (h : signPre s) :
    WP isa (Entry.operation umaal true) s fun t => abiPreserved s t ∧ signArm.post s t := by
  obtain ⟨hsp, hrd, hwr, _, _, _, dOS, _, dKS, dNS, dDS, _, fO, fK, fN, fD, fS, hv, hr1, hr3, hsw⟩ := id h
  have v := hv
  unfold Spec.Dsa.lengthsValid at v
  have hs16 : 128 * (arg s 0).toNat ≤ (arg s 6).toNat * 8 := by unfold Spec.Dsa.scratchWords at hsw; omega_arith
  obtain ⟨wp, wq, qp, q32, q0, p128⟩ := width_of hv
  simp only [Entry.operation, Core.sequence, List.foldr, ↓reduceIte]
  refine WP.seq (WP.mono (signEntry_ok h) fun u I => ?_)
  have E₀ := Env.of_installed I (by omega_arith)
  have fok := signFields_ok s
  refine WP.seq (widthDispatch_ok true _ E₀.ws (by omega_arith) (widths_mem hv) (by decide)
    (by rw [E₀.field (d := 100) (v := arg s 0) (by simp)]) (by rw [E₀.field (d := 104) (v := arg s 2) (by simp)]) fun t₁ R₁ M₁ => ?_)
  have E₁ := E₀.of_mem R₁ (by decide) M₁
  have hz : 12016 ≤ (arg s 6).toNat * 8 := by omega_arith
  have kr : (⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  obtain ⟨Ip₁, Iq₁, -, -, -⟩ := signKeyIn h rfl rfl E₁
  refine sized_ok true E₁.ws hz wp wq Ip₁.toReady Iq₁.toReady Ip₁.value Iq₁.value ?_ ?_
  · intro t₂ nv R₂ O₂
    have E₂ := E₁.keep fok R₂ (by decide) O₂ (fun r hr => by
      simp only [shapeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only <;> omega_arith)
    have po : pointerValue (State.addr (arg s 5)) t₂ (.input .out) = s.gpr .r0 :=
      E₂.field (d := 96) (v := s.gpr .r0) (by simp)
    refine WP.mono (failure_ok E₂.ws (by omega_arith) (signOutput h rfl rfl E₂) (by rw [E₂.field (d := 104) (v := arg s 2) (by simp)])
      q0 q32) fun t₃ ⟨Z₃, B₃, R₃, O₃⟩ => ?_
    rw [po] at B₃ O₃
    have none : signRes s = none :=
      VG.Proof.Dsa.signBytes_invalid_shape (by rw [signKey _ _ (by omega_arith)]; exact nv)
    refine finish_ok (E₂.ws.of_rest R₃ (by decide)) (by omega_arith) (E₂.saved_outside O₃ (hr1 ▸ dOS) (by omega_arith))
      (R₃.sp.trans E₂.sp) fun u A r0 M => ⟨A, ?_, ?_⟩
    · rw [BitVec.setWidth_append_eq_right, r0, Z₃, none]; rfl
    · rw [M, hr1, B₃, none]; rfl
  · intro t₂ valid hm D₂ R₂ O₂
    have E₂ := E₁.keep fok R₂ (by decide) O₂ (fun r hr => by
      simp only [shapeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only <;> omega_arith)
    have po : pointerValue (State.addr (arg s 5)) t₂ (.input .out) = s.gpr .r0 :=
      E₂.field (d := 96) (v := s.gpr .r0) (by simp)
    obtain ⟨Ip, Iq, Ig, Iy, Ix⟩ := signKeyIn h rfl rfl E₂
    have In := signNonceIn h rfl rfl E₂
    have Id := signDigestIn h rfl rfl E₂ (Nat.min_le_left (arg s 4).toNat (qWidth (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
        (State.addr (s.gpr .r2) + BitVec.ofNat 64 (arg s 0).toNat) (arg s 2).toNat))))
    have hc : countValue (State.addr (arg s 5)) t₂ Core.digestPrefix = min (arg s 4).toNat (qWidth
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
          (State.addr (s.gpr .r2) + BitVec.ofNat 64 (arg s 0).toNat) (arg s 2).toNat))) := by
      refine D₂.trans ?_
      rw [E₁.field (d := 108) (v := arg s 4) (by simp)]
    rw [VG.Proof.Dsa.bytesAt_prefix, qWidth_of_shape valid] at Id
    rw [qWidth_of_shape valid] at hc
    obtain ⟨hP, hPo, hQ, hQo⟩ := shape_bounds valid
    refine WP.mono (signBody_ok ⟨E₂.ws, by omega_arith, wp, wq, qp, q32⟩ Ip Iq Ig Iy Ix In Id hc hP hPo hQ hQo hm
      (signOutput h rfl rfl E₂)) fun t₃ ⟨Z₃, B₃, Bd₃⟩ => ?_
    rw [po] at B₃ Bd₃
    have SR : signRes s = _ := signBytes_eq (nonce := Spec.Rsa.bytesAt s.mem (State.addr (arg s 1)) (arg s 2).toNat) (digest := Spec.Rsa.bytesAt s.mem (State.addr (arg s 3)) (arg s 4).toNat) hv valid
      (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]; exact hr3)
      (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]) (signKey _ _ (by omega_arith)) rfl
    refine finish_ok (E₂.ws.of_rest Bd₃.rest (by decide)) (by omega_arith) (E₂.saved_body Bd₃ (hr1 ▸ dOS) (by omega_arith))
      (Bd₃.rest.sp.trans E₂.sp) fun u A r0 M => ⟨A, ?_, ?_⟩
    · rw [BitVec.setWidth_append_eq_right, r0, Z₃, SR]
      split <;> rfl
    · rw [M, hr1, B₃, SR]
      split <;> rfl

end VG.Proof.Dsa.Arm
