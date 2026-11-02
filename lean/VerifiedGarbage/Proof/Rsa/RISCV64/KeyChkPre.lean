module

public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyChkFn
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_rsa_check_key` and `vg_rsa_check_crt_key` on RISC-V: the preconditions

`CkP s`, `CckP s`: the shared contracts' preconditions (`checkKeyContract`,
`checkCrtKeyContract`), by name (`ckP_of`, `cckP_of`), and what the shared
proofs use of them (`ck_kpre`, `cck_kpre`).
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.KeyCheck

open VG VG.RISCV64

theorem stackArgs_ten (s : State) :
    List.map (stackArg s) (List.range 10) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9] := rfl

theorem stackArgs_eight (s : State) :
    List.map (stackArg s) (List.range 8) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7] := rfl

/-! ## `vg_rsa_check_key` -/

abbrev rgA (s : State) (a l : Reg) : Region := ⟨s.gpr a, (s.gpr l).toNat⟩
abbrev rgS (s : State) (a l : Nat) : Region := ⟨stackArg s a, (stackArg s l).toNat⟩

/-- `vg_rsa_check_key`'s working space. -/
abbrev ckScr (s : State) : Region := ⟨stackArg s 8, (stackArg s 9).toNat * 8⟩

structure CkP (s : State) : Prop where
  sp16 : s.sp.toNat % 16 = 0
  sp2 : s.sp.toNat + 80 ≤ 2 ^ 64
  hrd : s.rd = [rgA s .a0 .a1, rgA s .a2 .a3, rgA s .a4 .a5, rgA s .a6 .a7, rgS s 0 1, rgS s 2 3, rgS s 4 5,
    rgS s 6 7, ⟨stackArgAddr s 0, 80⟩]
  hwr : s.wr = [ckScr s]
  dn : (rgA s .a0 .a1).Disjoint (ckScr s)
  de : (rgA s .a2 .a3).Disjoint (ckScr s)
  dd : (rgA s .a4 .a5).Disjoint (ckScr s)
  dp : (rgA s .a6 .a7).Disjoint (ckScr s)
  dq : (rgS s 0 1).Disjoint (ckScr s)
  ddp : (rgS s 2 3).Disjoint (ckScr s)
  ddq : (rgS s 4 5).Disjoint (ckScr s)
  dqi : (rgS s 6 7).Disjoint (ckScr s)
  dsa : (ckScr s).Disjoint ⟨stackArgAddr s 0, 80⟩
  wn : (s.gpr .a0).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64
  we : (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64
  wd : (s.gpr .a4).toNat + (s.gpr .a5).toNat ≤ 2 ^ 64
  wp : (s.gpr .a6).toNat + (s.gpr .a7).toNat ≤ 2 ^ 64
  wq : (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64
  wdp : (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 64
  wdq : (stackArg s 4).toNat + (stackArg s 5).toNat ≤ 2 ^ 64
  wqi : (stackArg s 6).toNat + (stackArg s 7).toNat ≤ 2 ^ 64
  ws : (stackArg s 8).toNat + (stackArg s 9).toNat * 8 ≤ 2 ^ 64
  lv : Spec.Rsa.lenValid (s.gpr .a1).toNat
  e1 : 1 ≤ (s.gpr .a3).toNat
  e2 : (s.gpr .a3).toNat ≤ (s.gpr .a1).toNat
  d1 : 1 ≤ (s.gpr .a5).toNat
  d2 : (s.gpr .a5).toNat ≤ (s.gpr .a1).toNat
  p1 : 1 ≤ (s.gpr .a7).toNat
  p2 : (s.gpr .a7).toNat < (s.gpr .a1).toNat
  q1 : 1 ≤ (stackArg s 1).toNat
  q2 : (stackArg s 1).toNat < (s.gpr .a1).toNat
  hdp : (stackArg s 3).toNat = (s.gpr .a7).toNat
  hqi : (stackArg s 7).toNat = (s.gpr .a7).toNat
  hdq : (stackArg s 5).toNat = (stackArg s 1).toNat
  hs : Spec.Rsa.scratchWords (s.gpr .a1).toNat ≤ (stackArg s 9).toNat
  al : (stackArg s 8).toNat % 8 = 0

theorem ckP_of {s : State} (h : (Spec.Rsa.checkKeyContract RISCV64.abi).pre s) : CkP s := by
  sig_pre [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, RISCV64.abi, RISCV64.argRegs,
    stackArgs_ten, List.append_eq, List.range, List.range.loop] at h
  obtain ⟨sp16, sp2, hrd, hwr, dn, de, dd, dp, dq, ddp, ddq, dqi, dsa, wn, we, wd, wp, wq, wdp, wdq, wqi, ws,
    lv, e1, e2, d1, d2, p1, p2, q1, q2, hdp, hqi, hdq, hs, al⟩ := h
  exact ⟨sp16, sp2, hrd, hwr, dn, de, dd, dp, dq, ddp, ddq, dqi, dsa, wn, we, wd, wp, wq, wdp, wdq, wqi, ws,
    lv, e1, e2, d1, d2, p1, p2, q1, q2, hdp, hqi, hdq, hs, al⟩

theorem ck_kpre {s : State} (h : CkP s) :
    KPre s (stackArg s 8) ((stackArg s 9).toNat * 8) (s.gpr .a1).toNat 8 10 := by
  have hs := h.hs
  have lv := h.lv
  simp only [Spec.Rsa.scratchWords] at hs
  simp only [Spec.Rsa.lenValid] at lv
  exact ⟨by rw [h.hwr]; simp, h.ws, h.al, by omega, lv.1, lv.2, by have := h.sp2; omega, h.sp16,
    by rw [h.hrd]; simp, h.dsa, rfl, by decide, rfl⟩

/-! ## `vg_rsa_check_crt_key` -/

/-- `vg_rsa_check_crt_key`'s working space. -/
abbrev cckScr (s : State) : Region := ⟨stackArg s 6, (stackArg s 7).toNat * 8⟩

structure CckP (s : State) : Prop where
  sp16 : s.sp.toNat % 16 = 0
  sp2 : s.sp.toNat + 64 ≤ 2 ^ 64
  hrd : s.rd = [rgA s .a0 .a1, rgA s .a2 .a3, rgA s .a4 .a5, rgA s .a6 .a7, rgS s 0 1, rgS s 2 3, rgS s 4 5,
    ⟨stackArgAddr s 0, 64⟩]
  hwr : s.wr = [cckScr s]
  dn : (rgA s .a0 .a1).Disjoint (cckScr s)
  de : (rgA s .a2 .a3).Disjoint (cckScr s)
  dp : (rgA s .a4 .a5).Disjoint (cckScr s)
  dq : (rgA s .a6 .a7).Disjoint (cckScr s)
  ddp : (rgS s 0 1).Disjoint (cckScr s)
  ddq : (rgS s 2 3).Disjoint (cckScr s)
  dqi : (rgS s 4 5).Disjoint (cckScr s)
  dsa : (cckScr s).Disjoint ⟨stackArgAddr s 0, 64⟩
  wn : (s.gpr .a0).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64
  we : (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64
  wp : (s.gpr .a4).toNat + (s.gpr .a5).toNat ≤ 2 ^ 64
  wq : (s.gpr .a6).toNat + (s.gpr .a7).toNat ≤ 2 ^ 64
  wdp : (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64
  wdq : (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 64
  wqi : (stackArg s 4).toNat + (stackArg s 5).toNat ≤ 2 ^ 64
  ws : (stackArg s 6).toNat + (stackArg s 7).toNat * 8 ≤ 2 ^ 64
  lv : Spec.Rsa.lenValid (s.gpr .a1).toNat
  e1 : 1 ≤ (s.gpr .a3).toNat
  e2 : (s.gpr .a3).toNat ≤ (s.gpr .a1).toNat
  p1 : 1 ≤ (s.gpr .a5).toNat
  p2 : (s.gpr .a5).toNat < (s.gpr .a1).toNat
  q1 : 1 ≤ (s.gpr .a7).toNat
  q2 : (s.gpr .a7).toNat < (s.gpr .a1).toNat
  hdp : (stackArg s 1).toNat = (s.gpr .a5).toNat
  hqi : (stackArg s 5).toNat = (s.gpr .a5).toNat
  hdq : (stackArg s 3).toNat = (s.gpr .a7).toNat
  hs : Spec.Rsa.scratchWords (s.gpr .a1).toNat ≤ (stackArg s 7).toNat
  al : (stackArg s 6).toNat % 8 = 0

theorem cckP_of {s : State} (h : (Spec.Rsa.checkCrtKeyContract RISCV64.abi).pre s) : CckP s := by
  sig_pre [Spec.Rsa.checkCrtKeyContract, Spec.Rsa.checkCrtKeySig, RISCV64.abi, RISCV64.argRegs,
    stackArgs_eight, List.append_eq, List.range, List.range.loop] at h
  obtain ⟨sp16, sp2, hrd, hwr, dn, de, dp, dq, ddp, ddq, dqi, dsa, wn, we, wp, wq, wdp, wdq, wqi, ws,
    lv, e1, e2, p1, p2, q1, q2, hdp, hqi, hdq, hs, al⟩ := h
  exact ⟨sp16, sp2, hrd, hwr, dn, de, dp, dq, ddp, ddq, dqi, dsa, wn, we, wp, wq, wdp, wdq, wqi, ws,
    lv, e1, e2, p1, p2, q1, q2, hdp, hqi, hdq, hs, al⟩

theorem cck_kpre {s : State} (h : CckP s) :
    KPre s (stackArg s 6) ((stackArg s 7).toNat * 8) (s.gpr .a1).toNat 6 8 := by
  have hs := h.hs
  have lv := h.lv
  simp only [Spec.Rsa.scratchWords] at hs
  simp only [Spec.Rsa.lenValid] at lv
  exact ⟨by rw [h.hwr]; simp, h.ws, h.al, by omega, lv.1, lv.2, by have := h.sp2; omega, h.sp16,
    by rw [h.hrd]; simp, h.dsa, rfl, by decide, rfl⟩

end VG.Proof.Rsa.RISCV64.KeyCheck
