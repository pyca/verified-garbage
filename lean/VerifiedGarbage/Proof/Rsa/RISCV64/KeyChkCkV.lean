module

public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyChkCk
public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyChkCT
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Rsa.RISCV64.KeyChkCk
meta import VerifiedGarbage.Proof.Rsa.RISCV64.KeyChkCT
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.TCB.RISCV64.Target

/-!
# `vg_rsa_check_key` on RISC-V: verified

`ck_ct`: constant time, from `fn_rel` with the function's pieces (`ckKC`,
`ck_ok`) and the taint checks of its own code; `ck_verified`: against the
shared contract `Spec.Rsa.checkKeyContract`.
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.KeyCheck

open VG VG.RISCV64 VG.RISCV64.Taint VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Keys
open VG.Impl.Rsa.RISCV64.KeyCheck
open VG.Proof.Bignum.RISCV64.Pre (Two Pins two_post two_taint)

/-- The public data of `vg_rsa_check_key`: the arguments, `n` and `e`. -/
def ckData (s : State) : List (BitVec 64) × List (BitVec 64) × List Nat × Addr :=
  (argRegs.map s.gpr, (List.range 10).map (stackArg s),
    (Spec.Rsa.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat ++
      Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat).map (·.toNat), s.sp)

/-- `vg_rsa_check_key`, as `fn_rel` needs it. -/
def ckKC : KC (List (BitVec 64) × List (BitVec 64) × List Nat × Addr) where
  Pre := (Spec.Rsa.checkKeyContract RISCV64.abi).pre
  D := ckData
  B s := stackArg s 8
  Z s := (stackArg s 9).toNat * 8
  K s := (s.gpr .a1).toNat
  E s := s.gpr .a2
  L s := (s.gpr .a3).toNat
  N s := s.gpr .a0
  MV := CkRegs

theorem ck_same {s t : State} (h : ckData s = ckData t) :
    (∀ r ∈ argRegs, s.gpr r = t.gpr r) ∧ (∀ i < 10, stackArg s i = stackArg t i) ∧
      Spec.Rsa.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat = Spec.Rsa.bytesAt t.mem (t.gpr .a0) (t.gpr .a1).toNat ∧
      Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat = Spec.Rsa.bytesAt t.mem (t.gpr .a2) (t.gpr .a3).toNat := by
  simp only [ckData, Prod.mk.injEq] at h
  obtain ⟨hr, ha, hb, -⟩ := h
  have gr : ∀ r ∈ argRegs, s.gpr r = t.gpr r := List.map_inj_left.mp hr
  have h1 : s.gpr .a1 = t.gpr .a1 := gr _ (by decide)
  rw [List.map_append, List.map_append] at hb
  obtain ⟨hn, he⟩ := List.append_inj hb (by simp [len_bytes, h1])
  exact ⟨gr, fun i hi => List.map_inj_left.mp ha i (List.mem_range.mpr hi),
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hn,
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 he⟩

theorem ck_ok : ckKC.Ok 8 10 VG.Impl.Rsa.RISCV64.CheckKey.moves
    (([setup, .block eArr] : List (Prog isa)) ++ VG.Impl.Rsa.RISCV64.CheckKey.loads ++ (start ++ crtChecks ++ dChecks) ++
      ([.block ret] : List (Prog isa))) ckRegs where
  hk s h := ck_kpre (ckP_of h)
  hm s h := ck_moves_ok (ckP_of h)
  hL s h := by
    have h0 := ckP_of h
    have := h0.lv; have := h0.e1; have := h0.e2
    simp only [Spec.Rsa.lenValid] at *
    show 1 ≤ (s.gpr .a3).toNat ∧ (s.gpr .a3).toNat ≤ 1024
    exact ⟨h0.e1, by omega⟩
  hE s h := by
    have h0 := ckP_of h
    exact ⟨by rw [h0.hrd]; simp [ckKC], h0.de, h0.we⟩
  hN s h := by
    have h0 := ckP_of h
    exact ⟨by rw [h0.hrd]; simp [ckKC], h0.dn, h0.wn⟩
  hv s h v t mv kt bt h4 ev mv' := WP.mono (ck_valid (ckP_of h) bt (mv.of_keep kt) h4 ev mv') fun _ h => h.1
  hsame s t _ _ hd := by
    obtain ⟨gr, ga, hn, he⟩ := ck_same hd
    have g0 := gr .a0 (by decide); have g1 := gr .a1 (by decide)
    have g2 := gr .a2 (by decide); have g3 := gr .a3 (by decide)
    exact ⟨ga 8 (by decide), g2, g0, by simp only [ckKC, g3], by simp only [ckKC, g1], he, hn, gr⟩
  hmv s t v w _ _ hd mv mw := by
    obtain ⟨gr, ga, -, -⟩ := ck_same hd
    intro r hr
    simp only [ckRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [mv.s1, mw.s1, gr _ (by decide)]
    · rw [mv.s2, mw.s2, gr _ (by decide)]
    · rw [mv.s3, mw.s3, gr _ (by decide)]
    · rw [mv.s4, mw.s4, gr _ (by decide)]
    · rw [mv.a0, mw.a0, gr _ (by decide)]
    · rw [mv.a1, mw.a1, gr _ (by decide)]
    · rw [mv.s5, mw.s5, ga _ (by decide)]
    · rw [mv.s6, mw.s6, ga _ (by decide)]
    · rw [mv.a2, mw.a2, ga _ (by decide)]
    · rw [mv.a3, mw.a3, ga _ (by decide)]
    · rw [mv.a6, mw.a6, ga _ (by decide)]
  hmr := by decide

theorem ck_rel : RelCT isa (Two ckKC.C0) VG.Impl.Rsa.RISCV64.CheckKey.code fun _ _ => True := by
  unfold VG.Impl.Rsa.RISCV64.CheckKey.code
  show RelCT isa _ (fn (8 * 8) _ _ _) _
  exact fn_rel ckKC ck_ok (by decide) (by taint_decide) (by taint_decide) (by taint_decide)

theorem ck_pub_data {s₁ s₂ : State} (h : (Spec.Rsa.checkKeyContract RISCV64.abi).pub s₁ s₂) :
    ckData s₁ = ckData s₂ := by
  sig_pub [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, RISCV64.abi, RISCV64.argRegs,
    stackArgs_ten, List.append_eq] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hl, h3, h4, h5, h6, h7, h8, h9, h10, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h
  unfold ckData
  rw [hl]
  simp only [argRegs, List.map_cons, List.map_nil, stackArgs_ten, h3, h4, h5, h6, h7, h8, h9, h10, a0,
    a1, a2, a3, a4, a5, a6, a7, a8, a9, hsp]

theorem ck_ct : ConstantTime isa (Spec.Rsa.checkKeyContract RISCV64.abi).pre
    (Spec.Rsa.checkKeyContract RISCV64.abi).pub VG.Impl.Rsa.RISCV64.CheckKey.code :=
  RelCT.constantTime (ck_rel.mono (fun s _ ⟨hs, ht, hp⟩ =>
    ⟨ckData s, ⟨hs, rfl⟩, ⟨ht, (ck_pub_data hp).symm⟩, congrArg (·.2.2.2) (ck_pub_data hp)⟩) fun _ _ h => h)

/-- `vg_rsa_check_key` on the registers and the stack, with its result. -/
def ckContract : Contract isa where
  pre := (Spec.Rsa.checkKeyContract RISCV64.abi).pre
  post := ckPost
  pub := (Spec.Rsa.checkKeyContract RISCV64.abi).pub

/-- A state meeting the precondition: a 64-byte modulus, one-byte other
numbers, and the stack arguments at `0x10000`. -/
def ckSatState : State where
  gpr r := match r with
    | .a0 => 0x2000 | .a1 => 64 | .a2 => 0x3000 | .a3 => 1 | .a4 => 0x3100 | .a5 => 1
    | .a6 => 0x3200 | .a7 => 1 | _ => 0
  sp := 0x10000
  mem a :=
    bif Nat.beq a.toNat 0x10001 then 0x33 else bif Nat.beq a.toNat 0x10008 then 1
    else bif Nat.beq a.toNat 0x10011 then 0x34 else bif Nat.beq a.toNat 0x10018 then 1
    else bif Nat.beq a.toNat 0x10021 then 0x35 else bif Nat.beq a.toNat 0x10028 then 1
    else bif Nat.beq a.toNat 0x10031 then 0x36 else bif Nat.beq a.toNat 0x10038 then 1
    else bif Nat.beq a.toNat 0x10041 then 0x80 else bif Nat.beq a.toNat 0x10048 then 0x20
    else bif Nat.beq a.toNat 0x10049 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x3100, 1⟩, ⟨0x3200, 1⟩, ⟨0x3300, 1⟩, ⟨0x3400, 1⟩, ⟨0x3500, 1⟩,
    ⟨0x3600, 1⟩, ⟨0x10000, 80⟩]
  wr := [⟨0x8000, 8448⟩]

theorem ck_implies : ckContract.Implies (Spec.Rsa.checkKeyContract RISCV64.abi) where
  pre := fun _ h => h
  post := by
    sig_implies_post [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, RISCV64.abi,
      RISCV64.argRegs, ckContract, ckPost, ckOk, stackArgs_ten, List.append_eq]
  pub := fun _ _ _ _ h => h
  sat := by
    sig_implies_sat [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, RISCV64.abi,
      RISCV64.argRegs, ckContract, stackArgs_ten, List.append_eq] [ckSatState, stackArg, stackArgAddr,
      Mem.readW, Mem.read] using ckSatState

/-- `vg_rsa_check_key`. -/
theorem ck_verified :
    Verified RISCV64.target VG.Impl.Rsa.RISCV64.CheckKey.code (Spec.Rsa.checkKeyContract RISCV64.abi) :=
  Verified.of_correct ck_correct ck_ct ck_implies

end VG.Proof.Rsa.RISCV64.KeyCheck
