import VerifiedGarbage.Proof.Rsa.X86_64.PrivCtx
import VerifiedGarbage.Proof.Bignum.X86_64.PubVerified
import VerifiedGarbage.Spec.RsaPss.Contract
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant

/-!
# RSASSA-PSS signing on x86-64: the contract on the registers

`signK G` states `Spec.RsaPss.signContract G G` (with the stack the frame
and the calls use, `signStack`) on the registers and the stack
(`sign_implies`).
-/

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum.X86_64

/-- The stack below the stack pointer: the frame, the return address of
its calls, and what `vg_rsa_private_checked` uses below that. -/
def signStack : Nat := 392 + 8 + Proof.Rsa.X86_64.stackBytes

theorem stackArgs_fifteen (s : State) :
    List.map (stackArg s) (List.range 15) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11, stackArg s 12, stackArg s 13, stackArg s 14] := rfl

variable (G : Spec.Mgf1.Hash)

/-- `sign(out = rdi, out_len = rsi, n = rdx, n_len = rcx, e = r8, e_len = r9,
p = [rsp + 8], p_len, q, q_len, dp, dp_len, dq, dq_len, qinv, qinv_len,
digest = [rsp + 88], salt, salt_len, scratch, scratch_len = [rsp + 120])`. -/
def signK : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let n : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let e : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
    let p : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
    let q : Region := ⟨stackArg s 2, (stackArg s 3).toNat⟩
    let dp : Region := ⟨stackArg s 4, (stackArg s 5).toNat⟩
    let dq : Region := ⟨stackArg s 6, (stackArg s 7).toNat⟩
    let qi : Region := ⟨stackArg s 8, (stackArg s 9).toNat⟩
    let dg : Region := ⟨stackArg s 10, G.len⟩
    let sa : Region := ⟨stackArg s 11, (stackArg s 12).toNat⟩
    let scr : Region := ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 120⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stk : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩
    signStack ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 128 ≤ 2 ^ 64 ∧
      s.rd = [n, e, p, q, dp, dq, qi, dg, sa, args] ∧ s.wr = [out, scr] ∧
      out.Disjoint n ∧ out.Disjoint e ∧ out.Disjoint p ∧ out.Disjoint q ∧ out.Disjoint dp ∧
      out.Disjoint dq ∧ out.Disjoint qi ∧ out.Disjoint dg ∧ out.Disjoint sa ∧ out.Disjoint scr ∧
      out.Disjoint args ∧
      n.Disjoint scr ∧ e.Disjoint scr ∧ p.Disjoint scr ∧ q.Disjoint scr ∧ dp.Disjoint scr ∧
      dq.Disjoint scr ∧ qi.Disjoint scr ∧ dg.Disjoint scr ∧ sa.Disjoint scr ∧ scr.Disjoint args ∧
      ret.Disjoint out ∧ ret.Disjoint n ∧ ret.Disjoint e ∧ ret.Disjoint p ∧ ret.Disjoint q ∧
      ret.Disjoint dp ∧ ret.Disjoint dq ∧ ret.Disjoint qi ∧ ret.Disjoint dg ∧ ret.Disjoint sa ∧
      ret.Disjoint scr ∧ ret.Disjoint args ∧
      stk.Disjoint out ∧ stk.Disjoint n ∧ stk.Disjoint e ∧ stk.Disjoint p ∧ stk.Disjoint q ∧
      stk.Disjoint dp ∧ stk.Disjoint dq ∧ stk.Disjoint qi ∧ stk.Disjoint dg ∧ stk.Disjoint sa ∧
      stk.Disjoint scr ∧ stk.Disjoint args ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧
      (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 64 ∧ (stackArg s 4).toNat + (stackArg s 5).toNat ≤ 2 ^ 64 ∧
      (stackArg s 6).toNat + (stackArg s 7).toNat ≤ 2 ^ 64 ∧ (stackArg s 8).toNat + (stackArg s 9).toNat ≤ 2 ^ 64 ∧
      (stackArg s 10).toNat + G.len ≤ 2 ^ 64 ∧ (stackArg s 11).toNat + (stackArg s 12).toNat ≤ 2 ^ 64 ∧
      (stackArg s 13).toNat + (stackArg s 14).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .rcx).toNat ∧ (s.gpr .rsi).toNat = (s.gpr .rcx).toNat ∧
      1 ≤ (s.gpr .r9).toNat ∧ (s.gpr .r9).toNat ≤ (s.gpr .rcx).toNat ∧
      1 ≤ (stackArg s 1).toNat ∧ (stackArg s 1).toNat < (s.gpr .rcx).toNat ∧ 1 ≤ (stackArg s 3).toNat ∧
      (stackArg s 3).toNat < (s.gpr .rcx).toNat ∧ (stackArg s 5).toNat = (stackArg s 1).toNat ∧
      (stackArg s 9).toNat = (stackArg s 1).toNat ∧ (stackArg s 7).toNat = (stackArg s 3).toNat ∧
      Spec.RsaPss.scratchWords (s.gpr .rcx).toNat ≤ (stackArg s 14).toNat
  post s s' :=
    Spec.Rsa.writtenOutcome s'.mem (s.gpr .rdi) (s.gpr .rcx).toNat ((s'.gpr .rax).setWidth 32)
      (Spec.RsaPss.sign G G (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 6) (stackArg s 3).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 1).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 10) G.len)
        (Spec.Rsa.bytesAt s.mem (stackArg s 11) (stackArg s 12).toNat))
  pub s₁ s₂ :=
    (∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₁.gpr r = s₂.gpr r) ∧
      (List.range 15).map (stackArg s₁) = (List.range 15).map (stackArg s₂) ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .rdx) (s₁.gpr .rcx).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .rdx) (s₂.gpr .rcx).toNat ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r8) (s₁.gpr .r9).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r8) (s₂.gpr .r9).toNat

/-- A state meeting `signK.pre`: as `chkSatState`, with a digest and an
empty salt. -/
def signSatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 64 | .rdx => 0x2000 | .rcx => 64 | .r8 => 0x3000 | .r9 => 1
    | .rsp => 0x10000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x10009 then 0x41 else if a = 0x10010 then 1 else if a = 0x10019 then 0x42
    else if a = 0x10020 then 1 else if a = 0x10029 then 0x43 else if a = 0x10030 then 1
    else if a = 0x10039 then 0x44 else if a = 0x10040 then 1 else if a = 0x10049 then 0x45
    else if a = 0x10050 then 1 else if a = 0x10059 then 0x46 else if a = 0x10061 then 0x47
    else if a = 0x10072 then 0x02 else if a = 0x10079 then 0x08 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4100, 1⟩, ⟨0x4200, 1⟩, ⟨0x4300, 1⟩, ⟨0x4400, 1⟩, ⟨0x4500, 1⟩,
    ⟨0x4600, G.len⟩, ⟨0x4700, 0⟩, ⟨0x10008, 120⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x20000, 2048 * 8⟩]

/-- `signContract` is satisfiable for each of `MdHash`'s hash functions. -/
theorem sign_sat (hG : G ∈ Pbkdf2.Md.X86_64.mdHashes) :
    ∃ s, (Spec.RsaPss.signContract G G abi signStack).pre s := by
  simp only [Pbkdf2.Md.X86_64.mdHashes, List.mem_cons, List.not_mem_nil, or_false] at hG
  rcases hG with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · sig_implies_sat [Spec.RsaPss.signContract, Spec.RsaPss.signSig, abi, argRegs, signK, signStack, stackArgs_fifteen, List.append_eq] [signSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using signSatState Spec.Mgf1.md5
  · sig_implies_sat [Spec.RsaPss.signContract, Spec.RsaPss.signSig, abi, argRegs, signK, signStack, stackArgs_fifteen, List.append_eq] [signSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using signSatState Spec.Mgf1.sha1
  · sig_implies_sat [Spec.RsaPss.signContract, Spec.RsaPss.signSig, abi, argRegs, signK, signStack, stackArgs_fifteen, List.append_eq] [signSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using signSatState Spec.Mgf1.sha224
  · sig_implies_sat [Spec.RsaPss.signContract, Spec.RsaPss.signSig, abi, argRegs, signK, signStack, stackArgs_fifteen, List.append_eq] [signSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using signSatState Spec.Mgf1.sha256
  · sig_implies_sat [Spec.RsaPss.signContract, Spec.RsaPss.signSig, abi, argRegs, signK, signStack, stackArgs_fifteen, List.append_eq] [signSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using signSatState Spec.Mgf1.sha384
  · sig_implies_sat [Spec.RsaPss.signContract, Spec.RsaPss.signSig, abi, argRegs, signK, signStack, stackArgs_fifteen, List.append_eq] [signSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using signSatState Spec.Mgf1.sha512
  · sig_implies_sat [Spec.RsaPss.signContract, Spec.RsaPss.signSig, abi, argRegs, signK, signStack, stackArgs_fifteen, List.append_eq] [signSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using signSatState Spec.Mgf1.sha512_224
  · sig_implies_sat [Spec.RsaPss.signContract, Spec.RsaPss.signSig, abi, argRegs, signK, signStack, stackArgs_fifteen, List.append_eq] [signSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using signSatState Spec.Mgf1.sha512_256

theorem sign_implies (hsat : ∃ s, (Spec.RsaPss.signContract G G abi signStack).pre s) : (signK G).Implies (Spec.RsaPss.signContract G G abi signStack) where
  pre := by
    intro s h
    sig_pre [Spec.RsaPss.signContract, Spec.RsaPss.signSig, abi, argRegs, signK, signStack, stackArgs_fifteen, List.append_eq] at h
    sig_pre [Spec.RsaPss.signContract, Spec.RsaPss.signSig, abi, argRegs, signK, signStack, stackArgs_fifteen, List.append_eq] at h
    sig_split h
    sig_reduce [Spec.RsaPss.signContract, Spec.RsaPss.signSig, abi, argRegs, signK, signStack, stackArgs_fifteen, List.append_eq]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by sig_implies_post [Spec.RsaPss.signContract, Spec.RsaPss.signSig, abi, argRegs, signK, signStack, stackArgs_fifteen, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.RsaPss.signContract, Spec.RsaPss.signSig, abi, argRegs, signK, signStack, stackArgs_fifteen, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩ := h
    obtain ⟨hn, he⟩ := leak_eq (by simp [Spec.Rsa.bytesAt, hcx]) hl
    refine ⟨?_, by simp only [stackArgs_fifteen, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14],
      hn, he⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := hsat

end VG.Proof.RsaPss.X86_64
