module

public import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.PublicKey
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.SignCached
import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.Sha512OK
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Impl.Ed25519.RISCV64.Whole
public import VerifiedGarbage.Proof.Ed25519.RISCV64.PointOps
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.Common
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Proof.Framework.Contract

/-!
# Ed25519's public key and signing on RISC-V, by register

Each function, with its frame as one more argument, meets a contract of its
facts by register (`pkCE`, `signCE`), from an aligned `scratch` and frame, and
208 bytes of stack below the stack pointer for the callees' frames
(`pkE_ok`, `signE_ok`). Their constant time is `publicKeyExpanded_ct` and
`signExpanded_ct`.
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64.Whole

open VG VG.RISCV64 VG.Impl.Ed25519.RISCV64.Whole
open VG.Spec.Ed25519 (bytesAt)
open VG.Impl.Ed25519.RISCV64 (combSym combConsts)

/-- The stack the contract reserves. -/
theorem below_reserved (s : State) : below s.sp 208 ∈ RISCV64.abi.reserved 208 s := by
  show _ ∈ stackBelow s.sp 208
  rw [stackBelow_pos _ (by decide)]; simp

/-- The contract by register: `out` in `a0`, `expanded` (the seed's digest, 64 bytes) in `a1`,
`scratch` in `a2`, the frame in `a3`; without the comb's table. -/
def pkRE : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .a0, 32⟩
    let ex : Region := ⟨s.gpr .a1, 64⟩
    let sc : Region := ⟨s.gpr .a2, 8192⟩
    let fr : Region := ⟨s.gpr .a3, 144⟩
    s.rd = [ex] ∧ s.wr = [out, sc, fr] ∧ out.Disjoint ex ∧ out.Disjoint sc ∧ out.Disjoint fr ∧
      ex.Disjoint sc ∧ ex.Disjoint fr ∧ sc.Disjoint fr ∧ (s.gpr .a2).toNat % 8 = 0 ∧
      (s.gpr .a3).toNat % 8 = 0 ∧ s.sp.toNat % 16 = 0 ∧ 208 ≤ s.sp.toNat ∧
      (below s.sp 208).Disjoint out ∧ (below s.sp 208).Disjoint ex ∧ (below s.sp 208).Disjoint sc ∧
      (below s.sp 208).Disjoint fr ∧
      ∃ seed : List Byte, seed.length = 32 ∧ bytesAt s.mem (s.gpr .a1) 64 = Spec.Sha512.sha512 seed
  post s s' := ∀ seed : List Byte, seed.length = 32 → bytesAt s.mem (s.gpr .a1) 64 = Spec.Sha512.sha512 seed →
    bytesAt s'.mem (s.gpr .a0) 32 = Spec.Ed25519.publicKey seed
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp

/-- `pkRE` with the comb's table (`abi.withConsts`): `pkRE` for the state without it, and what the
table adds. -/
def pkCE : Contract isa where
  pre s := pkRE.pre (stripConsts combConsts s) ∧ ConstsOk combConsts 208 s
  post := pkRE.post
  pub s₁ s₂ := pkRE.pub s₁ s₂ ∧ s₁.syms combSym = s₂.syms combSym

theorem pkE_ok (B : BaseOk) (s : State) (hs : pkCE.pre s) :
    ∃ t s', Exec isa publicKeyExpanded s t s' ∧ abiPreserved s s' ∧ pkCE.post s s' := by
  obtain ⟨⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, -⟩, hk⟩ := hs
  simp only [stripConsts_gpr, stripConsts_wr, stripConsts_sp] at *
  obtain ⟨-, tal, tfit, words, twr, tres⟩ := tbl_of_consts hk
  have hrd : s.rd = [⟨s.gpr .a1, 64⟩, TBL (s.syms combSym)] := rd_of_consts hk a
  have tW : ∀ r ∈ pkW s, (TBL (s.syms combSym)).Disjoint r := fun r hr => by
    simp only [pkW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact twr _ (by rw [b]; simp)
    · exact twr _ (by rw [b]; simp)
    · exact twr _ (by rw [b]; simp)
    · exact tres _ (below_reserved s)
  obtain ⟨t, s', he, hg, hsp, hra, hq⟩ := publicKeyExpanded_wp B
    ⟨hrd, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, tal, tfit, words, tW⟩
  exact ⟨t, s', he, ⟨hg, hsp, hra⟩, fun seed _ hs => hq seed hs⟩

/-- The contract by register: `out` in `a0`, `expanded` (the seed's digest, 64 bytes) in `a1`,
`pk` in `a2`, the message in `a3` (`len` in `a4`), `scratch` in `a5`, the frame in `a6`; without the
comb's table. -/
def signRE : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .a0, 64⟩
    let ex : Region := ⟨s.gpr .a1, 64⟩
    let pk : Region := ⟨s.gpr .a2, 32⟩
    let msg : Region := ⟨s.gpr .a3, (s.gpr .a4).toNat⟩
    let sc : Region := ⟨s.gpr .a5, 8192⟩
    let fr : Region := ⟨s.gpr .a6, 288⟩
    s.rd = [ex, pk, msg] ∧ s.wr = [out, sc, fr] ∧ (s.gpr .a5).toNat % 8 = 0 ∧ (s.gpr .a6).toNat % 8 = 0 ∧
      out.Disjoint ex ∧ out.Disjoint pk ∧ out.Disjoint msg ∧ out.Disjoint sc ∧ out.Disjoint fr ∧
      ex.Disjoint sc ∧ ex.Disjoint fr ∧ pk.Disjoint sc ∧ pk.Disjoint fr ∧ msg.Disjoint sc ∧
      msg.Disjoint fr ∧ sc.Disjoint fr ∧ s.sp.toNat % 16 = 0 ∧ 208 ≤ s.sp.toNat ∧
      (below s.sp 208).Disjoint out ∧ (below s.sp 208).Disjoint ex ∧ (below s.sp 208).Disjoint pk ∧
      (below s.sp 208).Disjoint msg ∧ (below s.sp 208).Disjoint sc ∧ (below s.sp 208).Disjoint fr ∧
      ∃ seed : List Byte, seed.length = 32 ∧ bytesAt s.mem (s.gpr .a1) 64 = Spec.Sha512.sha512 seed ∧
        bytesAt s.mem (s.gpr .a2) 32 = Spec.Ed25519.publicKey seed
  post s s' := ∀ seed : List Byte, seed.length = 32 → bytesAt s.mem (s.gpr .a1) 64 = Spec.Sha512.sha512 seed →
    bytesAt s'.mem (s.gpr .a0) 64 = Spec.Ed25519.sign seed (bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat)
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧ s₁.gpr .a6 = s₂.gpr .a6 ∧
    s₁.sp = s₂.sp

/-- `signRE` with the comb's table (`abi.withConsts`). -/
def signCE : Contract isa where
  pre s := signRE.pre (stripConsts combConsts s) ∧ ConstsOk combConsts 208 s
  post := signRE.post
  pub s₁ s₂ := signRE.pub s₁ s₂ ∧ s₁.syms combSym = s₂.syms combSym

theorem signE_ok (B : BaseOk) (s : State) (hs : signCE.pre s) :
    ∃ t s', Exec isa signExpanded s t s' ∧ abiPreserved s s' ∧ signCE.post s s' := by
  obtain ⟨⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, u, v, w, x, y, z, z'⟩, hk⟩ := hs
  simp only [stripConsts_gpr, stripConsts_wr, stripConsts_sp, stripConsts_mem] at *
  obtain ⟨-, tal, tfit, words, twr, tres⟩ := tbl_of_consts hk
  have hrd : s.rd = [⟨s.gpr .a1, 64⟩, ⟨s.gpr .a2, 32⟩, msgR s, TBL (s.syms combSym)] := rd_of_consts hk a
  have tW : ∀ r ∈ signW s, (TBL (s.syms combSym)).Disjoint r := fun r hr => by
    simp only [signW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact twr _ (by rw [b]; simp)
    · exact twr _ (by rw [b]; simp)
    · exact twr _ (by rw [b]; simp)
    · exact tres _ (below_reserved s)
  obtain ⟨s₀, -, h₀, hk₀⟩ := z'
  obtain ⟨t, s', he, hg, hsp, hra, hq⟩ :=
    signExpanded_wp sha512OK B ⟨hrd, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, u, v, w, x, y, z,
      tal, tfit, words, tW⟩ ⟨s₀, h₀, hk₀⟩
  exact ⟨t, s', he, ⟨hg, hsp, hra⟩, fun seed _ hs => hq seed hs⟩

end VG.Proof.Ed25519.RISCV64.Whole
