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
# `vg_ed25519_public_key` and `vg_ed25519_sign_cached` on RISC-V, by register

Each function, with its frame as one more argument, meets a contract of its
facts by register (`pkC`, `signC`), from an aligned `scratch` and frame, and
208 bytes of stack below the stack pointer for the callees' frames
(`pk_ok`, `sign_ok`). Their constant time is `publicKey_ct` and
`signCached_ct`.
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64.Whole

open VG VG.RISCV64 VG.Impl.Ed25519.RISCV64.Whole
open VG.Spec.Ed25519 (bytesAt)
open VG.Impl.Ed25519.RISCV64 (combSym combConsts)

/-- The contract by register: `out` in `a0`, `seed` in `a1`, `scratch` in `a2`, the frame in `a3`;
without the comb's table. -/
def pkR : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .a0, 32⟩
    let seed : Region := ⟨s.gpr .a1, 32⟩
    let sc : Region := ⟨s.gpr .a2, 8192⟩
    let fr : Region := ⟨s.gpr .a3, 144⟩
    s.rd = [seed] ∧ s.wr = [out, sc, fr] ∧ out.Disjoint seed ∧ out.Disjoint sc ∧ out.Disjoint fr ∧
      seed.Disjoint sc ∧ seed.Disjoint fr ∧ sc.Disjoint fr ∧ (s.gpr .a2).toNat % 8 = 0 ∧
      (s.gpr .a3).toNat % 8 = 0 ∧ s.sp.toNat % 16 = 0 ∧ 208 ≤ s.sp.toNat ∧
      (below s.sp 208).Disjoint out ∧ (below s.sp 208).Disjoint seed ∧ (below s.sp 208).Disjoint sc ∧
      (below s.sp 208).Disjoint fr
  post s s' := bytesAt s'.mem (s.gpr .a0) 32 = Spec.Ed25519.publicKey (bytesAt s.mem (s.gpr .a1) 32)
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp

/-- `pkR` with the comb's table (`abi.withConsts`): `pkR` for the state without it, and what the table
adds. -/
def pkC : Contract isa where
  pre s := pkR.pre (stripConsts combConsts s) ∧ ConstsOk combConsts 208 s
  post := pkR.post
  pub s₁ s₂ := pkR.pub s₁ s₂ ∧ s₁.syms combSym = s₂.syms combSym

/-- The stack the contract reserves. -/
theorem below_reserved (s : State) : below s.sp 208 ∈ RISCV64.abi.reserved 208 s := by
  show _ ∈ stackBelow s.sp 208
  rw [stackBelow_pos _ (by decide)]; simp

theorem pk_ok (B : BaseOk) (s : State) (hs : pkC.pre s) :
    ∃ t s', Exec isa publicKey s t s' ∧ abiPreserved s s' ∧ pkC.post s s' := by
  obtain ⟨⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p⟩, hk⟩ := hs
  simp only [stripConsts_gpr, stripConsts_wr, stripConsts_sp] at *
  obtain ⟨-, tal, tfit, words, twr, tres⟩ := tbl_of_consts hk
  have hrd : s.rd = [⟨s.gpr .a1, 32⟩, TBL (s.syms combSym)] := rd_of_consts hk a
  have tW : ∀ r ∈ pkW s, (TBL (s.syms combSym)).Disjoint r := fun r hr => by
    simp only [pkW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact twr _ (by rw [b]; simp)
    · exact twr _ (by rw [b]; simp)
    · exact twr _ (by rw [b]; simp)
    · exact tres _ (below_reserved s)
  obtain ⟨t, s', he, hg, hsp, hra, hq⟩ := publicKey_wp sha512OK B
    ⟨hrd, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, tal, tfit, words, tW⟩
  exact ⟨t, s', he, ⟨hg, hsp, hra⟩, hq⟩

/-- The contract by register: `out` in `a0`, `seed` in `a1`, `pk` in `a2`, the message in `a3`
(`len` in `a4`), `scratch` in `a5`, the frame in `a6`;
without the comb's table. -/
def signR : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .a0, 64⟩
    let seed : Region := ⟨s.gpr .a1, 32⟩
    let pk : Region := ⟨s.gpr .a2, 32⟩
    let msg : Region := ⟨s.gpr .a3, (s.gpr .a4).toNat⟩
    let sc : Region := ⟨s.gpr .a5, 8192⟩
    let fr : Region := ⟨s.gpr .a6, 288⟩
    s.rd = [seed, pk, msg] ∧ s.wr = [out, sc, fr] ∧ (s.gpr .a5).toNat % 8 = 0 ∧ (s.gpr .a6).toNat % 8 = 0 ∧
      out.Disjoint seed ∧ out.Disjoint pk ∧ out.Disjoint msg ∧ out.Disjoint sc ∧ out.Disjoint fr ∧
      seed.Disjoint sc ∧ seed.Disjoint fr ∧ pk.Disjoint sc ∧ pk.Disjoint fr ∧ msg.Disjoint sc ∧
      msg.Disjoint fr ∧ sc.Disjoint fr ∧ s.sp.toNat % 16 = 0 ∧ 208 ≤ s.sp.toNat ∧
      (below s.sp 208).Disjoint out ∧ (below s.sp 208).Disjoint seed ∧ (below s.sp 208).Disjoint pk ∧
      (below s.sp 208).Disjoint msg ∧ (below s.sp 208).Disjoint sc ∧ (below s.sp 208).Disjoint fr ∧
      bytesAt s.mem (s.gpr .a2) 32 = Spec.Ed25519.publicKey (bytesAt s.mem (s.gpr .a1) 32)
  post s s' := bytesAt s'.mem (s.gpr .a0) 64 =
    Spec.Ed25519.sign (bytesAt s.mem (s.gpr .a1) 32) (bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat)
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧ s₁.gpr .a6 = s₂.gpr .a6 ∧
    s₁.sp = s₂.sp

/-- `signR` with the comb's table (`abi.withConsts`). -/
def signC : Contract isa where
  pre s := signR.pre (stripConsts combConsts s) ∧ ConstsOk combConsts 208 s
  post := signR.post
  pub s₁ s₂ := signR.pub s₁ s₂ ∧ s₁.syms combSym = s₂.syms combSym

theorem sign_ok (B : BaseOk) (s : State) (hs : signC.pre s) :
    ∃ t s', Exec isa signCached s t s' ∧ abiPreserved s s' ∧ signC.post s s' := by
  obtain ⟨⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, u, v, w, x, y, z, z'⟩, hk⟩ := hs
  simp only [stripConsts_gpr, stripConsts_wr, stripConsts_sp] at *
  obtain ⟨-, tal, tfit, words, twr, tres⟩ := tbl_of_consts hk
  have hrd : s.rd = [⟨s.gpr .a1, 32⟩, ⟨s.gpr .a2, 32⟩, msgR s, TBL (s.syms combSym)] := rd_of_consts hk a
  have tW : ∀ r ∈ signW s, (TBL (s.syms combSym)).Disjoint r := fun r hr => by
    simp only [signW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact twr _ (by rw [b]; simp)
    · exact twr _ (by rw [b]; simp)
    · exact twr _ (by rw [b]; simp)
    · exact tres _ (below_reserved s)
  obtain ⟨t, s', he, hg, hsp, hra, hq⟩ :=
    signCached_wp sha512OK B ⟨hrd, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, u, v, w, x, y, z, z',
      tal, tfit, words, tW⟩
  exact ⟨t, s', he, ⟨hg, hsp, hra⟩, hq⟩

/-- A contract by register `kR` without the comb's table implies the signature's contract under
`abi`; so does it with the table, under `abi.withConsts combConsts`. -/
theorem consts_implies {kR : Contract isa} {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {wa : Bool} {st : Nat}
    (h : kR.Implies (sig.contract abi pre post wa st))
    (hpost : ∀ s s', kR.post s s' → kR.post (stripConsts combConsts s) s')
    (hpub : ∀ s₁ s₂, kR.pub (stripConsts combConsts s₁) (stripConsts combConsts s₂) → kR.pub s₁ s₂)
    (hsat : ∃ s, (sig.contract (abi.withConsts combConsts) pre post wa st).pre s) :
    Contract.Implies (M := isa)
      { pre := fun s => kR.pre (stripConsts combConsts s) ∧ ConstsOk combConsts st s
        post := kR.post
        pub := fun s₁ s₂ => kR.pub s₁ s₂ ∧ s₁.syms combSym = s₂.syms combSym }
      (sig.contract (abi.withConsts combConsts) pre post wa st) where
  pre _ hs := ⟨h.pre _ (pre_consts.mp hs).1, (pre_consts.mp hs).2⟩
  post s s' hs hp := post_consts.mpr (post_stripConsts.mp (h.post (stripConsts combConsts s) s'
    (pre_consts.mp hs).1 (hpost s s' hp)))
  pub s₁ s₂ h₁ h₂ hp := ⟨hpub _ _ (h.pub (stripConsts combConsts s₁) (stripConsts combConsts s₂)
      (pre_consts.mp h₁).1 (pre_consts.mp h₂).1 (pub_stripConsts.mpr (pub_consts.mp hp).1)),
    (pub_consts.mp hp).2 _ List.mem_cons_self⟩
  sat := hsat

end VG.Proof.Ed25519.RISCV64.Whole
