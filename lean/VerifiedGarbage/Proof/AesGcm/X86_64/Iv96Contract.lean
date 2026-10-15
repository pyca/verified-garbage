module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.Iv96
public import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Iv96
public import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Contract
public import VerifiedGarbage.Spec.Gcm.PreparedIv96
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# AES-GCM on whole blocks given the block index, x86-64: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. `vg_aes_gcm_decrypt_blocks_prepared_iv96`
and `vg_aes_gcm_encrypt_blocks_to_prepared_iv96` take one more stack argument
than the functions without the index, `index` (at `rsp + 16` and `rsp + 32`):
their preconditions (`blocksPreMI`, `blocksToPreMI`) are the others' with the
stack arguments one longer and `index` the low word of the counter block,
and give `BP` or `BT` (the proofs of the functions without the index) and
`IdxArg` (`BP.ofMI`, `BT.ofMI`).
-/

@[expose] public section

namespace VG.Proof.AesGcm

open VG VG.X86_64
open VG.Spec.Gcm (Block blockAt blocksAt ctrIndex)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)

/-- A 32-bit word from its bytes. -/
theorem readW32_of_bytes {m : Mem} {a : Addr} {V : BitVec 32}
    (h : ∀ i < 4, m (a + BitVec.ofNat 64 i) = V.extractLsb' (8 * i) 8) : m.readW a 32 = V := by
  have e := Mem.read_eq_of_bytes (n := 4) (v := V) h
  show (m.read a 4).setWidth 32 = V
  rw [e]; exact BitVec.setWidth_eq V

/-- The low half of a 64-bit word. -/
theorem readW_lo32 (m : Mem) (a : Addr) : m.readW a 32 = (m.readW a 64).setWidth 32 := by
  apply readW32_of_bytes; intro i hi
  rw [BitVec.extractLsb'_setWidth_of_le (by omega)]
  show _ = ((m.read a 8).setWidth 64).extractLsb' (8 * i) 8
  rw [BitVec.extractLsb'_setWidth_of_le (by omega), Mem.extractLsb'_read m a (by omega : i < 8)]

/-- `blocksPreM`, with `index` after `scratch` on the stack, the low word of
the counter block, and each of the two words readable on its own (a caller
may push them separately). -/
def blocksPreMI (M : CtxMode) (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .rdi, M.len⟩
  let ctr : Region := ⟨s.gpr .rdx, 16⟩
  let y : Region := ⟨s.gpr .rcx, 16⟩
  let data : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat * 16⟩
  let scr : Region := ⟨arg s 0, 2112⟩
  ctx ∈ s.rd ∧ InRegions s.rd (s.gpr .rsp + BitVec.ofNat 64 8) 8 ∧
    InRegions s.rd (s.gpr .rsp + BitVec.ofNat 64 16) 8 ∧ s.wr = [ctr, y, data, scr] ∧
    ctx.Disjoint ctr ∧ ctx.Disjoint y ∧ ctx.Disjoint data ∧ ctx.Disjoint scr ∧
    ctr.Disjoint y ∧ ctr.Disjoint data ∧ ctr.Disjoint scr ∧ ctr.Disjoint (args s 2) ∧
    y.Disjoint data ∧ y.Disjoint scr ∧ y.Disjoint (args s 2) ∧
    data.Disjoint scr ∧ data.Disjoint (args s 2) ∧ scr.Disjoint (args s 2) ∧
    (ret s).Disjoint ctr ∧ (ret s).Disjoint y ∧ (ret s).Disjoint data ∧ (ret s).Disjoint scr ∧
    (stk s).Disjoint ctx ∧ (stk s).Disjoint ctr ∧ (stk s).Disjoint y ∧ (stk s).Disjoint data ∧
    (stk s).Disjoint scr ∧
    (s.gpr .rdi).toNat + M.len ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 16 ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + 16 ≤ 2 ^ 64 ∧
    (s.gpr .r8).toNat + (s.gpr .r9).toNat * 16 ≤ 2 ^ 64 ∧ (arg s 0).toNat + 2112 ≤ 2 ^ 64 ∧
    (s.gpr .rsp).toNat + 24 ≤ 2 ^ 64 ∧ rounds s ∧ M.ok s.mem (s.gpr .rdi) ∧
    ctrIndex (blockAt s.mem (s.gpr .rdx)) = (arg s 1).setWidth 32

/-- Each word of the two stack arguments is in their region. -/
theorem inRegions_args2 (sp : Addr) (ctx : Region) {d : Nat} (hd : d = 8 ∨ d = 16) :
    InRegions [ctx, ⟨sp + BitVec.ofNat 64 8, 16⟩] (sp + BitVec.ofNat 64 d) 8 :=
  ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _),
    Offset.contains (e := 8) (k := 16) _ (by omega) (by omega) (by decide)⟩

/-- The index, the last word of the four stack arguments, is in their region. -/
theorem inRegions_args4 (sp : Addr) (ctx src : Region) :
    InRegions [ctx, src, ⟨sp + BitVec.ofNat 64 8, 32⟩] (sp + BitVec.ofNat 64 32) 8 :=
  ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)),
    Offset.contains (e := 8) (k := 32) _ (by decide) (by decide) (by decide)⟩

/-- The first three of the four stack arguments are in their region. -/
theorem covers_args4 (sp : Addr) (ctx src : Region) :
    Covers [⟨sp + BitVec.ofNat 64 8, 24⟩] [ctx, src, ⟨sp + BitVec.ofNat 64 8, 32⟩] := fun a n ⟨r, hr, hc⟩ => by
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)),
    by simp only [Region.Contains] at hc ⊢; omega⟩

/-- `blocksPub`, and `index`. -/
def blocksPubI (s₁ s₂ : State) : Prop :=
  blocksPub s₁ s₂ ∧ (arg s₁ 1).setWidth 32 = (arg s₂ 1).setWidth 32

/-- `vg_aes_gcm_decrypt_blocks_prepared_iv96`, for a key context of kind `M`. -/
def decryptBlocksIv96X86_64M (M : CtxMode) : Contract isa where
  pre := blocksPreMI M
  post := decryptBlocksX86_64.post
  pub := blocksPubI

/-- `blocksToPreM`, with `index` after `scratch` on the stack, the low word
of the counter block, readable apart from the other three (a caller may push
it separately). -/
def blocksToPreMI (M : CtxMode) (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .rdi, M.len⟩
  let ctr : Region := ⟨s.gpr .rdx, 16⟩
  let y : Region := ⟨s.gpr .rcx, 16⟩
  let src : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat * 16⟩
  let dst : Region := ⟨arg s 0, (arg s 1).toNat * 16⟩
  let scr : Region := ⟨arg s 2, 2112⟩
  ctx ∈ s.rd ∧ src ∈ s.rd ∧ Covers [⟨s.gpr .rsp + BitVec.ofNat 64 8, 24⟩] s.rd ∧
    InRegions s.rd (s.gpr .rsp + BitVec.ofNat 64 32) 8 ∧ s.wr = [ctr, y, dst, scr] ∧ arg s 1 = s.gpr .r9 ∧
    ctx.Disjoint ctr ∧ ctx.Disjoint y ∧ ctx.Disjoint dst ∧ ctx.Disjoint scr ∧
    ctr.Disjoint y ∧ ctr.Disjoint src ∧ ctr.Disjoint dst ∧ ctr.Disjoint scr ∧ ctr.Disjoint (args s 4) ∧
    y.Disjoint src ∧ y.Disjoint dst ∧ y.Disjoint scr ∧ y.Disjoint (args s 4) ∧
    src.Disjoint dst ∧ src.Disjoint scr ∧
    dst.Disjoint scr ∧ dst.Disjoint (args s 4) ∧ scr.Disjoint (args s 4) ∧
    (ret s).Disjoint ctr ∧ (ret s).Disjoint y ∧ (ret s).Disjoint dst ∧ (ret s).Disjoint scr ∧
    (stk24 s).Disjoint ctx ∧ (stk24 s).Disjoint ctr ∧ (stk24 s).Disjoint y ∧ (stk24 s).Disjoint src ∧
    (stk24 s).Disjoint dst ∧ (stk24 s).Disjoint scr ∧
    (s.gpr .rdi).toNat + M.len ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 16 ≤ 2 ^ 64 ∧
    (s.gpr .rcx).toNat + 16 ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + (s.gpr .r9).toNat * 16 ≤ 2 ^ 64 ∧
    (arg s 0).toNat + (arg s 1).toNat * 16 ≤ 2 ^ 64 ∧ (arg s 2).toNat + 2112 ≤ 2 ^ 64 ∧
    24 ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 40 ≤ 2 ^ 64 ∧ rounds s ∧ M.ok s.mem (s.gpr .rdi) ∧
    ctrIndex (blockAt s.mem (s.gpr .rdx)) = (arg s 3).setWidth 32

/-- `blocksToPub`, and `index`. -/
def blocksToPubI (s₁ s₂ : State) : Prop :=
  blocksToPub s₁ s₂ ∧ (arg s₁ 3).setWidth 32 = (arg s₂ 3).setWidth 32

/-- `vg_aes_gcm_encrypt_blocks_to_prepared_iv96`, for a key context of kind `M`. -/
def encryptBlocksToIv96X86_64M (M : CtxMode) : Contract isa where
  pre := blocksToPreMI M
  post := blocksToPost
  pub := blocksToPubI

theorem stackArgAddr_eq (s : State) (i : Nat) : stackArgAddr s i = s.gpr .rsp + BitVec.ofNat 64 (8 * (i + 1)) := by
  simp [stackArgAddr]

/-- The index argument, as `IdxArg` reads it. -/
theorem idx_readW (s : State) (i : Nat) :
    s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 (8 * (i + 1))) 32 = (arg s i).setWidth 32 := by
  rw [readW_lo32, arg, stackArg, stackArgAddr_eq]

end VG.Proof.AesGcm

namespace VG.Proof.AesGcm.X86_64.Blocks

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm (arg args ret stk rounds stackArgAddr_eq idx_readW)

theorem BP.ofMI {M : CtxMode} {s : State} (h : Proof.AesGcm.blocksPreMI M s) : BP M s ∧ IdxArg 16 s := by
  obtain ⟨k₁, r₁, r₂, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃, a₁₄, a₁₅, a₁₆, a₁₇, a₁₈, a₁₉, a₂₀, a₂₁,
    a₂₂, a₂₃, a₂₄, a₂₅, a₂₆, a₂₇, a₂₈, a₂₉, a₃₀, a₃₁, a₃₂, a₃₃, a₃₄⟩ := h
  have hA : Proof.AesGcm.args s 2 = ⟨SP s + BitVec.ofNat 64 8, 16⟩ := by simp only [Proof.AesGcm.args, stackArgAddr_eq]
  rw [hA] at a₁₀ a₁₃ a₁₅ a₁₆
  have hs : Region.Sub (aR s) ⟨SP s + BitVec.ofNat 64 8, 16⟩ := Offset.sub (e := 8) (k := 16) _ (by decide) (by decide)
  have hi : Region.Sub ⟨SP s + BitVec.ofNat 64 16, 4⟩ ⟨SP s + BitVec.ofNat 64 8, 16⟩ :=
    Offset.sub (e := 8) (k := 16) _ (by decide) (by decide)
  have r₂' : InRegions s.rd (SP s + BitVec.ofNat 64 16) 4 := by
    obtain ⟨r, hr, hc⟩ := r₂; exact ⟨r, hr, by simp only [Region.Contains, SP] at hc ⊢; omega⟩
  refine ⟨⟨k₁, r₁, a₂,
    a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀.sub_right hs, a₁₁, a₁₂, a₁₃.sub_right hs, a₁₄, a₁₅.sub_right hs,
    a₁₆.sub_right hs, a₁₇, a₁₈, a₁₉, a₂₀, a₂₁, a₂₂, a₂₃, a₂₄, a₂₅, a₂₆, a₂₇, a₂₈, a₂₉, a₃₀, by simp only [SP]; omega, a₃₂, a₃₃⟩,
    ⟨?_, r₂', (a₁₅.symm.sub_left hi), (a₁₆.symm.sub_left hi)⟩⟩
  rw [show (16 : Nat) = 8 * (1 + 1) from rfl, idx_readW]; exact a₃₄.symm

end VG.Proof.AesGcm.X86_64.Blocks

namespace VG.Proof.AesGcm.X86_64.BlocksTo

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm (arg args ret stk24 rounds stackArgAddr_eq idx_readW)

theorem BT.ofMI {M : CtxMode} {s : State} (h : Proof.AesGcm.blocksToPreMI M s) : BT M s ∧ IdxArg 32 s := by
  obtain ⟨k₁, r₁, c₁, i₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃, a₁₄, a₁₅, a₁₆, a₁₇, a₁₈, a₁₉,
    a₂₀, a₂₁, a₂₂, a₂₃, a₂₄, a₂₅, a₂₆, a₂₇, a₂₈, a₂₉, a₃₀, a₃₁, a₃₂, a₃₃, a₃₄, a₃₅, a₃₆, a₃₇, a₃₈, a₃₉, a₄₀,
    a₄₁, a₄₂⟩ := h
  have hA : Proof.AesGcm.args s 4 = ⟨SP s + BitVec.ofNat 64 8, 32⟩ := by simp only [Proof.AesGcm.args, stackArgAddr_eq]
  rw [hA] at a₁₂ a₁₆ a₂₀ a₂₁
  rw [a₃] at a₂ a₆ a₁₀ a₁₄ a₁₇ a₁₉ a₂₀ a₂₄ a₃₀ a₃₆
  have hs : Region.Sub (aR s) ⟨SP s + BitVec.ofNat 64 8, 32⟩ := Offset.sub (e := 8) (k := 32) _ (by decide) (by decide)
  have hi : Region.Sub ⟨SP s + BitVec.ofNat 64 32, 4⟩ ⟨SP s + BitVec.ofNat 64 8, 32⟩ :=
    Offset.sub (e := 8) (k := 32) _ (by decide) (by decide)
  have i₁' : InRegions s.rd (SP s + BitVec.ofNat 64 32) 4 := by
    obtain ⟨r, hr, hc⟩ := i₁; exact ⟨r, hr, by simp only [Region.Contains, SP] at hc ⊢; omega⟩
  refine ⟨⟨k₁, r₁, c₁, a₂, a₃,
    a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂.sub_right hs, a₁₃, a₁₄, a₁₅, a₁₆.sub_right hs, a₁₇, a₁₈, a₁₉,
    a₂₀.sub_right hs, a₂₁.sub_right hs, a₂₂, a₂₃, a₂₄, a₂₅, a₂₆, a₂₇, a₂₈, a₂₉, a₃₀, a₃₁, a₃₂, a₃₃, a₃₄, a₃₅,
    a₃₆, a₃₇, a₃₈, by simp only [SP]; omega, a₄₀, a₄₁⟩,
    ⟨?_, i₁', (a₂₀.symm.sub_left hi), (a₂₁.symm.sub_left hi)⟩⟩
  rw [show (32 : Nat) = 8 * (3 + 1) from rfl, idx_readW]; exact a₄₂.symm

end VG.Proof.AesGcm.X86_64.BlocksTo
