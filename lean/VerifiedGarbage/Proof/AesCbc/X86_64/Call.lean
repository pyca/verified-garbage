import VerifiedGarbage.Proof.AesCbc.Spec
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.Spill
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Aes.X86_64.BlocksVariant
import VerifiedGarbage.Impl.AesCbc.X86_64

/-!
# AES-CBC on x86-64: the contracts, and a call of a block function

The artifacts' contracts are the shared ones of `Spec/Cbc/Contract.lean`,
which imply these (`Verified.lean`): `cbcX86_64 enc`, for encryption
(`enc = true`) and decryption. Each function calls a block function, whose
return address is in the 8 bytes below the stack pointer, which may not
overlap any buffer.

`blk_call`: a call of any implementation of `vg_aes_encrypt_blocks` or
`vg_aes_decrypt_blocks` (`f` being `Spec.Aes.cipher` or
`Spec.Aes.invCipher`) on one block `D` in place, with working space `S`,
from its contract (with `WP.call`): `D` then holds `f` of it, and only `D`,
`S` and the return address change. `blk_rel`: such calls, with the same
arguments in both runs, are constant time.
-/

namespace VG.Proof.AesCbc.X86_64

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)

/-- `vg_aes_cbc_encrypt` (`enc`) or `vg_aes_cbc_decrypt`
`(schedule = rdi, rounds = rsi, iv = rdx, data = rcx, n = r8, scratch = r9)`. -/
def cbcX86_64 (enc : Bool) : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .rdi, 240⟩
    let iv : Region := ⟨s.gpr .rdx, 16⟩
    let data : Region := ⟨s.gpr .rcx, 16 * (s.gpr .r8).toNat⟩
    let scr : Region := ⟨s.gpr .r9, 2176⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack := below (s.gpr .rsp) 8
    s.rd = [sched] ∧ s.wr = [iv, data, scr] ∧
      sched.Disjoint iv ∧ sched.Disjoint data ∧ sched.Disjoint scr ∧ iv.Disjoint data ∧
      iv.Disjoint scr ∧ data.Disjoint scr ∧ ret.Disjoint iv ∧ ret.Disjoint data ∧ ret.Disjoint scr ∧
      stack.Disjoint sched ∧ stack.Disjoint iv ∧ stack.Disjoint data ∧ stack.Disjoint scr ∧
      (s.gpr .rdx).toNat + 16 ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + 16 * (s.gpr .r8).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r9).toNat + 2176 ≤ 2 ^ 64 ∧
      ((s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14)
  post s s' :=
    let ciph := ciphOf enc (s.gpr .rsi).toNat (bytesAt s.mem (s.gpr .rdi) (16 * ((s.gpr .rsi).toNat + 1)))
    let iv := bytesAt s.mem (s.gpr .rdx) 16
    let xs := Spec.Cbc.blocksAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat
    let ys := cbc enc ciph iv xs
    Spec.Cbc.blocksAt s'.mem (s.gpr .rcx) (s.gpr .r8).toNat = ys ∧
      bytesAt s'.mem (s.gpr .rdx) 16 = Spec.Cbc.next iv (cts enc xs ys)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
      s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
      s₁.gpr .rsp = s₂.gpr .rsp

/-! ## A call of a block function -/

/-- Bytes outside a frame are unchanged. -/
theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n :=
  Proof.Cmac.bytesAt_frame hf hd hn

/-- The return address a call stores. -/
theorem callEntry_frame (s : State) : Frame [below (s.gpr .rsp) 8] s.mem s.callEntry.mem := by
  rw [State.callEntry_mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))

theorem toNat_rounds {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) : (BitVec.ofNat 64 R).toNat = R := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)

theorem one_toNat : (1 : BitVec 64).toNat = 1 := rfl

/-- What a call of a block function on one block needs. -/
structure CallPre (s : State) (W D S : Addr) (R : Nat) : Prop where
  rdi : s.gpr .rdi = W
  rsi : s.gpr .rsi = BitVec.ofNat 64 R
  rdx : s.gpr .rdx = D
  rcx : s.gpr .rcx = 1
  r8 : s.gpr .r8 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  wd : (⟨W, 240⟩ : Region).Disjoint ⟨D, 16⟩
  ws : (⟨W, 240⟩ : Region).Disjoint ⟨S, 2048⟩
  ds : (⟨D, 16⟩ : Region).Disjoint ⟨S, 2048⟩
  stkW : (below (s.gpr .rsp) 8).Disjoint ⟨W, 240⟩
  stkD : (below (s.gpr .rsp) 8).Disjoint ⟨D, 16⟩
  stkS : (below (s.gpr .rsp) 8).Disjoint ⟨S, 2048⟩
  wrap : D.toNat + 16 ≤ 2 ^ 64
  reads : Covers ([⟨W, 240⟩] ++ [⟨D, 16⟩, ⟨S, 2048⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨D, 16⟩, ⟨S, 2048⟩] s.wr

/-- What a call of a block function on one block leaves. -/
structure CallPost (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) (s : State) (W D S : Addr)
    (R : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨D, 16⟩, ⟨S, 2048⟩, below (s.gpr .rsp) 8] s.mem s'.mem
  out : bytesAt s'.mem D 16 = (f R (bytesAt s.mem W (16 * (R + 1))) (Spec.Aes.stateAt s.mem D)).toList

/-- The block function's precondition, on entry to a call with the regions it is given. -/
theorem CallPre.blk_pre {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {s : State} {W D S : Addr}
    {R : Nat} (h : CallPre s W D S R) :
    (Proof.Aes.blocksX86_64 f).pre (s.callEntry.withRegions [⟨W, 240⟩] [⟨D, 16⟩, ⟨S, 2048⟩]) := by
  have hR := toNat_rounds h.rounds
  simp only [Proof.Aes.blocksX86_64, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.callEntry_rsp, State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp),
    h.rdi, h.rsi, h.rdx, h.rcx, h.r8, hR, one_toNat, Nat.mul_one]
  exact ⟨trivial, trivial, h.wd, h.ws, h.ds, h.stkD, h.stkS, h.wrap, h.rounds⟩

theorem blk_call {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {b : Impl.Aes.X86_64.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksX86_64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86_64 f).post s s')
    (nosp : NoSp b.code) (depth : b.code.depth = 0)
    {s : State} {W D S : Addr} {R : Nat} (h : CallPre s W D S R) :
    WP isa (.call b.name b.code) s (CallPost f s W D S R) := by
  have hR := toNat_rounds h.rounds
  refine WP.call (k := Proof.Aes.blocksX86_64 f) ok nosp (by rw [depth]; decide)
    (rd := [⟨W, 240⟩]) (wr := [⟨D, 16⟩, ⟨S, 2048⟩]) h.blk_pre h.reads h.writes ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  rw [depth] at hf
  refine ⟨hrd, hwr, hcs, by simpa using hf, ?_⟩
  simp only [Proof.Aes.blocksX86_64, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp),
    h.rdi, h.rsi, h.rdx, h.rcx, hR, one_toNat] at hpost
  have fE := callEntry_frame s
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with rfl | rfl | rfl <;> decide
  have eW := bytesAt_frame fE (p := W) (n := 16 * (R + 1))
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.stkW.sub_right (Region.sub_prefix hRb)).symm)
    (by omega)
  have eD := bytesAt_frame fE (p := D) (n := 16)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.stkD.symm) (by decide)
  rw [← hm₂, bytesAt_of_statesAt hpost, eW, ← ofFn_bytesAt, eD, ofFn_bytesAt]

/-- Calls of a block function on one block, with the same arguments in both
runs, are constant time. -/
theorem blk_rel {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {b : Impl.Aes.X86_64.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksX86_64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86_64 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksX86_64 f).pre (Proof.Aes.blocksX86_64 f).pub b.code)
    {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ W D S : Addr, ∃ R : Nat,
      CallPre s₁ W D S R ∧ CallPre s₂ W D S R ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (.call b.name b.code) fun _ _ => True := by
  refine RelCT.callEx ok ct fun s₁ s₂ hp => ?_
  obtain ⟨W, D, S, R, h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨_, _, _, _, h₁.blk_pre, h₂.blk_pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes, hsp⟩
  simp only [Proof.Aes.blocksX86_64, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp),
    h₁.rdi, h₁.rsi, h₁.rdx, h₁.rcx, h₁.r8, h₂.rdi, h₂.rsi, h₂.rdx, h₂.rcx, h₂.r8, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

end VG.Proof.AesCbc.X86_64
