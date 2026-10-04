import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.Spill
import VerifiedGarbage.Impl.CmacAes.X86_64
import VerifiedGarbage.Proof.Aes.X86_64.Variant
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.X86_64.RelCT

section

section

section

/-!
# AES-CMAC on x86-64: calling `vg_aes_ctr32` on one block

`ctr_call`: a call of any implementation of `vg_aes_ctr32` with the counter
block `C`, one data block `D` holding zeros, and working space `S`, from its
contract (with `WP.call`): `D` then holds `CIPH_K(C)`, as bytes
(`Cmac.aesWith`), and only `C`, `D`, `S` and the return address change.
-/

namespace VG.Proof.CmacAes.X86_64

open VG VG.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- Bytes outside a frame are unchanged. -/
theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) :
    Spec.Aes.bytesAt m' p n = Spec.Aes.bytesAt m p n := by
  simp only [Spec.Aes.bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

/-- The return address a call stores. -/
theorem callEntry_frame (s : State) : Frame [below (s.gpr .rsp) 8] s.mem s.callEntry.mem := by
  rw [State.callEntry_mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))

theorem ofBytes_zeros : Spec.Gcm.ofBytes (Spec.Cmac.zeros 16) = 0 := by decide

theorem toNat_rounds {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) : (BitVec.ofNat 64 R).toNat = R := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)

theorem one_toNat : (1 : BitVec 64).toNat = 1 := rfl

/-- What a call of `vg_aes_ctr32` on one block needs. -/
structure CallPre (s : State) (W C D S : Addr) (R : Nat) : Prop where
  rdi : s.gpr .rdi = W
  rsi : s.gpr .rsi = BitVec.ofNat 64 R
  rdx : s.gpr .rdx = C
  rcx : s.gpr .rcx = D
  r8 : s.gpr .r8 = 1
  r9 : s.gpr .r9 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  wc : (⟨W, 240⟩ : Region).Disjoint ⟨C, 16⟩
  wd : (⟨W, 240⟩ : Region).Disjoint ⟨D, 16⟩
  ws : (⟨W, 240⟩ : Region).Disjoint ⟨S, 2048⟩
  cd : (⟨C, 16⟩ : Region).Disjoint ⟨D, 16⟩
  cs : (⟨C, 16⟩ : Region).Disjoint ⟨S, 2048⟩
  ds : (⟨D, 16⟩ : Region).Disjoint ⟨S, 2048⟩
  stkW : (below (s.gpr .rsp) 8).Disjoint ⟨W, 240⟩
  stkC : (below (s.gpr .rsp) 8).Disjoint ⟨C, 16⟩
  stkD : (below (s.gpr .rsp) 8).Disjoint ⟨D, 16⟩
  stkS : (below (s.gpr .rsp) 8).Disjoint ⟨S, 2048⟩
  wrap : D.toNat + 16 ≤ 2 ^ 64
  reads : Covers ([⟨W, 240⟩] ++ [⟨C, 16⟩, ⟨D, 16⟩, ⟨S, 2048⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨C, 16⟩, ⟨D, 16⟩, ⟨S, 2048⟩] s.wr
  zero : Spec.Aes.bytesAt s.mem D 16 = Spec.Cmac.zeros 16

/-- What a call of `vg_aes_ctr32` on one block leaves. -/
structure CallPost (s : State) (W C D S : Addr) (R : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨C, 16⟩, ⟨D, 16⟩, ⟨S, 2048⟩, below (s.gpr .rsp) 8] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem D 16 =
    Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem W (16 * (R + 1))) (Spec.Aes.bytesAt s.mem C 16)

/-- `vg_aes_ctr32`'s precondition, on entry to a call with the regions it is given. -/
theorem CallPre.ctr_pre {s : State} {W C D S : Addr} {R : Nat} (h : CallPre s W C D S R) :
    Proof.Aes.ctr32X86_64.pre
      (s.callEntry.withRegions [⟨W, 240⟩] [⟨C, 16⟩, ⟨D, 16⟩, ⟨S, 2048⟩]) := by
  have hR := toNat_rounds h.rounds
  simp only [Proof.Aes.ctr32X86_64, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.callEntry_rsp, State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.r9 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, hR,
    one_toNat, Nat.mul_one]
  exact ⟨trivial, trivial, h.wc, by simpa using h.wd, h.ws, by simpa using h.cd, h.cs,
    by simpa using h.ds, h.stkC, by simpa using h.stkD, h.stkS, by simpa using h.wrap, h.rounds⟩

theorem ctr_call (v : Ctr32Impl) {s : State} {W C D S : Addr} {R : Nat} (h : CallPre s W C D S R) :
    WP isa (.call v.callee.name v.callee.code) s (CallPost s W C D S R) := by
  have hR := toNat_rounds h.rounds
  refine WP.call (k := Proof.Aes.ctr32X86_64) v.ok v.nosp (by rw [v.depth]; decide)
    (rd := [⟨W, 240⟩]) (wr := [⟨C, 16⟩, ⟨D, 16⟩, ⟨S, 2048⟩]) h.ctr_pre h.reads h.writes ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  rw [v.depth] at hf
  refine ⟨hrd, hwr, hcs, ?_, ?_⟩
  · simpa using hf
  · obtain ⟨hdata, -⟩ := hpost
    simp only [State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp),
      State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp),
      State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, h.r8, hR,
      one_toNat] at hdata
    have fE := callEntry_frame s
    have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with rfl | rfl | rfl <;> decide
    have eW := bytesAt_frame fE (p := W) (n := 16 * (R + 1))
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (h.stkW.sub_right (Region.sub_prefix hRb)).symm)
      (by omega)
    have eC := bytesAt_frame fE (p := C) (n := 16)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.stkC.symm) (by decide)
    have eD := bytesAt_frame fE (p := D) (n := 16)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.stkD.symm) (by decide)
    have one : ∀ m : Mem, Spec.Gcm.blocksAt m D 1 = [Spec.Gcm.blockAt m D] := fun m => by
      simp [Spec.Gcm.blocksAt]
    have bD : Spec.Gcm.blockAt s.callEntry.mem D = 0 := by
      rw [Spec.Gcm.blockAt, eD, h.zero, ofBytes_zeros]
    have bC : Spec.Gcm.blockAt s.callEntry.mem C = Spec.Gcm.ofBytes (Spec.Aes.bytesAt s.mem C 16) := by
      rw [Spec.Gcm.blockAt, eC]
    rw [one, one, bD, bC, eW, Proof.Cmac.ctr32_one, List.cons.injEq] at hdata
    rw [← hm₂, Proof.Cmac.bytesAt_blockAt, hdata.1,
      Proof.Cmac.aesWith_bytes _ _ (Proof.Cmac.bytesAt_length _ _ _)]

/-- Calls of `vg_aes_ctr32` on one block, with the same arguments in both
runs, are constant time. -/
theorem ctr_rel (v : Ctr32Impl) {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ W C D S : Addr, ∃ R : Nat,
      CallPre s₁ W C D S R ∧ CallPre s₂ W C D S R ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (.call v.callee.name v.callee.code) fun _ _ => True := by
  refine RelCT.callEx v.ok v.ct fun s₁ s₂ hp => ?_
  obtain ⟨W, C, D, S, R, h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨_, _, _, _, h₁.ctr_pre, h₂.ctr_pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes, hsp⟩
  simp only [Proof.Aes.ctr32X86_64, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.r9 ≠ .rsp),
    h₁.rdi, h₁.rsi, h₁.rdx, h₁.rcx, h₁.r8, h₁.r9, h₂.rdi, h₂.rsi, h₂.rdx, h₂.rcx, h₂.r8, h₂.r9, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

end VG.Proof.CmacAes.X86_64

end

/-!
# AES-CMAC on x86-64: the contracts the proofs are written against

The artifacts' contracts are the shared ones of `Spec/Cmac/Contract.lean`,
which imply these (`Verified.lean`). Each function calls `vg_aes_ctr32`, whose
return address is in the 8 bytes below the stack pointer, which may not
overlap any buffer.
-/

namespace VG.Proof.CmacAes.X86_64

open VG VG.X86_64

/-- `CIPH_K` for AES with the key schedule at `w` for `R` rounds, in `m`. -/
abbrev ciphAt (m : Mem) (w : Addr) (R : Nat) : Spec.Cmac.Cipher :=
  Spec.Cmac.aesWith R (Spec.Aes.bytesAt m w (16 * (R + 1)))

/-- `vg_cmac_aes_update(schedule = rdi, rounds = rsi, state = rdx, data = rcx, n = r8, scratch = r9)`. -/
def updateX86_64 : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .rdi, 240⟩
    let state : Region := ⟨s.gpr .rdx, 16⟩
    let data : Region := ⟨s.gpr .rcx, 16 * (s.gpr .r8).toNat⟩
    let scr : Region := ⟨s.gpr .r9, 2176⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack := below (s.gpr .rsp) 8
    s.rd = [sched, data] ∧ s.wr = [state, scr] ∧
      sched.Disjoint state ∧ sched.Disjoint scr ∧ data.Disjoint state ∧ data.Disjoint scr ∧
      state.Disjoint scr ∧ ret.Disjoint state ∧ ret.Disjoint scr ∧
      stack.Disjoint sched ∧ stack.Disjoint data ∧ stack.Disjoint state ∧ stack.Disjoint scr ∧
      (s.gpr .rdx).toNat + 16 ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + 16 * (s.gpr .r8).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r9).toNat + 2176 ≤ 2 ^ 64 ∧
      ((s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14)
  post s s' :=
    Spec.Aes.bytesAt s'.mem (s.gpr .rdx) 16 =
      Spec.Cmac.chain (ciphAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (Spec.Aes.bytesAt s.mem (s.gpr .rdx) 16)
        (Spec.Cmac.blocksAt s.mem (s.gpr .rcx) 16 (s.gpr .r8).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
      s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
      s₁.gpr .rsp = s₂.gpr .rsp

/-- `vg_cmac_aes_subkeys(schedule = rdi, rounds = rsi, subkeys = rdx, scratch = rcx)`. -/
def subkeysX86_64 : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .rdi, 240⟩
    let subk : Region := ⟨s.gpr .rdx, 32⟩
    let scr : Region := ⟨s.gpr .rcx, 2176⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack := below (s.gpr .rsp) 8
    s.rd = [sched] ∧ s.wr = [subk, scr] ∧
      sched.Disjoint subk ∧ sched.Disjoint scr ∧ subk.Disjoint scr ∧
      ret.Disjoint subk ∧ ret.Disjoint scr ∧
      stack.Disjoint sched ∧ stack.Disjoint subk ∧ stack.Disjoint scr ∧
      (s.gpr .rdx).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + 2176 ≤ 2 ^ 64 ∧
      ((s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14)
  post s s' :=
    let ks := Spec.Cmac.subkeys (ciphAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) 16
    Spec.Aes.bytesAt s'.mem (s.gpr .rdx) 32 = ks.1 ++ ks.2
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
      s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- `vg_cmac_aes_finalize(key = rdi, rounds = rsi, state = rdx, last = rcx, last_len = r8, scratch = r9)`. -/
def finalizeX86_64 : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, 272⟩
    let state : Region := ⟨s.gpr .rdx, 16⟩
    let last : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
    let scr : Region := ⟨s.gpr .r9, 2176⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack := below (s.gpr .rsp) 8
    s.rd = [key, last] ∧ s.wr = [state, scr] ∧
      key.Disjoint state ∧ key.Disjoint scr ∧ last.Disjoint state ∧ last.Disjoint scr ∧
      state.Disjoint scr ∧ ret.Disjoint state ∧ ret.Disjoint scr ∧
      stack.Disjoint key ∧ stack.Disjoint last ∧ stack.Disjoint state ∧ stack.Disjoint scr ∧
      (s.gpr .rdi).toNat + 272 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 16 ≤ 2 ^ 64 ∧
      (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧ (s.gpr .r9).toNat + 2176 ≤ 2 ^ 64 ∧
      ((s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14) ∧
      (s.gpr .r8).toNat ≤ 16
  post s s' :=
    let ciph := ciphAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat
    let ks := Spec.Cmac.subkeys ciph 16
    Spec.Aes.bytesAt s.mem (s.gpr .rdi + 240) 32 = ks.1 ++ ks.2 →
    ∀ msg : List Byte, msg.length % 16 = 0 → (msg = [] ∨ 0 < (s.gpr .r8).toNat) →
      Spec.Aes.bytesAt s.mem (s.gpr .rdx) 16 = Spec.Cmac.chain ciph (Spec.Cmac.zeros 16) (Spec.Cmac.blocks 16 msg) →
      Spec.Aes.bytesAt s'.mem (s.gpr .rdx) 16 =
        Spec.Cmac.macFull ciph 16 (msg ++ Spec.Aes.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
      s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
      s₁.gpr .rsp = s₂.gpr .rsp

end VG.Proof.CmacAes.X86_64

end

/-!
# AES-CMAC on x86-64: `vg_cmac_aes_update`
-/

namespace VG.Proof.CmacAes.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.CmacAes.X86_64

theorem offset_nat (i : Nat) : BitVec.ofInt 64 (i : Int) = BitVec.ofNat 64 i := rfl

/-- The memory after saving the registers. -/
abbrev savedMem (s : State) : Mem := Spill.saveMem s.mem (s.gpr .r9) s.gpr saved

theorem saved_bound : ∀ p ∈ saved, 2064 ≤ p.2 ∧ p.2 + 8 ≤ 2112 := by decide

theorem prologue_ok (s : State)
    (hw : ∀ d, 2064 ≤ d → d + 8 ≤ 2112 → InRegions s.wr (s.gpr .r9 + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa (save ++ setup) s = some s' ∧
      s'.gpr .rbx = s.gpr .rdi ∧ s'.gpr .rbp = s.gpr .rsi ∧ s'.gpr .r12 = s.gpr .rdx ∧
      s'.gpr .r13 = s.gpr .rcx ∧ s'.gpr .r14 = s.gpr .r8 ∧ s'.gpr .r15 = s.gpr .r9 ∧
      s'.gpr .rsp = s.gpr .rsp ∧ s'.zf = some (s.gpr .r8 == 0) ∧
      s'.mem = savedMem s ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [save, setup, saved, List.map, List.cons_append, List.nil_append, runBlock_cons,
      runStep_some, runBlock_nil, at_, exec, readSrc, State.store64, State.ea, offset_nat,
      hw 2064 (by decide) (by decide), hw 2072 (by decide) (by decide), hw 2080 (by decide) (by decide),
      hw 2088 (by decide) (by decide), hw 2096 (by decide) (by decide), hw 2104 (by decide) (by decide),
      ite_true, Option.map_some, execAlu, Option.bind_some]
    rfl, ?_⟩
  simp only [reduceCtorEq, ↓reduceIte, and_self, gpr_setReg, gpr_arithFlags, zf_arithFlags, mem_setReg,
    mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, 
    BitVec.and_self]
  trivial

end VG.Proof.CmacAes.X86_64

namespace VG.Proof.CmacAes.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.CmacAes.X86_64

/-- The memory after `chainIn`: the counter block at `c` is the state at `p`
XORed with the block at `q`, and the state is zeroed. -/
def chainMem (m : Mem) (c p q : Addr) : Mem :=
  let m₁ := m.writeW c (m.readW p 64 ^^^ m.readW q 64)
  let m₂ := m₁.writeW (c + BitVec.ofNat 64 8) (m₁.readW (p + BitVec.ofNat 64 8) 64 ^^^ m₁.readW (q + BitVec.ofNat 64 8) 64)
  (m₂.writeW p (0 : BitVec 64)).writeW (p + BitVec.ofNat 64 8) (0 : BitVec 64)

theorem chainIn_ok (s : State) {C P Q : Addr} (hc : s.gpr .r15 + BitVec.ofNat 64 2048 = C)
    (hp : s.gpr .r12 = P) (hq : s.gpr .r13 = Q)
    (rp : InRegions (s.rd ++ s.wr) P 8) (rp8 : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 8) 8)
    (rq : InRegions (s.rd ++ s.wr) Q 8) (rq8 : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 8) 8)
    (wc : InRegions s.wr C 8) (wc8 : InRegions s.wr (C + BitVec.ofNat 64 8) 8)
    (wp : InRegions s.wr P 8) (wp8 : InRegions s.wr (P + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa (chainIn ++ updArgs) s = some s' ∧
      s'.gpr .rdi = s.gpr .rbx ∧ s'.gpr .rsi = s.gpr .rbp ∧ s'.gpr .rdx = C ∧ s'.gpr .rcx = P ∧
      s'.gpr .r8 = 1 ∧ s'.gpr .r9 = s.gpr .r15 ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      s'.mem = chainMem s.mem C P Q ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hc' : s.gpr .r15 + BitVec.ofNat 64 2056 = C + BitVec.ofNat 64 8 := by
    rw [← hc, BitVec.add_assoc]; rfl
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceAdd, Nat.reducePow, BitVec.reduceSignExtend, chainIn, updArgs, ctrArgs, cOff, List.cons_append,
      List.nil_append, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc, readSrc32,
      State.load64, State.store64, State.ea, offset_nat, execAlu, Option.bind_some, Option.map_some,
      gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg,
      wr_arithFlags, State.setReg32, hc, hc', hp, hq, BitVec.add_zero,
      rp, rp8, rq, rq8, wc, wc8, wp, wp8]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl⟩
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · simp [gpr_setReg, ← hc]
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]
  · rfl

theorem frame_store2 {m : Mem} (p : Addr) (w₀ w₁ : BitVec 64) :
    Frame [⟨p, 16⟩] m ((m.writeW p w₀).writeW (p + BitVec.ofNat 64 8) w₁) :=
  ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (by simpa using Offset.contains_base p (d := 0) (n := 8) (k := 16) (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (Offset.contains_base p (d := 8) (n := 8) (k := 16) (by decide) (by decide))

theorem chainMem_frame (m : Mem) (C P Q : Addr) : Frame [⟨C, 16⟩, ⟨P, 16⟩] m (chainMem m C P Q) := by
  have f₁ : Frame [⟨C, 16⟩, ⟨P, 16⟩] m _ :=
    (frame_store2 (m := m) C (m.readW P 64 ^^^ m.readW Q 64)
      ((m.writeW C (m.readW P 64 ^^^ m.readW Q 64)).readW (P + BitVec.ofNat 64 8) 64 ^^^
        (m.writeW C (m.readW P 64 ^^^ m.readW Q 64)).readW (Q + BitVec.ofNat 64 8) 64)).mono
      (fun r hr => by simp only [List.mem_singleton] at hr; simp [hr])
  exact f₁.trans ((frame_store2 P 0 0).mono (fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]))

theorem chainMem_state (m : Mem) (C P Q : Addr) :
    Spec.Aes.bytesAt (chainMem m C P Q) P 16 = Spec.Cmac.zeros 16 := by
  rw [chainMem, Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_zero]; rfl

theorem bytesAt_frame' {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 16⟩ : Region).Disjoint r) : Spec.Aes.bytesAt m' p 16 = Spec.Aes.bytesAt m p 16 :=
  bytesAt_frame hf hd (by decide)

theorem readW_frame16 {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {d : Nat} (hd8 : d + 8 ≤ 16)
    (hd : ∀ r ∈ rs, (⟨p, 16⟩ : Region).Disjoint r) :
    m'.readW (p + BitVec.ofNat 64 d) 64 = m.readW (p + BitVec.ofNat 64 d) 64 :=
  hf.readW (r := ⟨p + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
    (fun r hr => (hd r hr).sub_left (Offset.sub_base p hd8)) (by decide)

theorem chainMem_counter (m : Mem) {C P Q : Addr} (hcp : (⟨C, 16⟩ : Region).Disjoint ⟨P, 16⟩)
    (hcq : (⟨C, 16⟩ : Region).Disjoint ⟨Q, 16⟩) :
    Spec.Aes.bytesAt (chainMem m C P Q) C 16 =
      Spec.Cmac.xor (Spec.Aes.bytesAt m P 16) (Spec.Aes.bytesAt m Q 16) := by
  rw [chainMem, bytesAt_frame' (frame_store2 P 0 0) (by simpa using hcp), Proof.Cmac.bytesAt_store2]
  have g : Frame [⟨C, 16⟩] m (m.writeW C (m.readW P 64 ^^^ m.readW Q 64)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (by simpa using Offset.contains_base C (d := 0) (n := 8) (k := 16) (by decide) (by decide))
  rw [readW_frame16 g (d := 8) (by decide) (by simpa using hcp.symm),
    readW_frame16 g (d := 8) (by decide) (by simpa using hcq.symm)]
  exact Proof.Cmac.xor_words m P Q

end VG.Proof.CmacAes.X86_64

end

/-!
# AES-CMAC on x86-64: the loop of `vg_cmac_aes_update`

The invariant after `k` blocks (`LInv`): the registers hold the arguments
(`r13` the next block, `r14` the blocks left), only the state, the first 2064
bytes of the scratch buffer and the stack below the return address have
changed since the registers were saved, and the state is the chaining value
after the first `k` blocks.
-/

namespace VG.Proof.CmacAes.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.CmacAes.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)

section
variable (s₀ : State)

abbrev W : Addr := s₀.gpr .rdi
abbrev R : Nat := (s₀.gpr .rsi).toNat
abbrev St : Addr := s₀.gpr .rdx
abbrev Dp : Addr := s₀.gpr .rcx
abbrev N : Nat := (s₀.gpr .r8).toNat
abbrev S : Addr := s₀.gpr .r9

abbrev schR : Region := ⟨W s₀, 240⟩
abbrev stR : Region := ⟨St s₀, 16⟩
abbrev dataR : Region := ⟨Dp s₀, 16 * N s₀⟩
abbrev scrR : Region := ⟨S s₀, 2176⟩
abbrev stkR : Region := below (s₀.gpr .rsp) 8

/-- The cipher. -/
abbrev ciph : Spec.Cmac.Cipher := ciphAt s₀.mem (W s₀) (R s₀)

/-- The message blocks. -/
abbrev blks : List (List Byte) := Spec.Cmac.blocksAt s₀.mem (Dp s₀) 16 (N s₀)

end

/-- The precondition, by name. -/
structure UPre (s₀ : State) : Prop where
  rd : s₀.rd = [schR s₀, dataR s₀]
  wr : s₀.wr = [stR s₀, scrR s₀]
  sch_st : (schR s₀).Disjoint (stR s₀)
  sch_scr : (schR s₀).Disjoint (scrR s₀)
  data_st : (dataR s₀).Disjoint (stR s₀)
  data_scr : (dataR s₀).Disjoint (scrR s₀)
  st_scr : (stR s₀).Disjoint (scrR s₀)
  ret_st : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint (stR s₀)
  ret_scr : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint (scrR s₀)
  stk_sch : (stkR s₀).Disjoint (schR s₀)
  stk_data : (stkR s₀).Disjoint (dataR s₀)
  stk_st : (stkR s₀).Disjoint (stR s₀)
  stk_scr : (stkR s₀).Disjoint (scrR s₀)
  st_wrap : (St s₀).toNat + 16 ≤ 2 ^ 64
  data_wrap : (Dp s₀).toNat + 16 * N s₀ ≤ 2 ^ 64
  scr_wrap : (S s₀).toNat + 2176 ≤ 2 ^ 64
  rounds : R s₀ = 10 ∨ R s₀ = 12 ∨ R s₀ = 14

theorem UPre.of {s₀ : State} (h : updateX86_64.pre s₀) : UPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q⟩

/-- The loop invariant, after `k` blocks. -/
structure LInv (s₀ : State) (k : Nat) (s : State) : Prop where
  rbx : s.gpr .rbx = W s₀
  rbp : s.gpr .rbp = s₀.gpr .rsi
  r12 : s.gpr .r12 = St s₀
  r13 : s.gpr .r13 = Dp s₀ + BitVec.ofNat 64 (16 * k)
  r14 : s.gpr .r14 = BitVec.ofNat 64 (N s₀ - k)
  r15 : s.gpr .r15 = S s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR s₀, ⟨S s₀, 2064⟩, stkR s₀] (savedMem s₀) s.mem
  state : Spec.Aes.bytesAt s.mem (St s₀) 16 =
    Spec.Cmac.chain (ciph s₀) (Spec.Aes.bytesAt s₀.mem (St s₀) 16) ((blks s₀).take k)

/-! ## Regions -/

section
variable {s₀ : State}

theorem UPre.scr_sub {d n : Nat} (h : d + n ≤ 2176) : Region.Sub ⟨S s₀ + BitVec.ofNat 64 d, n⟩ (scrR s₀) :=
  Offset.sub_base _ h

theorem UPre.data_sub {k : Nat} (hk : k < N s₀) :
    Region.Sub ⟨Dp s₀ + BitVec.ofNat 64 (16 * k), 16⟩ (dataR s₀) :=
  Offset.sub_base _ (by omega)

theorem UPre.sch_sub {R' : Nat} (h : R' ≤ 240) : Region.Sub ⟨W s₀, R'⟩ (schR s₀) :=
  Region.sub_prefix h

end

theorem slot_contains (b : Addr) {d : Nat} (h₁ : 2064 ≤ d) (h₂ : d + 8 ≤ 2112) :
    (⟨b + BitVec.ofNat 64 2064, 48⟩ : Region).Contains (b + BitVec.ofNat 64 d) 8 := by
  rw [show b + BitVec.ofNat 64 d = (b + BitVec.ofNat 64 2064) + BitVec.ofNat 64 (d - 2064) from
    (Offset.add_add_eq b (by omega)).symm]
  exact Offset.contains_base _ (by omega) (by omega)

/-- Saving the registers changes only their slots. -/
theorem savedMem_frame (s : State) : Frame [⟨s.gpr .r9 + BitVec.ofNat 64 2064, 48⟩] s.mem (savedMem s) :=
  Spill.saveMem_frame _ _ _ _ fun p hp => slot_contains _ (saved_bound p hp).1 (saved_bound p hp).2

theorem advance_ok (s : State) :
    ∃ s', runBlock isa advance s = some s' ∧
      s'.gpr .r13 = s.gpr .r13 + BitVec.ofNat 64 16 ∧ s'.gpr .r14 = s.gpr .r14 - 1 ∧
      s'.zf = some ((s.gpr .r14 - 1) == 0) ∧ (∀ r, r ≠ .r13 → r ≠ .r14 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, BitVec.reduceSignExtend, advance, runBlock_cons, runStep_some, runBlock_nil, exec,
      execAlu, readSrc, Option.bind_some, gpr_setReg, gpr_arithFlags]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · simp [gpr_setReg]
  · exact gpr_setReg_self _ _ _
  · rw [zf_setReg, zf_arithFlags]; simp
  · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]

theorem rsi_ofNat (s₀ : State) : s₀.gpr .rsi = BitVec.ofNat 64 (R s₀) := by
  apply BitVec.eq_of_toNat_eq; simp [R]

theorem take_succ_blks (s₀ : State) {k : Nat} (hk : k < N s₀) :
    (blks s₀).take (k + 1) =
      (blks s₀).take k ++ [Spec.Aes.bytesAt s₀.mem (Dp s₀ + BitVec.ofNat 64 (16 * k)) 16] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simp [Spec.Cmac.blocksAt]; omega)]
  simp [Spec.Cmac.blocksAt]

theorem in_rw {rs : List Region} {r : Region} (hr : r ∈ rs) {a : Addr} {n : Nat} (hc : r.Contains a n) :
    InRegions rs a n := ⟨r, hr, hc⟩

/-! ## Memory outside the writable regions -/

/-- The regions the function writes. -/
abbrev Big (s₀ : State) : List Region := [stR s₀, scrR s₀, stkR s₀]

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.sched_bytes {m : Mem} (hf : Frame (Big s₀) s₀.mem m) :
    Spec.Aes.bytesAt m (W s₀) (16 * (R s₀ + 1)) = Spec.Aes.bytesAt s₀.mem (W s₀) (16 * (R s₀ + 1)) := by
  have hR : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega
  refine bytesAt_frame hf (fun r hr => ?_) (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.sch_st.sub_left (Region.sub_prefix hR)
  · exact hp.sch_scr.sub_left (Region.sub_prefix hR)
  · exact hp.stk_sch.symm.sub_left (Region.sub_prefix hR)

theorem UPre.block_bytes {m : Mem} (hf : Frame (Big s₀) s₀.mem m) {k : Nat} (hk : k < N s₀) :
    Spec.Aes.bytesAt m (Dp s₀ + BitVec.ofNat 64 (16 * k)) 16 =
      Spec.Aes.bytesAt s₀.mem (Dp s₀ + BitVec.ofNat 64 (16 * k)) 16 := by
  refine bytesAt_frame hf (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.data_st.sub_left (UPre.data_sub hk)
  · exact hp.data_scr.sub_left (UPre.data_sub hk)
  · exact hp.stk_data.symm.sub_left (UPre.data_sub hk)

omit hp in
theorem UPre.big_of {m : Mem} (hf : Frame [stR s₀, ⟨S s₀, 2064⟩, stkR s₀] (savedMem s₀) m) :
    Frame (Big s₀) s₀.mem m := by
  have f₀ : Frame (Big s₀) s₀.mem (savedMem s₀) :=
    (savedMem_frame s₀).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, UPre.scr_sub (by decide)⟩
  exact f₀.trans (hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR s₀, by simp, fun _ h => h⟩
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩)

end

/-! ## One block -/

/-- What the code before the call leaves. -/
structure BodyA (s₀ : State) (k : Nat) (s s₁ : State) : Prop where
  pre : CallPre s₁ (W s₀) (S s₀ + BitVec.ofNat 64 2048) (St s₀) (S s₀) (R s₀)
  saved : ∀ r ∈ calleeSaved, s₁.gpr r = s.gpr r
  mem : s₁.mem = chainMem s.mem (S s₀ + BitVec.ofNat 64 2048) (St s₀) (Dp s₀ + BitVec.ofNat 64 (16 * k))
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

theorem bodyA_wp {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State} (h : LInv s₀ k s) :
    WP isa (.block (chainIn ++ updArgs)) s (BodyA s₀ k s) := by
  have hRegs : s.rd ++ s.wr = [schR s₀, dataR s₀, stR s₀, scrR s₀] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have hW : s.wr = [stR s₀, scrR s₀] := by rw [h.wr, hp.wr]
  have h16k : 16 * k + 16 ≤ 16 * N s₀ := by omega
  have hdw := hp.data_wrap
  have cSt0 : (stR s₀).Contains (St s₀) 8 := by
    simpa using Offset.contains_base (St s₀) (d := 0) (n := 8) (k := 16) (by decide) (by decide)
  have cSt8 : (stR s₀).Contains (St s₀ + BitVec.ofNat 64 8) 8 := Offset.contains_base _ (by decide) (by decide)
  have cQ0 : (dataR s₀).Contains (Dp s₀ + BitVec.ofNat 64 (16 * k)) 8 :=
    Offset.contains_base _ (by omega) (by omega)
  have cQ8 : (dataR s₀).Contains (Dp s₀ + BitVec.ofNat 64 (16 * k) + BitVec.ofNat 64 8) 8 := by
    rw [Offset.add_add]; exact Offset.contains_base _ (by omega) (by omega)
  have cC0 : (scrR s₀).Contains (S s₀ + BitVec.ofNat 64 2048) 8 := Offset.contains_base _ (by decide) (by decide)
  have cC8 : (scrR s₀).Contains (S s₀ + BitVec.ofNat 64 2048 + BitVec.ofNat 64 8) 8 := by
    rw [Offset.add_add]; exact Offset.contains_base _ (by decide) (by decide)
  obtain ⟨s₁, run₁, rdi₁, rsi₁, rdx₁, rcx₁, r8₁, r9₁, cs₁, mem₁, rd₁, wr₁⟩ :=
    chainIn_ok s (C := S s₀ + BitVec.ofNat 64 2048) (P := St s₀) (Q := Dp s₀ + BitVec.ofNat 64 (16 * k))
      (by rw [h.r15]) h.r12 h.r13
      (by rw [hRegs]; exact in_rw (by simp) cSt0) (by rw [hRegs]; exact in_rw (by simp) cSt8)
      (by rw [hRegs]; exact in_rw (by simp) cQ0) (by rw [hRegs]; exact in_rw (by simp) cQ8)
      (by rw [hW]; exact in_rw (by simp) cC0) (by rw [hW]; exact in_rw (by simp) cC8)
      (by rw [hW]; exact in_rw (by simp) cSt0) (by rw [hW]; exact in_rw (by simp) cSt8)
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := by rw [cs₁ .rsp (by simp [calleeSaved]), h.rsp]
  have hR : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega
  have cDis : (⟨S s₀ + BitVec.ofNat 64 2048, 16⟩ : Region).Disjoint ⟨S s₀, 2048⟩ :=
    Offset.disjoint_base _ (by decide) (by have := hp.scr_wrap; omega)
  have pre : CallPre s₁ (W s₀) (S s₀ + BitVec.ofNat 64 2048) (St s₀) (S s₀) (R s₀) :=
    { rdi := by rw [rdi₁, h.rbx]
      rsi := by rw [rsi₁, h.rbp, rsi_ofNat]
      rdx := rdx₁
      rcx := rcx₁
      r8 := r8₁
      r9 := by rw [r9₁, h.r15]
      rounds := hp.rounds
      wc := hp.sch_scr.sub_right (UPre.scr_sub (by decide))
      wd := hp.sch_st
      ws := hp.sch_scr.sub_right (Region.sub_prefix (by decide))
      cd := hp.st_scr.symm.sub_left (UPre.scr_sub (by decide))
      cs := cDis
      ds := hp.st_scr.sub_right (Region.sub_prefix (by decide))
      stkW := by rw [rsp₁]; exact hp.stk_sch
      stkC := by rw [rsp₁]; exact hp.stk_scr.sub_right (UPre.scr_sub (by decide))
      stkD := by rw [rsp₁]; exact hp.stk_st
      stkS := by rw [rsp₁]; exact hp.stk_scr.sub_right (Region.sub_prefix (by decide))
      wrap := hp.st_wrap
      reads := by
        rw [rd₁, wr₁, hRegs]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
        · exact ⟨scrR s₀, by simp, 2048, rfl, by simp⟩
        · exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
        · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩
      writes := by
        rw [wr₁, hW]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨scrR s₀, by simp, 2048, rfl, by simp⟩
        · exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
        · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩
      zero := by rw [mem₁]; exact chainMem_state _ _ _ _ }
  exact ⟨pre, cs₁, mem₁, rd₁, wr₁⟩

theorem body_ok (v : Ctr32Impl) {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State}
    (h : LInv s₀ k s) :
    WP isa (body v.callee) s fun s' => LInv s₀ (k + 1) s' ∧ s'.zf = some (decide (N s₀ - (k + 1) = 0)) := by
  have h16k : 16 * k + 16 ≤ 16 * N s₀ := by omega
  have hdw := hp.data_wrap
  refine WP.seq (WP.mono (bodyA_wp hp hk h) fun s₁ ⟨pre, cs₁, mem₁, rd₁, wr₁⟩ => ?_)
  have rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := by rw [cs₁ .rsp (by simp [calleeSaved]), h.rsp]
  refine WP.seq (WP.mono (ctr_call v pre) fun s₂ h₂ => ?_)
  obtain ⟨s₃, run₃, r13₃, r14₃, zf₃, keep₃, mem₃, rd₃, wr₃⟩ := advance_ok s₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have g (r : Reg) (hr : r ∈ calleeSaved) (h13 : r ≠ .r13) (h14 : r ≠ .r14) : s₃.gpr r = s.gpr r := by
    rw [keep₃ r h13 h14, h₂.saved r hr, cs₁ r hr]
  have r13₂ : s₂.gpr .r13 = Dp s₀ + BitVec.ofNat 64 (16 * k) := by
    rw [h₂.saved .r13 (by simp [calleeSaved]), cs₁ .r13 (by simp [calleeSaved]), h.r13]
  have r14₂ : s₂.gpr .r14 = BitVec.ofNat 64 (N s₀ - k) := by
    rw [h₂.saved .r14 (by simp [calleeSaved]), cs₁ .r14 (by simp [calleeSaved]), h.r14]
  have hN := (s₀.gpr .r8).isLt
  have dec : BitVec.ofNat 64 (N s₀ - k) - 1 = BitVec.ofNat 64 (N s₀ - (k + 1)) := by
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega)]; rfl
  -- Memory.
  have bigS := UPre.big_of h.frame
  have f₁ : Frame [⟨S s₀ + BitVec.ofNat 64 2048, 16⟩, ⟨St s₀, 16⟩] s.mem s₁.mem := by
    rw [mem₁]; exact chainMem_frame _ _ _ _
  have big₁ : Frame (Big s₀) s₀.mem s₁.mem := bigS.trans (f₁.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨scrR s₀, by simp, UPre.scr_sub (by decide)⟩
    · exact ⟨stR s₀, by simp, fun _ h => h⟩)
  have cst : (⟨S s₀ + BitVec.ofNat 64 2048, 16⟩ : Region).Disjoint (stR s₀) :=
    hp.st_scr.symm.sub_left (UPre.scr_sub (by decide))
  have cq : (⟨S s₀ + BitVec.ofNat 64 2048, 16⟩ : Region).Disjoint ⟨Dp s₀ + BitVec.ofNat 64 (16 * k), 16⟩ :=
    (hp.data_scr.symm.sub_left (UPre.scr_sub (by decide))).sub_right (UPre.data_sub hk)
  have out := h₂.out
  rw [UPre.sched_bytes hp big₁, mem₁, chainMem_counter _ cst cq, h.state,
    UPre.block_bytes hp bigS hk] at out
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [g .rbx (by simp [calleeSaved]) (by decide) (by decide), h.rbx]
  · rw [g .rbp (by simp [calleeSaved]) (by decide) (by decide), h.rbp]
  · rw [g .r12 (by simp [calleeSaved]) (by decide) (by decide), h.r12]
  · rw [r13₃, r13₂, Offset.add_add_eq _ (c := 16 * (k + 1)) (by omega)]
  · rw [r14₃, r14₂, dec]
  · rw [g .r15 (by simp [calleeSaved]) (by decide) (by decide), h.r15]
  · rw [g .rsp (by simp [calleeSaved]) (by decide) (by decide), h.rsp]
  · rw [rd₃, h₂.rd, rd₁, h.rd]
  · rw [wr₃, h₂.wr, wr₁, h.wr]
  · rw [mem₃]
    refine h.frame.trans ((f₁.sub fun r hr => ?_).trans (h₂.frame.sub fun r hr => ?_))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨S s₀, 2064⟩, by simp, Offset.sub_base _ (by decide)⟩
      · exact ⟨stR s₀, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨S s₀, 2064⟩, by simp, Offset.sub_base _ (by decide)⟩
      · exact ⟨stR s₀, by simp, fun _ h => h⟩
      · exact ⟨⟨S s₀, 2064⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨stkR s₀, by simp, by rw [rsp₁]; exact fun _ h => h⟩
  · rw [mem₃, out, take_succ_blks s₀ hk, Proof.Cmac.chain_append, Proof.Cmac.chain_single]
  · rw [zf₃, r14₂, dec]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    constructor
    · intro he
      have := congrArg BitVec.toNat he
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      simpa using this
    · intro he; rw [he]; rfl

end VG.Proof.CmacAes.X86_64
