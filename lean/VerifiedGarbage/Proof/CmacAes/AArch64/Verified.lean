import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Impl.CmacAes.AArch64
import VerifiedGarbage.Proof.Aes.AArch64.Variant
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Gcm.AArch64.Ghash
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Cmac.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.AArch64.UpdateLoop`. -/
section

section

section

section

/-!
# AES-CMAC on AArch64: calling `vg_aes_ctr32` on one block

`ctr_call`: a call of any implementation of `vg_aes_ctr32` with the counter
block `C`, one data block `D` holding zeros, and working space `S`, from its
contract (with `WP.call`): `D` then holds `CIPH_K(C)`, as bytes
(`Cmac.aesWith`), and only `C`, `D` and `S` change in memory.
-/

namespace VG.Proof.CmacAes.AArch64

open VG VG.AArch64
open VG.Proof.Aes.AArch64 (Ctr32Impl)

theorem ofBytes_zeros : Spec.Gcm.ofBytes (Spec.Cmac.zeros 16) = 0 := by decide

theorem toNat_rounds {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) : (BitVec.ofNat 64 R).toNat = R := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)

theorem one_toNat : (1 : BitVec 64).toNat = 1 := rfl

/-- What a call of `vg_aes_ctr32` on one block needs. -/
structure CallPre (s : State) (W C D S : Addr) (R : Nat) : Prop where
  x0 : s.gpr .x0 = W
  x1 : s.gpr .x1 = BitVec.ofNat 64 R
  x2 : s.gpr .x2 = C
  x3 : s.gpr .x3 = D
  x4 : s.gpr .x4 = 1
  x5 : s.gpr .x5 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  wc : (⟨W, 240⟩ : Region).Disjoint ⟨C, 16⟩
  wd : (⟨W, 240⟩ : Region).Disjoint ⟨D, 16⟩
  ws : (⟨W, 240⟩ : Region).Disjoint ⟨S, 2048⟩
  cd : (⟨C, 16⟩ : Region).Disjoint ⟨D, 16⟩
  cs : (⟨C, 16⟩ : Region).Disjoint ⟨S, 2048⟩
  ds : (⟨D, 16⟩ : Region).Disjoint ⟨S, 2048⟩
  wrap : D.toNat + 16 ≤ 2 ^ 64
  reads : Covers ([⟨W, 240⟩] ++ [⟨C, 16⟩, ⟨D, 16⟩, ⟨S, 2048⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨C, 16⟩, ⟨D, 16⟩, ⟨S, 2048⟩] s.wr
  zero : Spec.Aes.bytesAt s.mem D 16 = Spec.Cmac.zeros 16

/-- What a call of `vg_aes_ctr32` on one block leaves. -/
structure CallPost (s : State) (W C D S : Addr) (R : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r
  frame : Frame [⟨C, 16⟩, ⟨D, 16⟩, ⟨S, 2048⟩] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem D 16 =
    Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem W (16 * (R + 1))) (Spec.Aes.bytesAt s.mem C 16)

theorem callEntry_x0 (s : State) : s.callEntry.gpr .x0 = s.gpr .x0 := s.callEntry_gpr (by decide)
theorem callEntry_x1 (s : State) : s.callEntry.gpr .x1 = s.gpr .x1 := s.callEntry_gpr (by decide)
theorem callEntry_x2 (s : State) : s.callEntry.gpr .x2 = s.gpr .x2 := s.callEntry_gpr (by decide)
theorem callEntry_x3 (s : State) : s.callEntry.gpr .x3 = s.gpr .x3 := s.callEntry_gpr (by decide)
theorem callEntry_x4 (s : State) : s.callEntry.gpr .x4 = s.gpr .x4 := s.callEntry_gpr (by decide)
theorem callEntry_x5 (s : State) : s.callEntry.gpr .x5 = s.gpr .x5 := s.callEntry_gpr (by decide)

/-- `vg_aes_ctr32`'s precondition, on entry to a call with the regions it is given. -/
theorem CallPre.ctr_pre {s : State} {W C D S : Addr} {R : Nat} (h : VG.Proof.CmacAes.AArch64.CallPre s W C D S R) :
    Proof.Aes.ctr32AArch64.pre
      (s.callEntry.withRegions [⟨W, 240⟩] [⟨C, 16⟩, ⟨D, 16⟩, ⟨S, 2048⟩]) := by
  have hR := VG.Proof.CmacAes.AArch64.toNat_rounds h.rounds
  simp only [Proof.Aes.ctr32AArch64, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, VG.Proof.CmacAes.AArch64.callEntry_x0, VG.Proof.CmacAes.AArch64.callEntry_x1, VG.Proof.CmacAes.AArch64.callEntry_x2, VG.Proof.CmacAes.AArch64.callEntry_x3, VG.Proof.CmacAes.AArch64.callEntry_x4,
    VG.Proof.CmacAes.AArch64.callEntry_x5, h.x0, h.x1, h.x2, h.x3, h.x4, h.x5, hR, VG.Proof.CmacAes.AArch64.one_toNat, Nat.mul_one]
  exact ⟨trivial, trivial, h.wc, by simpa using h.wd, h.ws, by simpa using h.cd, h.cs,
    by simpa using h.ds, by simpa using h.wrap, h.rounds⟩

theorem ctr_call (v : Ctr32Impl) {s : State} {W C D S : Addr} {R : Nat} (h : VG.Proof.CmacAes.AArch64.CallPre s W C D S R) :
    WP isa (.call v.callee.name v.callee.code) s (VG.Proof.CmacAes.AArch64.CallPost s W C D S R) := by
  have hR := VG.Proof.CmacAes.AArch64.toNat_rounds h.rounds
  refine WP.call (k := Proof.Aes.ctr32AArch64) v.ok (rd := [⟨W, 240⟩])
    (wr := [⟨C, 16⟩, ⟨D, 16⟩, ⟨S, 2048⟩]) h.ctr_pre h.reads h.writes ?_ v.noFrames
  intro s' hrd hwr hsp hf hsaved _ hpost
  refine ⟨hrd, hwr, hsp, hsaved, hf, ?_⟩
  obtain ⟨hdata, -⟩ := hpost
  simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, VG.Proof.CmacAes.AArch64.callEntry_x0,
    VG.Proof.CmacAes.AArch64.callEntry_x1, VG.Proof.CmacAes.AArch64.callEntry_x2, VG.Proof.CmacAes.AArch64.callEntry_x3, VG.Proof.CmacAes.AArch64.callEntry_x4, h.x0, h.x1, h.x2, h.x3, h.x4, hR,
    VG.Proof.CmacAes.AArch64.one_toNat] at hdata
  have one : ∀ m : Mem, Spec.Gcm.blocksAt m D 1 = [Spec.Gcm.blockAt m D] := fun m => by
    simp [Spec.Gcm.blocksAt]
  have bD : Spec.Gcm.blockAt s.mem D = 0 := by rw [Spec.Gcm.blockAt, h.zero, VG.Proof.CmacAes.AArch64.ofBytes_zeros]
  rw [one, one, bD, Proof.Cmac.ctr32_one, List.cons.injEq] at hdata
  rw [Proof.Cmac.bytesAt_blockAt, hdata.1, Spec.Gcm.blockAt,
    Proof.Cmac.aesWith_bytes _ _ (Proof.Cmac.bytesAt_length _ _ _)]

/-- Calls of `vg_aes_ctr32` on one block, with the same arguments in both
runs, are constant time. -/
theorem ctr_rel (v : Ctr32Impl) {W C D S : Addr} {R : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → VG.Proof.CmacAes.AArch64.CallPre s₁ W C D S R ∧ VG.Proof.CmacAes.AArch64.CallPre s₂ W C D S R ∧ s₁.sp = s₂.sp) :
    RelCT isa P (.call v.callee.name v.callee.code) fun _ _ => True := by
  refine RelCT.call v.ok v.ct [⟨W, 240⟩] [⟨C, 16⟩, ⟨D, 16⟩, ⟨S, 2048⟩] fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨h₁.ctr_pre, h₂.ctr_pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes⟩
  simp only [Proof.Aes.ctr32AArch64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    VG.Proof.CmacAes.AArch64.callEntry_x0, VG.Proof.CmacAes.AArch64.callEntry_x1, VG.Proof.CmacAes.AArch64.callEntry_x2, VG.Proof.CmacAes.AArch64.callEntry_x3, VG.Proof.CmacAes.AArch64.callEntry_x4, VG.Proof.CmacAes.AArch64.callEntry_x5,
    h₁.x0, h₁.x1, h₁.x2, h₁.x3, h₁.x4, h₁.x5, h₂.x0, h₂.x1, h₂.x2, h₂.x3, h₂.x4, h₂.x5, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

end VG.Proof.CmacAes.AArch64

end

/-!
# AES-CMAC on AArch64: the contracts the proofs are written against

The artifacts' contracts are the shared ones of `Spec/Cmac/Contract.lean`,
which imply these (`Verified.lean`). A call (`bl`) stores nothing in memory,
so no stack is used.
-/

namespace VG.Proof.CmacAes.AArch64

open VG VG.AArch64

/-- `CIPH_K` for AES with the key schedule at `w` for `R` rounds, in `m`. -/
abbrev ciphAt (m : Mem) (w : Addr) (R : Nat) : Spec.Cmac.Cipher :=
  Spec.Cmac.aesWith R (Spec.Aes.bytesAt m w (16 * (R + 1)))

/-- `vg_cmac_aes_update(schedule = x0, rounds = x1, state = x2, data = x3, n = x4, scratch = x5)`. -/
def updateAArch64 : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .x0, 240⟩
    let state : Region := ⟨s.gpr .x2, 16⟩
    let data : Region := ⟨s.gpr .x3, 16 * (s.gpr .x4).toNat⟩
    let scr : Region := ⟨s.gpr .x5, 2176⟩
    s.rd = [sched, data] ∧ s.wr = [state, scr] ∧
      sched.Disjoint state ∧ sched.Disjoint scr ∧ data.Disjoint state ∧ data.Disjoint scr ∧
      state.Disjoint scr ∧
      (s.gpr .x2).toNat + 16 ≤ 2 ^ 64 ∧ (s.gpr .x3).toNat + 16 * (s.gpr .x4).toNat ≤ 2 ^ 64 ∧
      (s.gpr .x5).toNat + 2176 ≤ 2 ^ 64 ∧
      ((s.gpr .x1).toNat = 10 ∨ (s.gpr .x1).toNat = 12 ∨ (s.gpr .x1).toNat = 14)
  post s s' :=
    Spec.Aes.bytesAt s'.mem (s.gpr .x2) 16 =
      Spec.Cmac.chain (VG.Proof.CmacAes.AArch64.ciphAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) (Spec.Aes.bytesAt s.mem (s.gpr .x2) 16)
        (Spec.Cmac.blocksAt s.mem (s.gpr .x3) 16 (s.gpr .x4).toNat)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧ s₁.sp = s₂.sp

/-- `vg_cmac_aes_subkeys(schedule = x0, rounds = x1, subkeys = x2, scratch = x3)`. -/
def subkeysAArch64 : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .x0, 240⟩
    let subk : Region := ⟨s.gpr .x2, 32⟩
    let scr : Region := ⟨s.gpr .x3, 2176⟩
    s.rd = [sched] ∧ s.wr = [subk, scr] ∧
      sched.Disjoint subk ∧ sched.Disjoint scr ∧ subk.Disjoint scr ∧
      (s.gpr .x2).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .x3).toNat + 2176 ≤ 2 ^ 64 ∧
      ((s.gpr .x1).toNat = 10 ∨ (s.gpr .x1).toNat = 12 ∨ (s.gpr .x1).toNat = 14)
  post s s' :=
    let ks := Spec.Cmac.subkeys (VG.Proof.CmacAes.AArch64.ciphAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) 16
    Spec.Aes.bytesAt s'.mem (s.gpr .x2) 32 = ks.1 ++ ks.2
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

/-- `vg_cmac_aes_finalize(key = x0, rounds = x1, state = x2, last = x3, last_len = x4, scratch = x5)`. -/
def finalizeAArch64 : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, 272⟩
    let state : Region := ⟨s.gpr .x2, 16⟩
    let last : Region := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
    let scr : Region := ⟨s.gpr .x5, 2176⟩
    s.rd = [key, last] ∧ s.wr = [state, scr] ∧
      key.Disjoint state ∧ key.Disjoint scr ∧ last.Disjoint state ∧ last.Disjoint scr ∧
      state.Disjoint scr ∧
      (s.gpr .x0).toNat + 272 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + 16 ≤ 2 ^ 64 ∧
      (s.gpr .x3).toNat + (s.gpr .x4).toNat ≤ 2 ^ 64 ∧ (s.gpr .x5).toNat + 2176 ≤ 2 ^ 64 ∧
      ((s.gpr .x1).toNat = 10 ∨ (s.gpr .x1).toNat = 12 ∨ (s.gpr .x1).toNat = 14) ∧
      (s.gpr .x4).toNat ≤ 16
  post s s' :=
    let ciph := VG.Proof.CmacAes.AArch64.ciphAt s.mem (s.gpr .x0) (s.gpr .x1).toNat
    let ks := Spec.Cmac.subkeys ciph 16
    Spec.Aes.bytesAt s.mem (s.gpr .x0 + 240) 32 = ks.1 ++ ks.2 →
    ∀ msg : List Byte, msg.length % 16 = 0 → (msg = [] ∨ 0 < (s.gpr .x4).toNat) →
      Spec.Aes.bytesAt s.mem (s.gpr .x2) 16 = Spec.Cmac.chain ciph (Spec.Cmac.zeros 16) (Spec.Cmac.blocks 16 msg) →
      Spec.Aes.bytesAt s'.mem (s.gpr .x2) 16 =
        Spec.Cmac.macFull ciph 16 (msg ++ Spec.Aes.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧ s₁.sp = s₂.sp

end VG.Proof.CmacAes.AArch64

end

/-!
# AES-CMAC on AArch64: `vg_cmac_aes_update`, the blocks before and in the loop
-/

namespace VG.Proof.CmacAes.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.CmacAes.AArch64

/-- The memory after saving the registers. -/
def savedMem (s : State) : Mem :=
  saved.foldl (fun m (r, d) => m.writeW (s.gpr .x5 + BitVec.ofNat 64 d) (s.gpr r)) s.mem

theorem prologue_ok (s : State)
    (hw : ∀ d, 2064 ≤ d → d + 8 ≤ 2120 → InRegions s.wr (s.gpr .x5 + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa (save ++ setup) s = some s' ∧
      s'.gpr .x19 = s.gpr .x0 ∧ s'.gpr .x20 = s.gpr .x1 ∧ s'.gpr .x21 = s.gpr .x2 ∧
      s'.gpr .x22 = s.gpr .x3 ∧ s'.gpr .x23 = s.gpr .x4 ∧ s'.gpr .x24 = s.gpr .x5 ∧
      (∀ r, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x22 → r ≠ .x23 → r ≠ .x24 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = VG.Proof.CmacAes.AArch64.savedMem s ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul, Nat.reduceMod, and_self, save, setup, saved, mov, List.map, List.cons_append,
      List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.store, Size.bytes,
      Size.bits, State.read, gpr_write, Option.bind_some,
      hw 2064 (by decide) (by decide), hw 2072 (by decide) (by decide), hw 2080 (by decide) (by decide),
      hw 2088 (by decide) (by decide), hw 2096 (by decide) (by decide), hw 2104 (by decide) (by decide),
      hw 2112 (by decide) (by decide)]
    rfl, ?_⟩
  refine ⟨by simp [gpr_write], by simp [gpr_write], by simp [gpr_write], by simp [gpr_write],
    by simp [gpr_write], by simp [gpr_write], fun r h₁ h₂ h₃ h₄ h₅ h₆ => ?_, rfl, ?_, rfl, rfl⟩
  · simp [gpr_write, h₁, h₂, h₃, h₄, h₅, h₆]
  · simp only [mem_write, VG.Proof.CmacAes.AArch64.savedMem, saved, List.foldl, Mem.writeW, BitVec.setWidth_eq]

theorem chainIn_ok (s : State) {C P Q : Addr} (hc : s.gpr .x24 + BitVec.ofNat 64 2048 = C)
    (hp : s.gpr .x21 = P) (hq : s.gpr .x22 = Q)
    (rp : InRegions (s.rd ++ s.wr) P 8) (rp8 : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 8) 8)
    (rq : InRegions (s.rd ++ s.wr) Q 8) (rq8 : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 8) 8)
    (wc : InRegions s.wr C 8) (wc8 : InRegions s.wr (C + BitVec.ofNat 64 8) 8)
    (wp : InRegions s.wr P 8) (wp8 : InRegions s.wr (P + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa (chainIn ++ updArgs) s = some s' ∧
      s'.gpr .x0 = s.gpr .x19 ∧ s'.gpr .x1 = s.gpr .x20 ∧ s'.gpr .x2 = C ∧ s'.gpr .x3 = P ∧
      s'.gpr .x4 = 1 ∧ s'.gpr .x5 = s.gpr .x24 ∧
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      s'.mem = Proof.Cmac.chainMem s.mem C P Q ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hc' : s.gpr .x24 + BitVec.ofNat 64 2056 = C + BitVec.ofNat 64 8 := by
    rw [← hc, BitVec.add_assoc]; rfl
  refine ⟨_, by
    simp (config := {decide := true}) only [chainIn, updArgs, ctrArgs, cOff, mov, List.cons_append,
      List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.store,
      Size.bytes, Size.bits, State.read, gpr_write, mem_write, rd_write, wr_write, ite_true, ite_false,
      Option.bind_some, Option.map_some, hc, hc', hp, hq, BitVec.add_zero, BitVec.setWidth_eq,
      rp, rp8, rq, rq8, wc, wc8, wp, wp8]
    rfl, ?_⟩
  simp (config := {decide := true}) only [gpr_write, mem_write, rd_write, wr_write, sp_write,
    ite_true, ite_false, BitVec.setWidth_eq]
  refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, fun r hr => ?_, trivial, ?_, trivial⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · simp only [Proof.Cmac.chainMem, Mem.writeW, Mem.readW, BitVec.setWidth_eq]
    rfl

end VG.Proof.CmacAes.AArch64

end

/-!
# AES-CMAC on AArch64: the loop of `vg_cmac_aes_update`

The invariant after `k` blocks (`LInv`): the registers hold the arguments
(`x22` the next block, `x23` the blocks left), only the state and the first
2064 bytes of the scratch buffer have changed since the registers were saved,
and the state is the chaining value after the first `k` blocks.
-/

namespace VG.Proof.CmacAes.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.CmacAes.AArch64
open VG.Proof.Aes.AArch64 (Ctr32Impl)

section
variable (s₀ : State)

abbrev W : Addr := s₀.gpr .x0
abbrev R : Nat := (s₀.gpr .x1).toNat
abbrev St : Addr := s₀.gpr .x2
abbrev Dp : Addr := s₀.gpr .x3
abbrev N : Nat := (s₀.gpr .x4).toNat
abbrev S : Addr := s₀.gpr .x5

abbrev schR : Region := ⟨VG.Proof.CmacAes.AArch64.W s₀, 240⟩
abbrev stR : Region := ⟨VG.Proof.CmacAes.AArch64.St s₀, 16⟩
abbrev dataR : Region := ⟨VG.Proof.CmacAes.AArch64.Dp s₀, 16 * VG.Proof.CmacAes.AArch64.N s₀⟩
abbrev scrR : Region := ⟨VG.Proof.CmacAes.AArch64.S s₀, 2176⟩

/-- The cipher. -/
abbrev ciph : Spec.Cmac.Cipher := VG.Proof.CmacAes.AArch64.ciphAt s₀.mem (VG.Proof.CmacAes.AArch64.W s₀) (VG.Proof.CmacAes.AArch64.R s₀)

/-- The message blocks. -/
abbrev blks : List (List Byte) := Spec.Cmac.blocksAt s₀.mem (VG.Proof.CmacAes.AArch64.Dp s₀) 16 (VG.Proof.CmacAes.AArch64.N s₀)

end

/-- The precondition, by name. -/
structure UPre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.CmacAes.AArch64.schR s₀, VG.Proof.CmacAes.AArch64.dataR s₀]
  wr : s₀.wr = [VG.Proof.CmacAes.AArch64.stR s₀, VG.Proof.CmacAes.AArch64.scrR s₀]
  sch_st : (VG.Proof.CmacAes.AArch64.schR s₀).Disjoint (VG.Proof.CmacAes.AArch64.stR s₀)
  sch_scr : (VG.Proof.CmacAes.AArch64.schR s₀).Disjoint (VG.Proof.CmacAes.AArch64.scrR s₀)
  data_st : (VG.Proof.CmacAes.AArch64.dataR s₀).Disjoint (VG.Proof.CmacAes.AArch64.stR s₀)
  data_scr : (VG.Proof.CmacAes.AArch64.dataR s₀).Disjoint (VG.Proof.CmacAes.AArch64.scrR s₀)
  st_scr : (VG.Proof.CmacAes.AArch64.stR s₀).Disjoint (VG.Proof.CmacAes.AArch64.scrR s₀)
  st_wrap : (VG.Proof.CmacAes.AArch64.St s₀).toNat + 16 ≤ 2 ^ 64
  data_wrap : (VG.Proof.CmacAes.AArch64.Dp s₀).toNat + 16 * VG.Proof.CmacAes.AArch64.N s₀ ≤ 2 ^ 64
  scr_wrap : (VG.Proof.CmacAes.AArch64.S s₀).toNat + 2176 ≤ 2 ^ 64
  rounds : VG.Proof.CmacAes.AArch64.R s₀ = 10 ∨ VG.Proof.CmacAes.AArch64.R s₀ = 12 ∨ VG.Proof.CmacAes.AArch64.R s₀ = 14

theorem UPre.of {s₀ : State} (h : updateAArch64.pre s₀) : VG.Proof.CmacAes.AArch64.UPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k⟩

/-- The loop invariant, after `k` blocks. -/
structure LInv (s₀ : State) (k : Nat) (s : State) : Prop where
  x19 : s.gpr .x19 = VG.Proof.CmacAes.AArch64.W s₀
  x20 : s.gpr .x20 = s₀.gpr .x1
  x21 : s.gpr .x21 = VG.Proof.CmacAes.AArch64.St s₀
  x22 : s.gpr .x22 = VG.Proof.CmacAes.AArch64.Dp s₀ + BitVec.ofNat 64 (16 * k)
  x23 : s.gpr .x23 = BitVec.ofNat 64 (VG.Proof.CmacAes.AArch64.N s₀ - k)
  x24 : s.gpr .x24 = VG.Proof.CmacAes.AArch64.S s₀
  other : ∀ r ∈ preserved, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x22 → r ≠ .x23 → r ≠ .x24 →
    r ≠ .x30 → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [VG.Proof.CmacAes.AArch64.stR s₀, ⟨VG.Proof.CmacAes.AArch64.S s₀, 2064⟩] (VG.Proof.CmacAes.AArch64.savedMem s₀) s.mem
  state : Spec.Aes.bytesAt s.mem (VG.Proof.CmacAes.AArch64.St s₀) 16 =
    Spec.Cmac.chain (VG.Proof.CmacAes.AArch64.ciph s₀) (Spec.Aes.bytesAt s₀.mem (VG.Proof.CmacAes.AArch64.St s₀) 16) ((VG.Proof.CmacAes.AArch64.blks s₀).take k)

/-! ## Regions -/

section
variable {s₀ : State}

theorem UPre.scr_sub {d n : Nat} (h : d + n ≤ 2176) : Region.Sub ⟨VG.Proof.CmacAes.AArch64.S s₀ + BitVec.ofNat 64 d, n⟩ (VG.Proof.CmacAes.AArch64.scrR s₀) :=
  Offset.sub_base _ h

theorem UPre.data_sub {k : Nat} (hk : k < VG.Proof.CmacAes.AArch64.N s₀) :
    Region.Sub ⟨VG.Proof.CmacAes.AArch64.Dp s₀ + BitVec.ofNat 64 (16 * k), 16⟩ (VG.Proof.CmacAes.AArch64.dataR s₀) :=
  Offset.sub_base _ (by omega)

end

theorem slot_contains (b : Addr) {d : Nat} (h₁ : 2064 ≤ d) (h₂ : d + 8 ≤ 2120) :
    (⟨b + BitVec.ofNat 64 2064, 56⟩ : Region).Contains (b + BitVec.ofNat 64 d) 8 := by
  rw [show b + BitVec.ofNat 64 d = (b + BitVec.ofNat 64 2064) + BitVec.ofNat 64 (d - 2064) from
    (Offset.add_add_eq b (by omega)).symm]
  exact Offset.contains_base _ (by omega) (by omega)

/-- Saving the registers changes only their slots. -/
theorem savedMem_frame (s : State) : Frame [⟨s.gpr .x5 + BitVec.ofNat 64 2064, 56⟩] s.mem (VG.Proof.CmacAes.AArch64.savedMem s) := by
  simp only [VG.Proof.CmacAes.AArch64.savedMem, saved, List.foldl]
  exact ((((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (VG.Proof.CmacAes.AArch64.slot_contains _ (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (VG.Proof.CmacAes.AArch64.slot_contains _ (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (VG.Proof.CmacAes.AArch64.slot_contains _ (by decide) (by decide))).writeW (List.mem_singleton_self _) _
    (VG.Proof.CmacAes.AArch64.slot_contains _ (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (VG.Proof.CmacAes.AArch64.slot_contains _ (by decide) (by decide))).writeW (List.mem_singleton_self _) _
    (VG.Proof.CmacAes.AArch64.slot_contains _ (by decide) (by decide))).writeW (List.mem_singleton_self _) _
    (VG.Proof.CmacAes.AArch64.slot_contains _ (by decide) (by decide)))

theorem advance_ok (s : State) :
    ∃ s', runBlock isa advance s = some s' ∧
      s'.gpr .x22 = s.gpr .x22 + BitVec.ofNat 64 16 ∧ s'.gpr .x23 = s.gpr .x23 - 1 ∧
      (∀ r, r ≠ .x22 → r ≠ .x23 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    rw [advance, runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons,
      exec_subImm_x (by decide), runStep_some, runBlock_nil], ?_⟩
  refine ⟨?_, ?_, fun r h₁ h₂ => ?_, rfl, rfl, rfl, rfl⟩
  · simp [gpr_write, State.read]
  · simp [gpr_write, State.read]
  · simp [gpr_write, h₁, h₂]

theorem x1_ofNat (s₀ : State) : s₀.gpr .x1 = BitVec.ofNat 64 (VG.Proof.CmacAes.AArch64.R s₀) := by
  apply BitVec.eq_of_toNat_eq; simp [VG.Proof.CmacAes.AArch64.R]

theorem take_succ_blks (s₀ : State) {k : Nat} (hk : k < VG.Proof.CmacAes.AArch64.N s₀) :
    (VG.Proof.CmacAes.AArch64.blks s₀).take (k + 1) =
      (VG.Proof.CmacAes.AArch64.blks s₀).take k ++ [Spec.Aes.bytesAt s₀.mem (VG.Proof.CmacAes.AArch64.Dp s₀ + BitVec.ofNat 64 (16 * k)) 16] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simp [Spec.Cmac.blocksAt]; omega)]
  simp [Spec.Cmac.blocksAt]

theorem in_rw {rs : List Region} {r : Region} (hr : r ∈ rs) {a : Addr} {n : Nat} (hc : r.Contains a n) :
    InRegions rs a n := ⟨r, hr, hc⟩

/-! ## Memory outside the writable regions -/

/-- The regions the function writes. -/
abbrev Big (s₀ : State) : List Region := [VG.Proof.CmacAes.AArch64.stR s₀, VG.Proof.CmacAes.AArch64.scrR s₀]

section
variable {s₀ : State} (hp : VG.Proof.CmacAes.AArch64.UPre s₀)
include hp

theorem UPre.sched_bytes {m : Mem} (hf : Frame (VG.Proof.CmacAes.AArch64.Big s₀) s₀.mem m) :
    Spec.Aes.bytesAt m (VG.Proof.CmacAes.AArch64.W s₀) (16 * (VG.Proof.CmacAes.AArch64.R s₀ + 1)) = Spec.Aes.bytesAt s₀.mem (VG.Proof.CmacAes.AArch64.W s₀) (16 * (VG.Proof.CmacAes.AArch64.R s₀ + 1)) := by
  have hR : 16 * (VG.Proof.CmacAes.AArch64.R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega
  refine Proof.Cmac.bytesAt_frame hf (fun r hr => ?_) (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.sch_st.sub_left (Region.sub_prefix hR)
  · exact hp.sch_scr.sub_left (Region.sub_prefix hR)

theorem UPre.block_bytes {m : Mem} (hf : Frame (VG.Proof.CmacAes.AArch64.Big s₀) s₀.mem m) {k : Nat} (hk : k < VG.Proof.CmacAes.AArch64.N s₀) :
    Spec.Aes.bytesAt m (VG.Proof.CmacAes.AArch64.Dp s₀ + BitVec.ofNat 64 (16 * k)) 16 =
      Spec.Aes.bytesAt s₀.mem (VG.Proof.CmacAes.AArch64.Dp s₀ + BitVec.ofNat 64 (16 * k)) 16 := by
  refine Proof.Cmac.bytesAt_frame hf (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.data_st.sub_left (UPre.data_sub hk)
  · exact hp.data_scr.sub_left (UPre.data_sub hk)

omit hp in
theorem UPre.big_of {m : Mem} (hf : Frame [VG.Proof.CmacAes.AArch64.stR s₀, ⟨VG.Proof.CmacAes.AArch64.S s₀, 2064⟩] (VG.Proof.CmacAes.AArch64.savedMem s₀) m) :
    Frame (VG.Proof.CmacAes.AArch64.Big s₀) s₀.mem m := by
  have f₀ : Frame (VG.Proof.CmacAes.AArch64.Big s₀) s₀.mem (VG.Proof.CmacAes.AArch64.savedMem s₀) :=
    (VG.Proof.CmacAes.AArch64.savedMem_frame s₀).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.CmacAes.AArch64.scrR s₀, by simp, UPre.scr_sub (by decide)⟩
  exact f₀.trans (hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨VG.Proof.CmacAes.AArch64.stR s₀, by simp, fun _ h => h⟩
    · exact ⟨VG.Proof.CmacAes.AArch64.scrR s₀, by simp, Region.sub_prefix (by decide)⟩)

end

/-! ## One block -/

/-- What the code before the call leaves. -/
structure BodyA (s₀ : State) (k : Nat) (s s₁ : State) : Prop where
  pre : VG.Proof.CmacAes.AArch64.CallPre s₁ (VG.Proof.CmacAes.AArch64.W s₀) (VG.Proof.CmacAes.AArch64.S s₀ + BitVec.ofNat 64 2048) (VG.Proof.CmacAes.AArch64.St s₀) (VG.Proof.CmacAes.AArch64.S s₀) (VG.Proof.CmacAes.AArch64.R s₀)
  saved : ∀ r ∈ preserved, s₁.gpr r = s.gpr r
  sp : s₁.sp = s.sp
  mem : s₁.mem = Proof.Cmac.chainMem s.mem (VG.Proof.CmacAes.AArch64.S s₀ + BitVec.ofNat 64 2048) (VG.Proof.CmacAes.AArch64.St s₀) (VG.Proof.CmacAes.AArch64.Dp s₀ + BitVec.ofNat 64 (16 * k))
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

theorem bodyA_wp {s₀ : State} (hp : VG.Proof.CmacAes.AArch64.UPre s₀) {k : Nat} (hk : k < VG.Proof.CmacAes.AArch64.N s₀) {s : State} (h : VG.Proof.CmacAes.AArch64.LInv s₀ k s) :
    WP isa (.block (chainIn ++ updArgs)) s (VG.Proof.CmacAes.AArch64.BodyA s₀ k s) := by
  have hRegs : s.rd ++ s.wr = [VG.Proof.CmacAes.AArch64.schR s₀, VG.Proof.CmacAes.AArch64.dataR s₀, VG.Proof.CmacAes.AArch64.stR s₀, VG.Proof.CmacAes.AArch64.scrR s₀] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have hW : s.wr = [VG.Proof.CmacAes.AArch64.stR s₀, VG.Proof.CmacAes.AArch64.scrR s₀] := by rw [h.wr, hp.wr]
  have h16k : 16 * k + 16 ≤ 16 * VG.Proof.CmacAes.AArch64.N s₀ := by omega
  have hdw := hp.data_wrap
  have cSt0 : (VG.Proof.CmacAes.AArch64.stR s₀).Contains (VG.Proof.CmacAes.AArch64.St s₀) 8 := by
    simpa using Offset.contains_base (VG.Proof.CmacAes.AArch64.St s₀) (d := 0) (n := 8) (k := 16) (by decide) (by decide)
  have cSt8 : (VG.Proof.CmacAes.AArch64.stR s₀).Contains (VG.Proof.CmacAes.AArch64.St s₀ + BitVec.ofNat 64 8) 8 := Offset.contains_base _ (by decide) (by decide)
  have cQ0 : (VG.Proof.CmacAes.AArch64.dataR s₀).Contains (VG.Proof.CmacAes.AArch64.Dp s₀ + BitVec.ofNat 64 (16 * k)) 8 :=
    Offset.contains_base _ (by omega) (by omega)
  have cQ8 : (VG.Proof.CmacAes.AArch64.dataR s₀).Contains (VG.Proof.CmacAes.AArch64.Dp s₀ + BitVec.ofNat 64 (16 * k) + BitVec.ofNat 64 8) 8 := by
    rw [Offset.add_add]; exact Offset.contains_base _ (by omega) (by omega)
  have cC0 : (VG.Proof.CmacAes.AArch64.scrR s₀).Contains (VG.Proof.CmacAes.AArch64.S s₀ + BitVec.ofNat 64 2048) 8 := Offset.contains_base _ (by decide) (by decide)
  have cC8 : (VG.Proof.CmacAes.AArch64.scrR s₀).Contains (VG.Proof.CmacAes.AArch64.S s₀ + BitVec.ofNat 64 2048 + BitVec.ofNat 64 8) 8 := by
    rw [Offset.add_add]; exact Offset.contains_base _ (by decide) (by decide)
  obtain ⟨s₁, run₁, x0₁, x1₁, x2₁, x3₁, x4₁, x5₁, cs₁, sp₁, mem₁, rd₁, wr₁⟩ :=
    VG.Proof.CmacAes.AArch64.chainIn_ok s (C := VG.Proof.CmacAes.AArch64.S s₀ + BitVec.ofNat 64 2048) (P := VG.Proof.CmacAes.AArch64.St s₀) (Q := VG.Proof.CmacAes.AArch64.Dp s₀ + BitVec.ofNat 64 (16 * k))
      (by rw [h.x24]) h.x21 h.x22
      (by rw [hRegs]; exact VG.Proof.CmacAes.AArch64.in_rw (by simp) cSt0) (by rw [hRegs]; exact VG.Proof.CmacAes.AArch64.in_rw (by simp) cSt8)
      (by rw [hRegs]; exact VG.Proof.CmacAes.AArch64.in_rw (by simp) cQ0) (by rw [hRegs]; exact VG.Proof.CmacAes.AArch64.in_rw (by simp) cQ8)
      (by rw [hW]; exact VG.Proof.CmacAes.AArch64.in_rw (by simp) cC0) (by rw [hW]; exact VG.Proof.CmacAes.AArch64.in_rw (by simp) cC8)
      (by rw [hW]; exact VG.Proof.CmacAes.AArch64.in_rw (by simp) cSt0) (by rw [hW]; exact VG.Proof.CmacAes.AArch64.in_rw (by simp) cSt8)
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have cDis : (⟨VG.Proof.CmacAes.AArch64.S s₀ + BitVec.ofNat 64 2048, 16⟩ : Region).Disjoint ⟨VG.Proof.CmacAes.AArch64.S s₀, 2048⟩ :=
    Offset.disjoint_base _ (by decide) (by have := hp.scr_wrap; omega)
  have pre : VG.Proof.CmacAes.AArch64.CallPre s₁ (VG.Proof.CmacAes.AArch64.W s₀) (VG.Proof.CmacAes.AArch64.S s₀ + BitVec.ofNat 64 2048) (VG.Proof.CmacAes.AArch64.St s₀) (VG.Proof.CmacAes.AArch64.S s₀) (VG.Proof.CmacAes.AArch64.R s₀) :=
    { x0 := by rw [x0₁, h.x19]
      x1 := by rw [x1₁, h.x20, VG.Proof.CmacAes.AArch64.x1_ofNat]
      x2 := x2₁
      x3 := x3₁
      x4 := x4₁
      x5 := by rw [x5₁, h.x24]
      rounds := hp.rounds
      wc := hp.sch_scr.sub_right (UPre.scr_sub (by decide))
      wd := hp.sch_st
      ws := hp.sch_scr.sub_right (Region.sub_prefix (by decide))
      cd := hp.st_scr.symm.sub_left (UPre.scr_sub (by decide))
      cs := cDis
      ds := hp.st_scr.sub_right (Region.sub_prefix (by decide))
      wrap := hp.st_wrap
      reads := by
        rw [rd₁, wr₁, hRegs]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact ⟨VG.Proof.CmacAes.AArch64.schR s₀, by simp, 0, by simp, by simp⟩
        · exact ⟨VG.Proof.CmacAes.AArch64.scrR s₀, by simp, 2048, rfl, by simp⟩
        · exact ⟨VG.Proof.CmacAes.AArch64.stR s₀, by simp, 0, by simp, by simp⟩
        · exact ⟨VG.Proof.CmacAes.AArch64.scrR s₀, by simp, 0, by simp, by simp⟩
      writes := by
        rw [wr₁, hW]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨VG.Proof.CmacAes.AArch64.scrR s₀, by simp, 2048, rfl, by simp⟩
        · exact ⟨VG.Proof.CmacAes.AArch64.stR s₀, by simp, 0, by simp, by simp⟩
        · exact ⟨VG.Proof.CmacAes.AArch64.scrR s₀, by simp, 0, by simp, by simp⟩
      zero := by rw [mem₁]; exact Proof.Cmac.chainMem_state _ _ _ _ }
  exact ⟨pre, cs₁, sp₁, mem₁, rd₁, wr₁⟩

theorem body_ok (v : Ctr32Impl) {s₀ : State} (hp : VG.Proof.CmacAes.AArch64.UPre s₀) {k : Nat} (hk : k < VG.Proof.CmacAes.AArch64.N s₀) {s : State}
    (h : VG.Proof.CmacAes.AArch64.LInv s₀ k s) :
    WP isa (VG.Impl.CmacAes.AArch64.body v.callee) s fun s' => VG.Proof.CmacAes.AArch64.LInv s₀ (k + 1) s' := by
  have h16k : 16 * k + 16 ≤ 16 * VG.Proof.CmacAes.AArch64.N s₀ := by omega
  have hdw := hp.data_wrap
  refine WP.seq (WP.mono (VG.Proof.CmacAes.AArch64.bodyA_wp hp hk h) fun s₁ ⟨pre, cs₁, sp₁, mem₁, rd₁, wr₁⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.CmacAes.AArch64.ctr_call v pre) fun s₂ h₂ => ?_)
  obtain ⟨s₃, run₃, x22₃, x23₃, keep₃, sp₃, mem₃, rd₃, wr₃⟩ := VG.Proof.CmacAes.AArch64.advance_ok s₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have g (r : Reg) (hr : r ∈ preserved) (h30 : r ≠ .x30) (h22 : r ≠ .x22) (h23 : r ≠ .x23) :
      s₃.gpr r = s.gpr r := by
    rw [keep₃ r h22 h23, h₂.saved r hr h30, cs₁ r hr]
  have x22₂ : s₂.gpr .x22 = VG.Proof.CmacAes.AArch64.Dp s₀ + BitVec.ofNat 64 (16 * k) := by
    rw [h₂.saved .x22 (by simp [preserved]) (by decide), cs₁ .x22 (by simp [preserved]), h.x22]
  have x23₂ : s₂.gpr .x23 = BitVec.ofNat 64 (VG.Proof.CmacAes.AArch64.N s₀ - k) := by
    rw [h₂.saved .x23 (by simp [preserved]) (by decide), cs₁ .x23 (by simp [preserved]), h.x23]
  have hN := (s₀.gpr .x4).isLt
  have dec : BitVec.ofNat 64 (VG.Proof.CmacAes.AArch64.N s₀ - k) - 1 = BitVec.ofNat 64 (VG.Proof.CmacAes.AArch64.N s₀ - (k + 1)) := by
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega)]; rfl
  -- Memory.
  have bigS := UPre.big_of h.frame
  have f₁ : Frame [⟨VG.Proof.CmacAes.AArch64.S s₀ + BitVec.ofNat 64 2048, 16⟩, ⟨VG.Proof.CmacAes.AArch64.St s₀, 16⟩] s.mem s₁.mem := by
    rw [mem₁]; exact Proof.Cmac.chainMem_frame _ _ _ _
  have big₁ : Frame (VG.Proof.CmacAes.AArch64.Big s₀) s₀.mem s₁.mem := bigS.trans (f₁.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨VG.Proof.CmacAes.AArch64.scrR s₀, by simp, UPre.scr_sub (by decide)⟩
    · exact ⟨VG.Proof.CmacAes.AArch64.stR s₀, by simp, fun _ h => h⟩)
  have cst : (⟨VG.Proof.CmacAes.AArch64.S s₀ + BitVec.ofNat 64 2048, 16⟩ : Region).Disjoint (VG.Proof.CmacAes.AArch64.stR s₀) :=
    hp.st_scr.symm.sub_left (UPre.scr_sub (by decide))
  have cq : (⟨VG.Proof.CmacAes.AArch64.S s₀ + BitVec.ofNat 64 2048, 16⟩ : Region).Disjoint ⟨VG.Proof.CmacAes.AArch64.Dp s₀ + BitVec.ofNat 64 (16 * k), 16⟩ :=
    (hp.data_scr.symm.sub_left (UPre.scr_sub (by decide))).sub_right (UPre.data_sub hk)
  have out := h₂.out
  rw [UPre.sched_bytes hp big₁, mem₁, Proof.Cmac.chainMem_counter _ cst cq, h.state,
    UPre.block_bytes hp bigS hk] at out
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g .x19 (by simp [preserved]) (by decide) (by decide) (by decide), h.x19]
  · rw [g .x20 (by simp [preserved]) (by decide) (by decide) (by decide), h.x20]
  · rw [g .x21 (by simp [preserved]) (by decide) (by decide) (by decide), h.x21]
  · rw [x22₃, x22₂, Offset.add_add_eq _ (c := 16 * (k + 1)) (by omega)]
  · rw [x23₃, x23₂, dec]
  · rw [g .x24 (by simp [preserved]) (by decide) (by decide) (by decide), h.x24]
  · intro r hr h19 h20 h21 h22 h23 h24 h30
    rw [g r hr h30 h22 h23, h.other r hr h19 h20 h21 h22 h23 h24 h30]
  · rw [sp₃, h₂.sp, sp₁, h.sp]
  · rw [rd₃, h₂.rd, rd₁, h.rd]
  · rw [wr₃, h₂.wr, wr₁, h.wr]
  · rw [mem₃]
    refine h.frame.trans ((f₁.sub fun r hr => ?_).trans (h₂.frame.sub fun r hr => ?_))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨VG.Proof.CmacAes.AArch64.S s₀, 2064⟩, by simp, Offset.sub_base _ (by decide)⟩
      · exact ⟨VG.Proof.CmacAes.AArch64.stR s₀, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨⟨VG.Proof.CmacAes.AArch64.S s₀, 2064⟩, by simp, Offset.sub_base _ (by decide)⟩
      · exact ⟨VG.Proof.CmacAes.AArch64.stR s₀, by simp, fun _ h => h⟩
      · exact ⟨⟨VG.Proof.CmacAes.AArch64.S s₀, 2064⟩, by simp, Region.sub_prefix (by decide)⟩
  · rw [mem₃, out, VG.Proof.CmacAes.AArch64.take_succ_blks s₀ hk, Proof.Cmac.chain_append, Proof.Cmac.chain_single]

end VG.Proof.CmacAes.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.AArch64.UpdateCorrect`. -/
section

/-!
# AES-CMAC on AArch64: `vg_cmac_aes_update` is correct
-/

namespace VG.Proof.CmacAes.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.CmacAes.AArch64
open VG.Proof.Aes.AArch64 (Ctr32Impl)

theorem ofNat_ne_zero {x : Nat} (hx : x < 2 ^ 64) : (BitVec.ofNat 64 x != 0) = !decide (x = 0) := by
  have : (BitVec.ofNat 64 x == 0) = decide (x = 0) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    constructor
    · intro he
      have := congrArg BitVec.toNat he
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx] at this
      simpa using this
    · intro he; rw [he]; rfl
  rw [bne, this]

theorem eval_x23 {s : State} {x : Nat} (hx : x < 2 ^ 64) (h : s.gpr .x23 = BitVec.ofNat 64 x) :
    isa.eval (.nonzero .x .x23) s = some !decide (x = 0) := by
  show some (s.read .x .x23 != 0) = _
  rw [State.read, h, BitVec.setWidth_eq, VG.Proof.CmacAes.AArch64.ofNat_ne_zero hx]

theorem eval_zero_x23 {s : State} {x : Nat} (hx : x < 2 ^ 64) (h : s.gpr .x23 = BitVec.ofNat 64 x) :
    isa.eval (.zero .x .x23) s = some (decide (x = 0)) := by
  show some (s.read .x .x23 == 0) = _
  rw [State.read, h, BitVec.setWidth_eq]
  have := VG.Proof.CmacAes.AArch64.ofNat_ne_zero hx
  rw [bne] at this
  cases hb : (BitVec.ofNat 64 x == 0) <;> rw [hb] at this <;> cases hd : decide (x = 0) <;> simp_all

theorem loop_ok (v : Ctr32Impl) {s₀ : State} (hp : VG.Proof.CmacAes.AArch64.UPre s₀) {k : Nat} (hk : k < VG.Proof.CmacAes.AArch64.N s₀) {s : State}
    (h : VG.Proof.CmacAes.AArch64.LInv s₀ k s) : WP isa (.loop (VG.Impl.CmacAes.AArch64.body v.callee) (.nonzero .x .x23)) s (VG.Proof.CmacAes.AArch64.LInv s₀ (VG.Proof.CmacAes.AArch64.N s₀)) := by
  refine WP.loop (M := isa) (body := VG.Impl.CmacAes.AArch64.body v.callee) (c := .nonzero .x .x23) (Q := VG.Proof.CmacAes.AArch64.LInv s₀ (VG.Proof.CmacAes.AArch64.N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = VG.Proof.CmacAes.AArch64.N s₀ - j ∧ j < VG.Proof.CmacAes.AArch64.N s₀ ∧ VG.Proof.CmacAes.AArch64.LInv s₀ j t) ?_ (VG.Proof.CmacAes.AArch64.N s₀ - k) s
    ⟨k, rfl, hk, h⟩
  rintro n s ⟨k, rfl, hk, h⟩
  refine WP.mono (VG.Proof.CmacAes.AArch64.body_ok v hp hk h) fun s' h' => ?_
  have hN : VG.Proof.CmacAes.AArch64.N s₀ < 2 ^ 64 := (s₀.gpr .x4).isLt
  have ev := VG.Proof.CmacAes.AArch64.eval_x23 (x := VG.Proof.CmacAes.AArch64.N s₀ - (k + 1)) (by omega) h'.x23
  by_cases hz : VG.Proof.CmacAes.AArch64.N s₀ - (k + 1) = 0
  · left
    refine ⟨by rw [ev]; simp [hz], ?_⟩
    rwa [show VG.Proof.CmacAes.AArch64.N s₀ = k + 1 by omega]
  · right
    refine ⟨by rw [ev]; simp [hz], VG.Proof.CmacAes.AArch64.N s₀ - (k + 1), by omega, k + 1, rfl, by omega, h'⟩

/-! ## Saving and restoring the registers -/

theorem readW_writeW_other (m : Mem) (b : Addr) {d e : Nat} (v : BitVec 64) (h : d + 8 ≤ e ∨ e + 8 ≤ d)
    (hd : d + 8 ≤ 2 ^ 64) (he : e + 8 ≤ 2 ^ 64) :
    (m.writeW (b + BitVec.ofNat 64 e) v).readW (b + BitVec.ofNat 64 d) 64 = m.readW (b + BitVec.ofNat 64 d) 64 :=
  Mem.readW_writeW_sep (Offset.sep b h hd he) (by decide)

/-- Each slot holds the register saved there. -/
theorem savedMem_slot (s : State) {r : Reg} {d : Nat} (h : (r, d) ∈ saved) :
    (VG.Proof.CmacAes.AArch64.savedMem s).readW (s.gpr .x5 + BitVec.ofNat 64 d) 64 = s.gpr r := by
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  simp only [VG.Proof.CmacAes.AArch64.savedMem, saved, List.foldl]
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  repeat (first
    | rw [Mem.readW_writeW_self64]
    | rw [VG.Proof.CmacAes.AArch64.readW_writeW_other _ _ _ (by decide) (by decide) (by decide)])

theorem restore_ok (s : State) {B : Addr} (hb : s.gpr .x24 = B)
    (hr : ∀ d, 2064 ≤ d → d + 8 ≤ 2120 → InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa restore s = some s' ∧
      (∀ r d, (r, d) ∈ saved → s'.gpr r = s.mem.readW (B + BitVec.ofNat 64 d) 64) ∧
      (∀ r, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x22 → r ≠ .x23 → r ≠ .x30 → r ≠ .x24 →
        s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul, Nat.reduceMod, and_self, restore, saved, List.map, runBlock_cons, runStep_some,
      runBlock_nil, exec, addr, State.load, Size.bytes, Size.bits, gpr_write, mem_write, rd_write,
      wr_write, Option.bind_some, Option.map_some, hb,
      hr 2064 (by decide) (by decide), hr 2072 (by decide) (by decide), hr 2080 (by decide) (by decide),
      hr 2088 (by decide) (by decide), hr 2096 (by decide) (by decide), hr 2104 (by decide) (by decide),
      hr 2112 (by decide) (by decide)]
    rfl, ?_⟩
  refine ⟨fun r d h => ?_, fun r h₁ h₂ h₃ h₄ h₅ h₆ h₇ => ?_, rfl, rfl⟩
  · simp only [saved, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [gpr_write, Mem.readW]
  · simp [gpr_write, h₁, h₂, h₃, h₄, h₅, h₆, h₇]

/-! ## The whole function -/

theorem x4_ofNat (s₀ : State) : s₀.gpr .x4 = BitVec.ofNat 64 (VG.Proof.CmacAes.AArch64.N s₀) := by
  apply BitVec.eq_of_toNat_eq; simp [VG.Proof.CmacAes.AArch64.N]

theorem slots_disj {s₀ : State} (hp : VG.Proof.CmacAes.AArch64.UPre s₀) :
    ∀ r ∈ [VG.Proof.CmacAes.AArch64.stR s₀, ⟨VG.Proof.CmacAes.AArch64.S s₀, 2064⟩], (⟨VG.Proof.CmacAes.AArch64.S s₀ + BitVec.ofNat 64 2064, 56⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.st_scr.symm.sub_left (UPre.scr_sub (by decide))
  · exact Offset.disjoint_base _ (by decide) (by have := hp.scr_wrap; omega)

theorem slot_read {s₀ : State} (hp : VG.Proof.CmacAes.AArch64.UPre s₀) {m : Mem}
    (hf : Frame [VG.Proof.CmacAes.AArch64.stR s₀, ⟨VG.Proof.CmacAes.AArch64.S s₀, 2064⟩] (VG.Proof.CmacAes.AArch64.savedMem s₀) m) {d : Nat} (h₁ : 2064 ≤ d) (h₂ : d + 8 ≤ 2120) :
    m.readW (VG.Proof.CmacAes.AArch64.S s₀ + BitVec.ofNat 64 d) 64 = (VG.Proof.CmacAes.AArch64.savedMem s₀).readW (VG.Proof.CmacAes.AArch64.S s₀ + BitVec.ofNat 64 d) 64 :=
  hf.readW (r := ⟨VG.Proof.CmacAes.AArch64.S s₀ + BitVec.ofNat 64 2064, 56⟩) (VG.Proof.CmacAes.AArch64.slot_contains _ h₁ h₂) (VG.Proof.CmacAes.AArch64.slots_disj hp) (by decide)

theorem prologue_wp {s₀ : State} (hp : VG.Proof.CmacAes.AArch64.UPre s₀) :
    WP isa (.block (save ++ setup)) s₀ fun s₁ => VG.Proof.CmacAes.AArch64.LInv s₀ 0 s₁ := by
  obtain ⟨s₁, run₁, x19₁, x20₁, x21₁, x22₁, x23₁, x24₁, keep₁, sp₁, mem₁, rd₁, wr₁⟩ :=
    VG.Proof.CmacAes.AArch64.prologue_ok s₀ fun d _ h₂ => by
      rw [hp.wr]; exact VG.Proof.CmacAes.AArch64.in_rw (r := VG.Proof.CmacAes.AArch64.scrR s₀) (by simp) (Offset.contains_base _ (by omega) (by omega))
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have stSaved : Spec.Aes.bytesAt (VG.Proof.CmacAes.AArch64.savedMem s₀) (VG.Proof.CmacAes.AArch64.St s₀) 16 = Spec.Aes.bytesAt s₀.mem (VG.Proof.CmacAes.AArch64.St s₀) 16 :=
    Proof.Cmac.bytesAt_frame16 (VG.Proof.CmacAes.AArch64.savedMem_frame s₀) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_scr.sub_right (UPre.scr_sub (by decide))
  exact { x19 := x19₁, x20 := x20₁, x21 := x21₁
          x22 := by rw [x22₁]; simp
          x23 := by rw [x23₁, VG.Proof.CmacAes.AArch64.x4_ofNat]; rfl
          x24 := x24₁
          other := fun r _ h19 h20 h21 h22 h23 h24 _ => keep₁ r h19 h20 h21 h22 h23 h24
          sp := sp₁, rd := rd₁, wr := wr₁
          frame := by rw [mem₁]; exact Frame.refl _ _
          state := by rw [mem₁, stSaved]; rfl }

theorem mid_wp (v : Ctr32Impl) {s₀ : State} (hp : VG.Proof.CmacAes.AArch64.UPre s₀) {s₁ : State} (h : VG.Proof.CmacAes.AArch64.LInv s₀ 0 s₁) :
    WP isa (.ite (.zero .x .x23) (.block []) (.loop (VG.Impl.CmacAes.AArch64.body v.callee) (.nonzero .x .x23))) s₁
      (VG.Proof.CmacAes.AArch64.LInv s₀ (VG.Proof.CmacAes.AArch64.N s₀)) := by
  have hN := (s₀.gpr .x4).isLt
  have ev := VG.Proof.CmacAes.AArch64.eval_zero_x23 (x := VG.Proof.CmacAes.AArch64.N s₀) hN (by rw [h.x23]; rfl)
  by_cases hn : VG.Proof.CmacAes.AArch64.N s₀ = 0
  · refine WP.ite true (by rw [ev]; simp [hn]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    rw [hn]; exact h
  · refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
    exact VG.Proof.CmacAes.AArch64.loop_ok v hp (by omega) h

theorem epilogue_wp {s₀ : State} (hp : VG.Proof.CmacAes.AArch64.UPre s₀) {s₂ : State} (h₂ : VG.Proof.CmacAes.AArch64.LInv s₀ (VG.Proof.CmacAes.AArch64.N s₀) s₂) :
    WP isa (.block restore) s₂ fun s' => GprAbi s₀ s' ∧ updateAArch64.post s₀ s' := by
  have rdwr : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [h₂.rd, h₂.wr]
  obtain ⟨s₃, run₃, slot₃, keep₃, sp₃, mem₃⟩ :=
    VG.Proof.CmacAes.AArch64.restore_ok s₂ h₂.x24 fun d _ h₂' => by
      rw [rdwr, hp.rd, hp.wr]
      exact VG.Proof.CmacAes.AArch64.in_rw (r := VG.Proof.CmacAes.AArch64.scrR s₀) (by simp) (Offset.contains_base _ (by omega) (by have := hp.scr_wrap; omega))
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have sl {r : Reg} {d : Nat} (h : (r, d) ∈ saved) : s₃.gpr r = s₀.gpr r := by
    have hd : 2064 ≤ d ∧ d + 8 ≤ 2120 := by
      simp only [saved, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
      omega
    rw [slot₃ r d h, VG.Proof.CmacAes.AArch64.slot_read hp h₂.frame hd.1 hd.2, VG.Proof.CmacAes.AArch64.savedMem_slot s₀ h]
  refine ⟨⟨fun r hr => ?_, by rw [sp₃, h₂.sp]⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact sl (d := 2064) (by simp [saved])
    · exact sl (d := 2072) (by simp [saved])
    · exact sl (d := 2080) (by simp [saved])
    · exact sl (d := 2088) (by simp [saved])
    · exact sl (d := 2096) (by simp [saved])
    · exact sl (d := 2112) (by simp [saved])
    · rw [keep₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact h₂.other _ (by simp [preserved]) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    · rw [keep₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact h₂.other _ (by simp [preserved]) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    · rw [keep₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact h₂.other _ (by simp [preserved]) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    · rw [keep₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact h₂.other _ (by simp [preserved]) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    · exact sl (d := 2104) (by simp [saved])
  · show Spec.Aes.bytesAt s₃.mem (VG.Proof.CmacAes.AArch64.St s₀) 16 = Spec.Cmac.chain (VG.Proof.CmacAes.AArch64.ciph s₀) _ (VG.Proof.CmacAes.AArch64.blks s₀)
    rw [mem₃, h₂.state, List.take_of_length_le (by simp [Spec.Cmac.blocksAt])]

theorem update_wp (v : Ctr32Impl) {s₀ : State} (h0 : updateAArch64.pre s₀) :
    WP isa (update v.callee) s₀ fun s' => GprAbi s₀ s' ∧ updateAArch64.post s₀ s' := by
  have hp := UPre.of h0
  exact WP.seq (WP.mono (VG.Proof.CmacAes.AArch64.prologue_wp hp) fun s₁ h₁ =>
    WP.seq (WP.mono (VG.Proof.CmacAes.AArch64.mid_wp v hp h₁) fun _ h₂ => VG.Proof.CmacAes.AArch64.epilogue_wp hp h₂))

end VG.Proof.CmacAes.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.AArch64.Subkeys`. -/
section

section

/-!
# AES-CMAC on AArch64: doubling a block in two 64-bit words

`subkeys` loads a block as two byte-reversed words (`rev`), the high and low
halves of the block as a big-endian integer (`Proof.Gcm.AArch64.blockAt_rev`),
doubles the integer a word at a time (`dbl_words`), and stores the halves
byte-reversed again (`le8_rev`).
-/

namespace VG.Proof.CmacAes.AArch64

open VG VG.AArch64 Proof.Cmac

theorem getD_le8_append (a b : BitVec 64) {k : Nat} (hk : k < 16) :
    (le8 a ++ le8 b).getD k 0 = if k < 8 then a.extractLsb' (8 * k) 8 else b.extractLsb' (8 * (k - 8)) 8 := by
  rw [List.getD_eq_getElem?_getD]
  split
  · rw [List.getElem?_append_left (by rw [length_le8]; omega), ← List.getD_eq_getElem?_getD, getD_le8 _ ‹_›]
  · rw [List.getElem?_append_right (by rw [length_le8]; omega), length_le8, ← List.getD_eq_getElem?_getD,
      getD_le8 _ (by omega)]

theorem getLsbD_rev64 (x : BitVec 64) {p : Nat} (hp : p < 64) :
    (rev64 x).getLsbD p = x.getLsbD (8 * (7 - p / 8) + p % 8) :=
  Proof.Gcm.getLsbD_byteRev64 x p hp

/-- Storing the byte-reversed halves of `h ++ l` stores its bytes, big-endian. -/
theorem le8_rev (h l : BitVec 64) :
    le8 (rev64 h) ++ le8 (rev64 l) = Spec.Gcm.toBytes (h ++ l) := by
  refine ext16 (by simp [length_le8]) (toBytes_length _) fun k hk => ?_
  rw [Proof.Aes.toBytes_getD _ hk]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  simp only [hj, decide_true, Bool.true_and]
  rcases Nat.lt_or_ge k 8 with h8 | h8
  · rw [VG.Proof.CmacAes.AArch64.getD_le8_append _ _ hk]
    simp only [h8, ↓reduceIte]
    rw [BitVec.getLsbD_extractLsb', VG.Proof.CmacAes.AArch64.getLsbD_rev64 _ (by omega)]
    simp only [hj, decide_true, Bool.true_and, show ¬ 8 * (15 - k) + j < 64 by omega, ite_false]
    congr 1; omega
  · rw [VG.Proof.CmacAes.AArch64.getD_le8_append _ _ hk]
    simp only [show ¬ k < 8 by omega, ↓reduceIte]
    rw [BitVec.getLsbD_extractLsb', VG.Proof.CmacAes.AArch64.getLsbD_rev64 _ (by omega)]
    simp only [hj, decide_true, Bool.true_and, show 8 * (15 - k) + j < 64 by omega, ite_true]
    congr 1; omega

theorem mask_eq (hi : BitVec 64) :
    ((0 : BitVec 64) - (hi >>> 63)) &&& 0x87 = if hi.msb then 0x87 else 0 := by
  have h : hi >>> 63 = if hi.msb then 1 else 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.msb_eq_decide]
    have := hi.isLt
    by_cases hm : 2 ^ (64 - 1) ≤ hi.toNat
    · rw [decide_eq_true hm]; simp; omega
    · rw [decide_eq_false hm]; simp; omega
  rw [h]
  split <;> decide

theorem bit135 : ∀ p < 64, (135 : BitVec 64).getLsbD p = (135 : BitVec 128).getLsbD p := by decide

/-- The words `subkeys` stores, from the halves `hi` and `lo` it loads. -/
def dblHi (hi lo : BitVec 64) : BitVec 64 := (hi <<< 1) ||| (lo >>> 63)
def dblLo (hi lo : BitVec 64) : BitVec 64 := (lo <<< 1) ^^^ (((0 : BitVec 64) - (hi >>> 63)) &&& 0x87)

/-- `subkeys`' doubling of `hi ++ lo`. -/
theorem dbl_words (hi lo : BitVec 64) : VG.Proof.CmacAes.AArch64.dblHi hi lo ++ VG.Proof.CmacAes.AArch64.dblLo hi lo = dbl128 (hi ++ lo) := by
  rw [VG.Proof.CmacAes.AArch64.dblHi, VG.Proof.CmacAes.AArch64.dblLo, VG.Proof.CmacAes.AArch64.mask_eq, dbl128, BitVec.msb_append]
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  rw [BitVec.getLsbD_append]
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append, hp, decide_true, Bool.true_and]
  have h0 : ((64 : Nat) = 0) = False := by simp
  simp only [h0, ite_false]
  by_cases h64 : p < 64
  · simp only [h64, ↓reduceIte, show p - 1 < 64 by omega, decide_true, Bool.true_and]
    congr 1
    split
    · exact VG.Proof.CmacAes.AArch64.bit135 p h64
    · simp
  · have hm : (if hi.msb = true then (135 : BitVec 128) else 0).getLsbD p = false := by
      split
      · exact Proof.Cmac.high_0x87 (by omega)
      · simp
    rw [hm, Bool.xor_false]
    simp only [h64, ↓reduceIte, show p - 64 < 64 by omega, decide_true, Bool.true_and]
    rcases Nat.eq_or_lt_of_le (show 64 ≤ p by omega) with rfl | hlt
    · simp
    · rw [BitVec.getLsbD_of_ge lo (63 + (p - 64)) (by omega)]
      simp [show ¬ p - 64 < 1 by omega, show ¬ p < 1 by omega, show ¬ p - 1 < 64 by omega]
      congr 1

end VG.Proof.CmacAes.AArch64

end

/-!
# AES-CMAC on AArch64: `vg_cmac_aes_subkeys`
-/

namespace VG.Proof.CmacAes.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.CmacAes.AArch64
open VG.Proof.Aes.AArch64 (Ctr32Impl)

/-! ## Doubling a block -/

/-- The memory after `dbl src dst`, from `x19 = K`. -/
def dblMem (m : Mem) (K : Addr) (src dst : Nat) : Mem :=
  let hi := rev64 (m.readW (K + BitVec.ofNat 64 src) 64)
  let lo := rev64 (m.readW (K + BitVec.ofNat 64 (src + 8)) 64)
  (m.writeW (K + BitVec.ofNat 64 dst) (rev64 (VG.Proof.CmacAes.AArch64.dblHi hi lo))).writeW (K + BitVec.ofNat 64 (dst + 8))
    (rev64 (VG.Proof.CmacAes.AArch64.dblLo hi lo))

theorem mz0 : BitVec.setWidth 64 (0 : BitVec 16) <<< (16 * 0) = 0 := by decide
theorem mz87 : BitVec.setWidth 64 (135 : BitVec 16) <<< (16 * 0) = 0x87 := by decide

theorem dbl_ok (s : State) {K : Addr} (hb : s.gpr .x19 = K) {src dst : Nat}
    (hs : src % 8 = 0 ∧ src + 8 < 32768) (hd : dst % 8 = 0 ∧ dst + 8 < 32768)
    (r₀ : InRegions (s.rd ++ s.wr) (K + BitVec.ofNat 64 src) 8)
    (r₁ : InRegions (s.rd ++ s.wr) (K + BitVec.ofNat 64 (src + 8)) 8)
    (w₀ : InRegions s.wr (K + BitVec.ofNat 64 dst) 8) (w₁ : InRegions s.wr (K + BitVec.ofNat 64 (dst + 8)) 8) :
    ∃ s', runBlock isa (dbl src dst) s = some s' ∧ s'.mem = VG.Proof.CmacAes.AArch64.dblMem s.mem K src dst ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp (config := {decide := true}) only [dbl, runBlock_cons, runStep_some, runBlock_nil, exec, addr,
      State.load, State.store, Size.bytes, Size.bits, State.read, gpr_write, mem_write, rd_write, wr_write,
      ite_true, ite_false, Option.bind_some, Option.map_some, hb, hs.1, hd.1, BitVec.setWidth_eq,
      show src < 32768 by omega, show src + 8 < 32768 from hs.2, show dst < 32768 by omega,
      show dst + 8 < 32768 from hd.2, Nat.add_mod_right, r₀, r₁, w₀, w₁, and_self]
    rfl, ?_⟩
  refine ⟨?_, fun r h₁ h₂ h₃ h₄ => by simp [gpr_write, h₁, h₂, h₃, h₄], rfl, rfl, rfl⟩
  simp only [VG.Proof.CmacAes.AArch64.dblMem, VG.Proof.CmacAes.AArch64.dblHi, VG.Proof.CmacAes.AArch64.dblLo, Mem.writeW, Mem.readW, BitVec.setWidth_eq, VG.Proof.CmacAes.AArch64.mz0, VG.Proof.CmacAes.AArch64.mz87]

theorem dblMem_frame (m : Mem) (K : Addr) (src dst : Nat) :
    Frame [⟨K + BitVec.ofNat 64 dst, 16⟩] m (VG.Proof.CmacAes.AArch64.dblMem m K src dst) := by
  rw [VG.Proof.CmacAes.AArch64.dblMem, show K + BitVec.ofNat 64 (dst + 8) = K + BitVec.ofNat 64 dst + BitVec.ofNat 64 8 from
    (Offset.add_add _ _ _).symm]
  exact Proof.Cmac.frame_store2 _ _ _

theorem dblMem_bytes (m : Mem) (K : Addr) (src dst : Nat) :
    Spec.Aes.bytesAt (VG.Proof.CmacAes.AArch64.dblMem m K src dst) (K + BitVec.ofNat 64 dst) 16 =
      Spec.Cmac.dbl 16 (Spec.Aes.bytesAt m (K + BitVec.ofNat 64 src) 16) := by
  rw [VG.Proof.CmacAes.AArch64.dblMem, show K + BitVec.ofNat 64 (dst + 8) = K + BitVec.ofNat 64 dst + BitVec.ofNat 64 8 from
      (Offset.add_add _ _ _).symm,
    show K + BitVec.ofNat 64 (src + 8) = K + BitVec.ofNat 64 src + BitVec.ofNat 64 8 from
      (Offset.add_add _ _ _).symm,
    Proof.Cmac.bytesAt_store2, VG.Proof.CmacAes.AArch64.le8_rev, VG.Proof.CmacAes.AArch64.dbl_words, Proof.Cmac.dbl_eq (Proof.Cmac.bytesAt_length _ _ _),
    ← Spec.Gcm.blockAt, ← Proof.Gcm.AArch64.blockAt_rev, BitVec.add_zero]

/-! ## Before the call -/

/-- The memory after `subkeysPre`. -/
def preMem (s : State) : Mem :=
  ((((((s.mem.writeW (s.gpr .x3 + BitVec.ofNat 64 2064) (s.gpr .x19)).writeW
    (s.gpr .x3 + BitVec.ofNat 64 2072) (s.gpr .x20)).writeW
    (s.gpr .x3 + BitVec.ofNat 64 2080) (s.gpr .x30)).writeW
    (s.gpr .x3 + BitVec.ofNat 64 2048) (0 : BitVec 64)).writeW
    (s.gpr .x3 + BitVec.ofNat 64 2056) (0 : BitVec 64)).writeW
    (s.gpr .x2 + BitVec.ofNat 64 0) (0 : BitVec 64)).writeW
    (s.gpr .x2 + BitVec.ofNat 64 8) (0 : BitVec 64)

theorem subkeysPre_ok (s : State)
    (w₁ : InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 2064) 8)
    (w₂ : InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 2072) 8)
    (w₃ : InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 2080) 8)
    (w₄ : InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 2048) 8)
    (w₅ : InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 2056) 8)
    (w₆ : InRegions s.wr (s.gpr .x2 + BitVec.ofNat 64 0) 8)
    (w₇ : InRegions s.wr (s.gpr .x2 + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa subkeysPre s = some s' ∧
      s'.gpr .x0 = s.gpr .x0 ∧ s'.gpr .x1 = s.gpr .x1 ∧
      s'.gpr .x2 = s.gpr .x3 + BitVec.ofNat 64 2048 ∧ s'.gpr .x3 = s.gpr .x2 ∧ s'.gpr .x4 = 1 ∧
      s'.gpr .x5 = s.gpr .x3 ∧ s'.gpr .x19 = s.gpr .x2 ∧ s'.gpr .x20 = s.gpr .x3 ∧
      (∀ r ∈ preserved, r ≠ .x19 → r ≠ .x20 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      s'.mem = VG.Proof.CmacAes.AArch64.preMem s ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp (config := {decide := true}) only [subkeysPre, ctrArgs, cOff, mov, List.cons_append,
      List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.store, Size.bytes,
      Size.bits, State.read, gpr_write, mem_write, wr_write, ite_true, ite_false, Option.bind_some,
      BitVec.setWidth_eq, w₁, w₂, w₃, w₄, w₅, w₆, w₇]
    rfl, ?_⟩
  refine ⟨by simp [gpr_write], by simp [gpr_write], by simp [gpr_write], by simp [gpr_write], rfl,
    by simp [gpr_write], by simp [gpr_write], by simp [gpr_write], fun r hr h₁ h₂ => ?_, rfl, ?_, rfl, rfl⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [gpr_write]
  · simp only [mem_write, VG.Proof.CmacAes.AArch64.preMem, Mem.writeW, BitVec.setWidth_eq, VG.Proof.CmacAes.AArch64.mz0]

/-! ## The whole function -/

/-- The precondition, by name: the schedule `W`, the subkeys `K`, the scratch
buffer `S` and the rounds `R`. -/
structure SPre (s₀ : State) (W K S : Addr) (R : Nat) : Prop where
  x0 : s₀.gpr .x0 = W
  x2 : s₀.gpr .x2 = K
  x3 : s₀.gpr .x3 = S
  x1 : (s₀.gpr .x1).toNat = R
  rd : s₀.rd = [⟨W, 240⟩]
  wr : s₀.wr = [⟨K, 32⟩, ⟨S, 2176⟩]
  sch_k : (⟨W, 240⟩ : Region).Disjoint ⟨K, 32⟩
  sch_scr : (⟨W, 240⟩ : Region).Disjoint ⟨S, 2176⟩
  k_scr : (⟨K, 32⟩ : Region).Disjoint ⟨S, 2176⟩
  k_wrap : K.toNat + 32 ≤ 2 ^ 64
  scr_wrap : S.toNat + 2176 ≤ 2 ^ 64
  rounds : R = 10 ∨ R = 12 ∨ R = 14

theorem SPre.of {s₀ : State} (h : subkeysAArch64.pre s₀) :
    VG.Proof.CmacAes.AArch64.SPre s₀ (s₀.gpr .x0) (s₀.gpr .x2) (s₀.gpr .x3) (s₀.gpr .x1).toNat :=
  let ⟨a, b, c, d, e, f, g, h⟩ := h
  ⟨rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h⟩

theorem bytesAt_32 (m : Mem) (p : Addr) :
    Spec.Aes.bytesAt m p 32 = Spec.Aes.bytesAt m p 16 ++ Spec.Aes.bytesAt m (p + BitVec.ofNat 64 16) 16 := by
  simp only [Spec.Aes.bytesAt]
  rw [show (32 : Nat) = 16 + 16 from rfl, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, BitVec.add_assoc]
  congr 1
  rw [BitVec.ofNat_add]

theorem k0 (K : Addr) : K + BitVec.ofNat 64 0 = K := BitVec.add_zero K

theorem zeros_8_8 : Spec.Cmac.zeros 8 ++ Spec.Cmac.zeros 8 = Spec.Cmac.zeros 16 := by decide

theorem scr_sub' {S : Addr} {d n : Nat} (h : d + n ≤ 2176) :
    Region.Sub ⟨S + BitVec.ofNat 64 d, n⟩ ⟨S, 2176⟩ := Offset.sub_base _ h

theorem preMem_frame (s : State) :
    Frame [⟨s.gpr .x3 + BitVec.ofNat 64 2048, 40⟩, ⟨s.gpr .x2, 16⟩] s.mem (VG.Proof.CmacAes.AArch64.preMem s) := by
  have c (d : Nat) (h : d + 8 ≤ 40) :
      (⟨s.gpr .x3 + BitVec.ofNat 64 2048, 40⟩ : Region).Contains (s.gpr .x3 + BitVec.ofNat 64 (2048 + d)) 8 := by
    rw [← Offset.add_add]; exact Offset.contains_base _ h (by omega)
  have k (d : Nat) (h : d + 8 ≤ 16) : (⟨s.gpr .x2, 16⟩ : Region).Contains (s.gpr .x2 + BitVec.ofNat 64 d) 8 :=
    Offset.contains_base _ h (by omega)
  exact (((((((Frame.refl _ _).writeW (by simp) _ (c 16 (by decide))).writeW (by simp) _
    (c 24 (by decide))).writeW (by simp) _ (c 32 (by decide))).writeW
    (by simp) _ (c 0 (by decide))).writeW (by simp) _ (c 8 (by decide))).writeW (by simp) _
    (k 0 (by decide))).writeW (by simp) _ (k 8 (by decide))

theorem frame_store2' {m : Mem} (p : Addr) (w₀ w₁ : BitVec 64) :
    Frame [⟨p, 16⟩] m ((m.writeW (p + BitVec.ofNat 64 0) w₀).writeW (p + BitVec.ofNat 64 8) w₁) := by
  rw [VG.Proof.CmacAes.AArch64.k0]; exact Proof.Cmac.frame_store2 _ _ _

theorem restore3_ok (s : State) {B : Addr} (hb : s.gpr .x20 = B)
    (r₁ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 2064) 8)
    (r₂ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 2072) 8)
    (r₃ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 2080) 8) :
    ∃ s', runBlock isa [.ldr .x .x30 .x20 2080, .ldr .x .x19 .x20 2064, .ldr .x .x20 .x20 2072] s = some s' ∧
      s'.gpr .x19 = s.mem.readW (B + BitVec.ofNat 64 2064) 64 ∧
      s'.gpr .x20 = s.mem.readW (B + BitVec.ofNat 64 2072) 64 ∧
      s'.gpr .x30 = s.mem.readW (B + BitVec.ofNat 64 2080) 64 ∧
      (∀ r, r ≠ .x19 → r ≠ .x20 → r ≠ .x30 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul, Nat.reduceMod, and_self, runBlock_cons, runStep_some, runBlock_nil, exec, addr,
      State.load, Size.bytes, Size.bits, gpr_write, mem_write, rd_write, wr_write,
      Option.bind_some, Option.map_some, hb, r₁, r₂, r₃]
    rfl, ?_⟩
  refine ⟨by simp [gpr_write, Mem.readW], by simp [gpr_write, Mem.readW], by simp [gpr_write, Mem.readW],
    fun r h₁ h₂ h₃ => by simp [gpr_write, h₁, h₂, h₃], rfl, rfl⟩

theorem readW_writeW_other' (m : Mem) (b : Addr) {d e : Nat} (v : BitVec 64) (h : d + 8 ≤ e ∨ e + 8 ≤ d)
    (hd : d + 8 ≤ 2 ^ 64) (he : e + 8 ≤ 2 ^ 64) :
    (m.writeW (b + BitVec.ofNat 64 e) v).readW (b + BitVec.ofNat 64 d) 64 = m.readW (b + BitVec.ofNat 64 d) 64 :=
  VG.Proof.CmacAes.AArch64.readW_writeW_other m b v h hd he

theorem preMem_slot (s : State) {d : Nat} (hd : d = 2064 ∨ d = 2072 ∨ d = 2080)
    (hks : (⟨s.gpr .x2, 32⟩ : Region).Disjoint ⟨s.gpr .x3, 2176⟩) :
    (VG.Proof.CmacAes.AArch64.preMem s).readW (s.gpr .x3 + BitVec.ofNat 64 d) 64 =
      if d = 2064 then s.gpr .x19 else if d = 2072 then s.gpr .x20 else s.gpr .x30 := by
  have kd (e : Nat) (he : e + 8 ≤ 32) : Mem.Sep (s.gpr .x3 + BitVec.ofNat 64 d) (64 / 8)
      (s.gpr .x2 + BitVec.ofNat 64 e) (64 / 8) :=
    hks.symm.sep (Offset.contains_base _ (by omega) (by omega)) (Offset.contains_base _ he (by omega))
  rw [VG.Proof.CmacAes.AArch64.preMem, Mem.readW_writeW_sep (kd 8 (by decide)) (by decide), Mem.readW_writeW_sep (kd 0 (by decide)) (by decide),
    VG.Proof.CmacAes.AArch64.readW_writeW_other _ _ _ (by omega) (by omega) (by decide),
    VG.Proof.CmacAes.AArch64.readW_writeW_other _ _ _ (by omega) (by omega) (by decide)]
  rcases hd with rfl | rfl | rfl
  · rw [VG.Proof.CmacAes.AArch64.readW_writeW_other _ _ _ (by decide) (by decide) (by decide),
      VG.Proof.CmacAes.AArch64.readW_writeW_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]; rfl
  · rw [VG.Proof.CmacAes.AArch64.readW_writeW_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]; rfl
  · rw [Mem.readW_writeW_self64]; rfl

theorem callPre_of {s₀ : State} {W K S : Addr} {R : Nat} (hp : VG.Proof.CmacAes.AArch64.SPre s₀ W K S R) {s₁ : State}
    (x0₁ : s₁.gpr .x0 = s₀.gpr .x0) (x1₁ : s₁.gpr .x1 = s₀.gpr .x1)
    (x2₁ : s₁.gpr .x2 = s₀.gpr .x3 + BitVec.ofNat 64 2048) (x3₁ : s₁.gpr .x3 = s₀.gpr .x2)
    (x4₁ : s₁.gpr .x4 = 1) (x5₁ : s₁.gpr .x5 = s₀.gpr .x3)
    (mem₁ : s₁.mem = VG.Proof.CmacAes.AArch64.preMem s₀) (rd₁ : s₁.rd = s₀.rd) (wr₁ : s₁.wr = s₀.wr) :
    VG.Proof.CmacAes.AArch64.CallPre s₁ W (S + BitVec.ofNat 64 2048) K S R := by
  have hR := hp.rounds
  have kw := hp.k_wrap
  have sw := hp.scr_wrap
  have cK : (⟨K, 16⟩ : Region).Disjoint ⟨S + BitVec.ofNat 64 2048, 16⟩ :=
    (hp.k_scr.sub_left (Region.sub_prefix (by decide))).sub_right (VG.Proof.CmacAes.AArch64.scr_sub' (by decide))
  have zK : Spec.Aes.bytesAt s₁.mem K 16 = Spec.Cmac.zeros 16 := by
    rw [mem₁, VG.Proof.CmacAes.AArch64.preMem, hp.x2, VG.Proof.CmacAes.AArch64.k0, Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_zero, VG.Proof.CmacAes.AArch64.zeros_8_8]
  exact
      { x0 := by rw [x0₁, hp.x0]
        x1 := by rw [x1₁]; apply BitVec.eq_of_toNat_eq; simp [hp.x1]; omega
        x2 := by rw [x2₁, hp.x3]
        x3 := by rw [x3₁, hp.x2]
        x4 := x4₁
        x5 := by rw [x5₁, hp.x3]
        rounds := hR
        wc := hp.sch_scr.sub_right (VG.Proof.CmacAes.AArch64.scr_sub' (by decide))
        wd := hp.sch_k.sub_right (Region.sub_prefix (by decide))
        ws := hp.sch_scr.sub_right (Region.sub_prefix (by decide))
        cd := cK.symm
        cs := Offset.disjoint_base _ (by decide) (by omega)
        ds := (hp.k_scr.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
        wrap := by omega
        reads := by
          rw [rd₁, wr₁, hp.rd, hp.wr]
          refine Covers.of_sub fun r hr => ?_
          simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · exact ⟨⟨W, 240⟩, by simp, 0, by simp, by simp⟩
          · exact ⟨⟨S, 2176⟩, by simp, 2048, rfl, by simp⟩
          · exact ⟨⟨K, 32⟩, by simp, 0, by simp, by simp⟩
          · exact ⟨⟨S, 2176⟩, by simp, 0, by simp, by simp⟩
        writes := by
          rw [wr₁, hp.wr]
          refine Covers.of_sub fun r hr => ?_
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact ⟨⟨S, 2176⟩, by simp, 2048, rfl, by simp⟩
          · exact ⟨⟨K, 32⟩, by simp, 0, by simp, by simp⟩
          · exact ⟨⟨S, 2176⟩, by simp, 0, by simp, by simp⟩
        zero := zK }

theorem subkeys_wp (v : Ctr32Impl) {s₀ : State} (h0 : subkeysAArch64.pre s₀) :
    WP isa (subkeys v.callee) s₀ fun s' => GprAbi s₀ s' ∧ subkeysAArch64.post s₀ s' := by
  have hp := SPre.of h0
  generalize s₀.gpr .x0 = W at hp
  generalize s₀.gpr .x2 = K at hp
  generalize s₀.gpr .x3 = S at hp
  generalize (s₀.gpr .x1).toNat = R at hp
  have hR := hp.rounds
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with h | h | h <;> omega
  have kw := hp.k_wrap
  have sw := hp.scr_wrap
  have inS (d : Nat) (h : d + 8 ≤ 2176) : InRegions s₀.wr (S + BitVec.ofNat 64 d) 8 := by
    rw [hp.wr]; exact VG.Proof.CmacAes.AArch64.in_rw (r := ⟨S, 2176⟩) (by simp) (Offset.contains_base _ h (by omega))
  have inK (d : Nat) (h : d + 8 ≤ 32) : InRegions s₀.wr (K + BitVec.ofNat 64 d) 8 := by
    rw [hp.wr]; exact VG.Proof.CmacAes.AArch64.in_rw (r := ⟨K, 32⟩) (by simp) (Offset.contains_base _ h (by omega))
  -- Before the call.
  obtain ⟨s₁, run₁, x0₁, x1₁, x2₁, x3₁, x4₁, x5₁, x19₁, x20₁, cs₁, sp₁, mem₁, rd₁, wr₁⟩ :=
    VG.Proof.CmacAes.AArch64.subkeysPre_ok s₀ (by rw [hp.x3]; exact inS _ (by decide)) (by rw [hp.x3]; exact inS _ (by decide))
      (by rw [hp.x3]; exact inS _ (by decide)) (by rw [hp.x3]; exact inS _ (by decide))
      (by rw [hp.x3]; exact inS _ (by decide))
      (by rw [hp.x2]; exact inK _ (by decide)) (by rw [hp.x2]; exact inK _ (by decide))
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  -- The memory before the call.
  have f₁ : Frame [⟨S + BitVec.ofNat 64 2048, 40⟩, ⟨K, 16⟩] s₀.mem s₁.mem := by
    rw [mem₁, ← hp.x3, ← hp.x2]; exact VG.Proof.CmacAes.AArch64.preMem_frame s₀
  have cK : (⟨K, 16⟩ : Region).Disjoint ⟨S + BitVec.ofNat 64 2048, 16⟩ :=
    (hp.k_scr.sub_left (Region.sub_prefix (by decide))).sub_right (VG.Proof.CmacAes.AArch64.scr_sub' (by decide))
  have zC : Spec.Aes.bytesAt s₁.mem (S + BitVec.ofNat 64 2048) 16 = Spec.Cmac.zeros 16 := by
    rw [mem₁, VG.Proof.CmacAes.AArch64.preMem, hp.x3, hp.x2]
    rw [Proof.Cmac.bytesAt_frame16 (VG.Proof.CmacAes.AArch64.frame_store2' K _ _) (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact cK.symm)]
    rw [(Offset.add_add_eq S (a := 2048) (b := 8) (c := 2056) rfl).symm, Proof.Cmac.bytesAt_store2,
      Proof.Cmac.le8_zero, VG.Proof.CmacAes.AArch64.zeros_8_8]
  have zK : Spec.Aes.bytesAt s₁.mem K 16 = Spec.Cmac.zeros 16 := by
    rw [mem₁, VG.Proof.CmacAes.AArch64.preMem, hp.x2, VG.Proof.CmacAes.AArch64.k0, Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_zero, VG.Proof.CmacAes.AArch64.zeros_8_8]
  have schB : ∀ m : Mem, Frame [⟨S + BitVec.ofNat 64 2048, 40⟩, ⟨K, 16⟩] s₀.mem m →
      Spec.Aes.bytesAt m W (16 * (R + 1)) = Spec.Aes.bytesAt s₀.mem W (16 * (R + 1)) := fun m hf =>
    Proof.Cmac.bytesAt_frame hf (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hp.sch_scr.sub_left (Region.sub_prefix hRb)).sub_right (VG.Proof.CmacAes.AArch64.scr_sub' (by decide))
      · exact (hp.sch_k.sub_left (Region.sub_prefix hRb)).sub_right (Region.sub_prefix (by decide))) (by omega)
  -- The call.
  have pre := VG.Proof.CmacAes.AArch64.callPre_of hp x0₁ x1₁ x2₁ x3₁ x4₁ x5₁ mem₁ rd₁ wr₁
  refine WP.seq (WP.mono (VG.Proof.CmacAes.AArch64.ctr_call v pre) fun s₂ h₂ => ?_)
  -- After the call.
  have x19₂ : s₂.gpr .x19 = K := by rw [h₂.saved .x19 (by simp [preserved]) (by decide), x19₁, hp.x2]
  have x20₂ : s₂.gpr .x20 = S := by rw [h₂.saved .x20 (by simp [preserved]) (by decide), x20₁, hp.x3]
  have rdwr₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [h₂.rd, h₂.wr, rd₁, wr₁]
  have wr₂ : s₂.wr = s₀.wr := by rw [h₂.wr, wr₁]
  have rIn (a : Addr) (h : InRegions s₀.wr a 8) : InRegions (s₀.rd ++ s₀.wr) a 8 := by
    obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩
  rw [subkeysPost, WP.block_append_iff, WP.block_append_iff]
  obtain ⟨s₃, run₃, mem₃, g₃, sp₃, rd₃, wr₃⟩ := VG.Proof.CmacAes.AArch64.dbl_ok s₂ x19₂ (src := 0) (dst := 0) (by decide) (by decide)
    (by rw [rdwr₂]; exact rIn _ (inK 0 (by decide))) (by rw [rdwr₂]; exact rIn _ (inK 8 (by decide)))
    (by rw [wr₂]; exact inK 0 (by decide)) (by rw [wr₂]; exact inK 8 (by decide))
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have x19₃ : s₃.gpr .x19 = K := by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), x19₂]
  obtain ⟨s₄, run₄, mem₄, g₄, sp₄, rd₄, wr₄⟩ := VG.Proof.CmacAes.AArch64.dbl_ok s₃ x19₃ (src := 0) (dst := 16) (by decide) (by decide)
    (by rw [rd₃, wr₃, rdwr₂]; exact rIn _ (inK 0 (by decide)))
    (by rw [rd₃, wr₃, rdwr₂]; exact rIn _ (inK 8 (by decide)))
    (by rw [wr₃, wr₂]; exact inK 16 (by decide)) (by rw [wr₃, wr₂]; exact inK 24 (by decide))
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  have x20₄ : s₄.gpr .x20 = S := by
    rw [g₄ _ (by decide) (by decide) (by decide) (by decide), g₃ _ (by decide) (by decide) (by decide) (by decide),
      x20₂]
  obtain ⟨s₅, run₅, x19₅, x20₅, x30₅, g₅, sp₅, mem₅⟩ := VG.Proof.CmacAes.AArch64.restore3_ok s₄ x20₄
    (by rw [rd₄, wr₄, rd₃, wr₃, rdwr₂]; exact rIn _ (inS 2064 (by decide)))
    (by rw [rd₄, wr₄, rd₃, wr₃, rdwr₂]; exact rIn _ (inS 2072 (by decide)))
    (by rw [rd₄, wr₄, rd₃, wr₃, rdwr₂]; exact rIn _ (inS 2080 (by decide)))
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  -- Memory.
  have f₂ := h₂.frame
  have f₃ : Frame [⟨K + BitVec.ofNat 64 0, 16⟩] s₂.mem s₃.mem := by rw [mem₃]; exact VG.Proof.CmacAes.AArch64.dblMem_frame _ _ _ _
  have f₄ : Frame [⟨K + BitVec.ofNat 64 16, 16⟩] s₃.mem s₄.mem := by rw [mem₄]; exact VG.Proof.CmacAes.AArch64.dblMem_frame _ _ _ _
  have slotD : ∀ r ∈ [⟨S + BitVec.ofNat 64 2048, 16⟩, ⟨K, 16⟩, ⟨S, 2048⟩],
      (⟨S + BitVec.ofNat 64 2064, 24⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint S (by decide) (by omega) (by omega)
    · exact (hp.k_scr.symm.sub_left (VG.Proof.CmacAes.AArch64.scr_sub' (by decide))).sub_right (Region.sub_prefix (by decide))
    · exact Offset.disjoint_base _ (by decide) (by omega)
  have slotK (e : Nat) (he : e ≤ 16) : (⟨S + BitVec.ofNat 64 2064, 24⟩ : Region).Disjoint ⟨K + BitVec.ofNat 64 e, 16⟩ :=
    (hp.k_scr.symm.sub_left (VG.Proof.CmacAes.AArch64.scr_sub' (by decide))).sub_right (Offset.sub_base _ (by omega))
  have slot (d : Nat) (h₁ : 2064 ≤ d) (h₂' : d + 8 ≤ 2088) :
      s₄.mem.readW (S + BitVec.ofNat 64 d) 64 = s₁.mem.readW (S + BitVec.ofNat 64 d) 64 := by
    have c : (⟨S + BitVec.ofNat 64 2064, 24⟩ : Region).Contains (S + BitVec.ofNat 64 d) (64 / 8) := by
      rw [show S + BitVec.ofNat 64 d = S + BitVec.ofNat 64 2064 + BitVec.ofNat 64 (d - 2064) from
        (Offset.add_add_eq S (by omega)).symm]
      exact Offset.contains_base _ (by omega) (by omega)
    rw [f₄.readW c (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact slotK 16 (by decide))
        (by decide),
      f₃.readW c (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact slotK 0 (by decide))
        (by decide),
      f₂.readW c slotD (by decide)]
  have pslot := fun d hd => VG.Proof.CmacAes.AArch64.preMem_slot s₀ (d := d) hd (by rw [hp.x2, hp.x3]; exact hp.k_scr)
  rw [hp.x3] at pslot
  have gk (r : Reg) (hr : r ∈ preserved) (h19 : r ≠ .x19) (h20 : r ≠ .x20) (h30 : r ≠ .x30) :
      s₅.gpr r = s₀.gpr r := by
    have n9 : r ≠ .x9 := by rintro rfl; simp [preserved] at hr
    have n10 : r ≠ .x10 := by rintro rfl; simp [preserved] at hr
    have n11 : r ≠ .x11 := by rintro rfl; simp [preserved] at hr
    have n12 : r ≠ .x12 := by rintro rfl; simp [preserved] at hr
    rw [g₅ r h19 h20 h30, g₄ r n9 n10 n11 n12, g₃ r n9 n10 n11 n12, h₂.saved r hr h30, cs₁ r hr h19 h20]
  refine ⟨⟨fun r hr => ?_, by rw [sp₅, sp₄, sp₃, h₂.sp, sp₁]⟩, ?_⟩
  · by_cases h19 : r = .x19
    · subst h19; rw [x19₅, slot 2064 (by decide) (by decide), mem₁, pslot 2064 (.inl rfl)]; rfl
    by_cases h20 : r = .x20
    · subst h20; rw [x20₅, slot 2072 (by decide) (by decide), mem₁, pslot 2072 (.inr (.inl rfl))]; rfl
    by_cases h30 : r = .x30
    · subst h30; rw [x30₅, slot 2080 (by decide) (by decide), mem₁, pslot 2080 (.inr (.inr rfl))]; rfl
    exact gk r hr h19 h20 h30
  · show Spec.Aes.bytesAt s₅.mem (s₀.gpr .x2) 32 = _
    rw [hp.x2, hp.x0, hp.x1, mem₅, VG.Proof.CmacAes.AArch64.bytesAt_32]
    have L : Spec.Aes.bytesAt s₂.mem K 16 = VG.Proof.CmacAes.AArch64.ciphAt s₀.mem W R (Spec.Cmac.zeros 16) := by
      rw [h₂.out, schB _ f₁, zC]
    have b3 : Spec.Aes.bytesAt s₃.mem K 16 = Spec.Cmac.dbl 16 (Spec.Aes.bytesAt s₂.mem K 16) := by
      have := VG.Proof.CmacAes.AArch64.dblMem_bytes s₂.mem K 0 0
      rw [VG.Proof.CmacAes.AArch64.k0] at this; rw [mem₃, this]
    have b4lo : Spec.Aes.bytesAt s₄.mem K 16 = Spec.Aes.bytesAt s₃.mem K 16 :=
      Proof.Cmac.bytesAt_frame16 f₄ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (Offset.disjoint_base K (by decide) (by omega)).symm
    have b4hi : Spec.Aes.bytesAt s₄.mem (K + BitVec.ofNat 64 16) 16 =
        Spec.Cmac.dbl 16 (Spec.Aes.bytesAt s₃.mem K 16) := by
      have := VG.Proof.CmacAes.AArch64.dblMem_bytes s₃.mem K 0 16
      rw [VG.Proof.CmacAes.AArch64.k0] at this; rw [mem₄, this]
    rw [b4lo, b4hi, b3, L]
    rfl

end VG.Proof.CmacAes.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.AArch64.Finalize`. -/
section

/-!
# AES-CMAC on AArch64: `vg_cmac_aes_finalize`, the last block

The steps that form the counter block `C ⊕ Mₙ` in the scratch buffer before
the call.
-/

namespace VG.Proof.CmacAes.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.CmacAes.AArch64

/-- The block XOR `full`, `padK2` and `finArgs` do: the words at `pb + pd` and
`qb + qd` XORed into `cb + cd`. -/
def xor2 (pb qb cb : Reg) (pd qd cd : Nat) : List Instr :=
  [.ldr .x .x9 pb pd, .ldr .x .x10 qb qd, .logic .eor .x .x9 .x9 .x10, .str .x .x9 cb cd,
   .ldr .x .x9 pb (pd + 8), .ldr .x .x10 qb (qd + 8), .logic .eor .x .x9 .x9 .x10, .str .x .x9 cb (cd + 8)]

theorem xor2_ok (s : State) (pb qb cb : Reg) (pd qd cd : Nat) {P Q C : Addr}
    (hpd : pd % 8 = 0 ∧ pd + 8 < 32768) (hqd : qd % 8 = 0 ∧ qd + 8 < 32768)
    (hcd : cd % 8 = 0 ∧ cd + 8 < 32768)
    (hp : s.gpr pb + BitVec.ofNat 64 pd = P) (hp8 : s.gpr pb + BitVec.ofNat 64 (pd + 8) = P + BitVec.ofNat 64 8)
    (hq : s.gpr qb + BitVec.ofNat 64 qd = Q) (hq8 : s.gpr qb + BitVec.ofNat 64 (qd + 8) = Q + BitVec.ofNat 64 8)
    (hc : s.gpr cb + BitVec.ofNat 64 cd = C) (hc8 : s.gpr cb + BitVec.ofNat 64 (cd + 8) = C + BitVec.ofNat 64 8)
    (hr : pb ≠ .x9 ∧ pb ≠ .x10 ∧ qb ≠ .x9 ∧ qb ≠ .x10 ∧ cb ≠ .x9 ∧ cb ≠ .x10)
    (rp : InRegions (s.rd ++ s.wr) P 8) (rp8 : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 8) 8)
    (rq : InRegions (s.rd ++ s.wr) Q 8) (rq8 : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 8) 8)
    (wc : InRegions s.wr C 8) (wc8 : InRegions s.wr (C + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa (VG.Proof.CmacAes.AArch64.xor2 pb qb cb pd qd cd) s = some s' ∧
      s'.mem = Proof.Cmac.xor2Mem s.mem C P Q ∧ (∀ r, r ≠ .x9 → r ≠ .x10 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := hr
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceMul, VG.Proof.CmacAes.AArch64.xor2, runBlock_cons, runStep_some, runBlock_nil, exec, addr,
      State.load, State.store, Size.bytes, Size.bits, State.read, gpr_write, mem_write, rd_write,
      wr_write, Option.bind_some, Option.map_some, BitVec.setWidth_eq,
      h₁, h₂, h₃, h₄, h₅, h₆, hpd.1, hqd.1, hcd.1, Nat.add_mod_right,
      show pd < 32768 by omega, show qd < 32768 by omega, show cd < 32768 by omega, hpd.2, hqd.2, hcd.2,
      hp, hp8, hq, hq8, hc, hc8, rp, rp8, rq, rq8, wc, wc8, and_self]
    rfl, ?_⟩
  refine ⟨?_, fun r h₁ h₂ => by simp [gpr_write, h₁, h₂], rfl, rfl, rfl⟩
  simp only [Proof.Cmac.xor2Mem, Mem.writeW, Mem.readW, BitVec.setWidth_eq]

theorem full_eq : full = VG.Proof.CmacAes.AArch64.xor2 .x3 .x0 .x5 0 240 2048 := rfl
theorem padK2_eq :
    padK2 = ([.movz .x .x9 0x80 0, .strb .x9 .x6 0] : List Instr) ++ VG.Proof.CmacAes.AArch64.xor2 .x5 .x0 .x5 2048 256 2048 := rfl
theorem finArgs_eq : finArgs = VG.Proof.CmacAes.AArch64.xor2 .x5 .x2 .x5 2048 0 2048 ++
    ([.movz .x .x9 0 0, .str .x .x9 .x2 0, .str .x .x9 .x2 8, .str .x .x19 .x5 2064, .str .x .x30 .x5 2072,
     mov .x19 .x5, mov .x3 .x2, .addImm .x .x2 .x5 cOff, .movz .x .x4 1 0] : List Instr) := rfl

theorem sub16_ok (s : State) {L : Nat} (h4 : s.gpr .x4 = BitVec.ofNat 64 L) (hL : L ≤ 16) :
    ∃ s', runBlock isa [.subImm .x .x9 .x4 16] s = some s' ∧
      isa.eval (.zero .x .x9) s' = some (decide (L = 16)) ∧
      (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by rw [runBlock_cons, exec_subImm_x (by decide), runStep_some, runBlock_nil], ?_⟩
  refine ⟨?_, fun r h => by simp [gpr_write, h], rfl, rfl, rfl, rfl⟩
  show some (_ == 0) = _
  simp only [State.read, gpr_write_self, BitVec.setWidth_eq, h4]
  rw [Offset.ofNat_sub_ofNat_beq (by omega) (by decide)]

theorem zero_ok (s : State) {C : Addr} (hc : s.gpr .x5 + BitVec.ofNat 64 2048 = C)
    (hc8 : s.gpr .x5 + BitVec.ofNat 64 2056 = C + BitVec.ofNat 64 8)
    (wc : InRegions s.wr C 8) (wc8 : InRegions s.wr (C + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa zero s = some s' ∧ s'.mem = Proof.Cmac.zero2 s.mem C ∧ s'.gpr .x6 = C ∧
      s'.gpr .x7 = s.gpr .x3 ∧ s'.gpr .x8 = s.gpr .x4 ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp (config := {decide := true}) only [zero, cOff, mov, runBlock_cons, runStep_some, runBlock_nil,
      exec, addr, State.store, Size.bytes, Size.bits, State.read, gpr_write, mem_write, wr_write,
      ite_true, ite_false, Option.bind_some, BitVec.setWidth_eq, hc, hc8, wc, wc8]
    rfl, ?_⟩
  refine ⟨?_, by simp [gpr_write, ← hc], by simp [gpr_write], by simp [gpr_write],
    fun r h₁ h₂ h₃ h₄ => by simp [gpr_write, h₁, h₂, h₃, h₄], rfl, rfl, rfl⟩
  simp only [mem_write, Proof.Cmac.zero2, Mem.writeW, BitVec.setWidth_eq, VG.Proof.CmacAes.AArch64.mz0]

/-- The copy loop's body. -/
abbrev copyBody : List Instr :=
  [.ldrb .x9 .x7 0, .strb .x9 .x6 0, .addImm .x .x7 .x7 1, .addImm .x .x6 .x6 1, .subImm .x .x8 .x8 1]

theorem byte_rt (b : BitVec (8 * 1)) :
    BitVec.setWidth 8 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 b))) = b := by
  apply BitVec.eq_of_toNat_eq
  have := b.isLt
  simp only [BitVec.toNat_setWidth]
  omega

theorem read_one (m : Mem) (a : Addr) : m.read a 1 = m a := by
  have := Mem.extractLsb'_read m a (n := 1) (j := 0) (by decide)
  rw [show 8 * 0 = 0 from rfl, BitVec.extractLsb'_eq_self, show BitVec.ofNat 64 0 = 0#64 from rfl,
    BitVec.add_zero] at this
  exact this

theorem copyStep_ok (s : State) {A B : Addr} (ha : s.gpr .x7 + BitVec.ofNat 64 0 = A)
    (hb : s.gpr .x6 + BitVec.ofNat 64 0 = B)
    (r : InRegions (s.rd ++ s.wr) A 1) (w : InRegions s.wr B 1) :
    ∃ s', runBlock isa VG.Proof.CmacAes.AArch64.copyBody s = some s' ∧ s'.mem = s.mem.writeW B (s.mem A) ∧
      s'.gpr .x7 = s.gpr .x7 + 1 ∧ s'.gpr .x6 = s.gpr .x6 + 1 ∧ s'.gpr .x8 = s.gpr .x8 - 1 ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul, Nat.reduceMod, and_self, VG.Proof.CmacAes.AArch64.copyBody, runBlock_cons, runStep_some, runBlock_nil,
      exec, addr, State.load, State.store, Size.bits, State.read, gpr_write, mem_write,
      rd_write, wr_write, Option.bind_some, Option.map_some, BitVec.setWidth_eq,
      ha, hb, r, w]
    rfl, ?_⟩
  refine ⟨?_, by simp [gpr_write], by simp [gpr_write], by simp [gpr_write],
    fun r h₁ h₂ h₃ h₄ => by simp [gpr_write, h₁, h₂, h₃, h₄], rfl, rfl, rfl⟩
  simp only [mem_write, Mem.writeW, VG.Proof.CmacAes.AArch64.byte_rt, VG.Proof.CmacAes.AArch64.read_one, Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq]

theorem succ_ofNat (i : Nat) : BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) := (BitVec.ofNat_add i 1).symm

open VG.WriteBytes in
theorem copy_ok (s : State) {P C : Addr} {L : Nat} (hL₀ : 0 < L) (hL : L < 16)
    (h7 : s.gpr .x7 = P) (h6 : s.gpr .x6 = C) (h8 : s.gpr .x8 = BitVec.ofNat 64 L)
    (hr : ∀ i < L, InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < 16, InRegions s.wr (C + BitVec.ofNat 64 i) 1)
    (hd : (⟨P, L⟩ : Region).Disjoint ⟨C, 16⟩) :
    WP isa copy s fun s' => s'.mem = writeBytes s.mem C (Spec.Aes.bytesAt s.mem P L) ∧
      s'.gpr .x6 = C + BitVec.ofNat 64 L ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.loop (M := isa) (body := .block VG.Proof.CmacAes.AArch64.copyBody) (c := .nonzero .x .x8)
    (fun (n : Nat) (t : State) => ∃ i, n = L - i ∧ i < L ∧ t.gpr .x7 = P + BitVec.ofNat 64 i ∧
      t.gpr .x6 = C + BitVec.ofNat 64 i ∧ t.gpr .x8 = BitVec.ofNat 64 (L - i) ∧
      t.mem = writeBytes s.mem C (Spec.Aes.bytesAt s.mem P i) ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → t.gpr r = s.gpr r) ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (L - 0) _
    ⟨0, rfl, hL₀, by rw [h7]; simp, by rw [h6]; simp, by rw [h8, Nat.sub_zero], by simp [Spec.Aes.bytesAt, writeBytes_nil],
      fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
  rintro n t ⟨i, rfl, hi, x7, x6, x8, mem, g, sp, rd, wr⟩
  obtain ⟨t', run', mem', x7', x6', x8', g', sp', rd', wr'⟩ := VG.Proof.CmacAes.AArch64.copyStep_ok t
    (A := P + BitVec.ofNat 64 i) (B := C + BitVec.ofNat 64 i) (by rw [x7, BitVec.add_zero])
    (by rw [x6, BitVec.add_zero]) (by rw [rd, wr]; exact hr i hi) (by rw [wr]; exact hw i (by omega))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hlen : (Spec.Aes.bytesAt s.mem P i).length = i := by simp [Spec.Aes.bytesAt]
  have hx : writeBytes s.mem C (Spec.Aes.bytesAt s.mem P i) (P + BitVec.ofNat 64 i) = s.mem (P + BitVec.ofNat 64 i) :=
    (writeBytes_frame s.mem C _ (R := ⟨C, i⟩) (by rw [hlen]; exact Region.contains_self _ _)) _
      fun r hr hcon => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hd _ (Offset.contains_base P (by omega) (by omega)) (Region.sub_prefix (by omega) _ hcon)
  have hmem : t'.mem = writeBytes s.mem C (Spec.Aes.bytesAt s.mem P (i + 1)) := by
    rw [mem', mem, hx, Proof.Cmac.bytesAt_succ,
      writeBytes_snoc s.mem C (Spec.Aes.bytesAt s.mem P i) (s.mem (P + BitVec.ofNat 64 i)) (by rw [hlen]; omega),
      hlen]
  have hb : L < 2 ^ 64 := by omega
  have x8'' : t'.gpr .x8 = BitVec.ofNat 64 (L - (i + 1)) := by
    rw [x8', x8, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega)]; rfl
  have ev : isa.eval (.nonzero .x .x8) t' = some !decide (L - (i + 1) = 0) := by
    show some (t'.read .x .x8 != 0) = _
    rw [State.read, x8'', BitVec.setWidth_eq, VG.Proof.CmacAes.AArch64.ofNat_ne_zero (by omega)]
  have gg : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → t'.gpr r = s.gpr r := fun r h₁ h₂ h₃ h₄ => by
    rw [g' r h₁ h₂ h₃ h₄, g r h₁ h₂ h₃ h₄]
  by_cases he : i + 1 = L
  · left
    refine ⟨by rw [ev]; simp [he], by rw [hmem, he], by rw [x6', x6, BitVec.add_assoc, VG.Proof.CmacAes.AArch64.succ_ofNat, he], gg,
      by rw [sp', sp], by rw [rd', rd], by rw [wr', wr]⟩
  · right
    refine ⟨by rw [ev]; simp; omega, L - (i + 1), by omega, i + 1, rfl, by omega,
      by rw [x7', x7, BitVec.add_assoc, VG.Proof.CmacAes.AArch64.succ_ofNat], by rw [x6', x6, BitVec.add_assoc, VG.Proof.CmacAes.AArch64.succ_ofNat], x8'', hmem, gg,
      by rw [sp', sp], by rw [rd', rd], by rw [wr', wr]⟩

theorem pad_ok (s : State) {B : Addr} (hb : s.gpr .x6 + BitVec.ofNat 64 0 = B) (w : InRegions s.wr B 1) :
    ∃ s', runBlock isa [.movz .x .x9 0x80 0, .strb .x9 .x6 0] s = some s' ∧
      s'.mem = s.mem.writeW B (0x80 : Byte) ∧ (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul, Nat.reduceMod, and_self, runBlock_cons, runStep_some, runBlock_nil, exec, addr,
      State.store, Size.bits, State.read, gpr_write, wr_write, Option.bind_some,
      hb, w]
    rfl, ?_⟩
  refine ⟨?_, fun r h => by simp [gpr_write, h], rfl, rfl, rfl⟩
  simp only [mem_write, Mem.writeW, Nat.reduceDiv, Nat.reduceMul]
  rfl

theorem args_ok (s : State) {D S : Addr} (hd : s.gpr .x2 = D) (hs : s.gpr .x5 = S)
    (wd : InRegions s.wr (D + BitVec.ofNat 64 0) 8) (wd8 : InRegions s.wr (D + BitVec.ofNat 64 8) 8)
    (ws₁ : InRegions s.wr (S + BitVec.ofNat 64 2064) 8) (ws₂ : InRegions s.wr (S + BitVec.ofNat 64 2072) 8) :
    ∃ s', runBlock isa [.movz .x .x9 0 0, .str .x .x9 .x2 0, .str .x .x9 .x2 8, .str .x .x19 .x5 2064,
        .str .x .x30 .x5 2072, mov .x19 .x5, mov .x3 .x2, .addImm .x .x2 .x5 cOff, .movz .x .x4 1 0] s = some s' ∧
      s'.mem = (((s.mem.writeW (D + BitVec.ofNat 64 0) (0 : BitVec 64)).writeW (D + BitVec.ofNat 64 8)
        (0 : BitVec 64)).writeW (S + BitVec.ofNat 64 2064) (s.gpr .x19)).writeW (S + BitVec.ofNat 64 2072)
        (s.gpr .x30) ∧
      s'.gpr .x3 = D ∧ s'.gpr .x2 = S + BitVec.ofNat 64 2048 ∧ s'.gpr .x4 = 1 ∧ s'.gpr .x19 = S ∧
      (∀ r, r ≠ .x2 → r ≠ .x3 → r ≠ .x4 → r ≠ .x9 → r ≠ .x19 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp (config := {decide := true}) only [cOff, mov, runBlock_cons, runStep_some, runBlock_nil, exec,
      addr, State.store, Size.bytes, Size.bits, State.read, gpr_write, mem_write, wr_write, ite_true,
      ite_false, Option.bind_some, BitVec.setWidth_eq, hd, hs, wd, wd8, ws₁, ws₂]
    rfl, ?_⟩
  refine ⟨?_, by simp [gpr_write], by simp [gpr_write], rfl, by simp [gpr_write],
    fun r h₁ h₂ h₃ h₄ h₅ => by simp [gpr_write, h₁, h₂, h₃, h₄, h₅], rfl, rfl, rfl⟩
  simp only [mem_write, Mem.writeW, BitVec.setWidth_eq, VG.Proof.CmacAes.AArch64.mz0]

end VG.Proof.CmacAes.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.AArch64.FinalizeCorrect`. -/
section

/-!
# AES-CMAC on AArch64: `vg_cmac_aes_finalize` is correct

Before the call, the counter block (at `S + 2048`) holds `Mₙ ⊕ C`, for the
last block `Mₙ` of §6.2 step 4 and the chaining value `C` at `state`, the
state is zeroed, and `x19` and `x30` are saved in the scratch buffer; the call
leaves `CIPH_K(C ⊕ Mₙ)` there, the MAC (`macFull_split`).
-/

namespace VG.Proof.CmacAes.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.CmacAes.AArch64
open VG.Proof.Aes.AArch64 (Ctr32Impl)

/-- The precondition, by name: the key (schedule and subkeys) `W`, the state
`St`, the last bytes `P` (`L` of them), the scratch buffer `S` and the
rounds `R`. -/
structure FPre (s₀ : State) (W St P S : Addr) (L R : Nat) : Prop where
  x0 : s₀.gpr .x0 = W
  x2 : s₀.gpr .x2 = St
  x3 : s₀.gpr .x3 = P
  x4 : (s₀.gpr .x4).toNat = L
  x5 : s₀.gpr .x5 = S
  x1 : (s₀.gpr .x1).toNat = R
  rd : s₀.rd = [⟨W, 272⟩, ⟨P, L⟩]
  wr : s₀.wr = [⟨St, 16⟩, ⟨S, 2176⟩]
  key_st : (⟨W, 272⟩ : Region).Disjoint ⟨St, 16⟩
  key_scr : (⟨W, 272⟩ : Region).Disjoint ⟨S, 2176⟩
  last_st : (⟨P, L⟩ : Region).Disjoint ⟨St, 16⟩
  last_scr : (⟨P, L⟩ : Region).Disjoint ⟨S, 2176⟩
  st_scr : (⟨St, 16⟩ : Region).Disjoint ⟨S, 2176⟩
  key_wrap : W.toNat + 272 ≤ 2 ^ 64
  st_wrap : St.toNat + 16 ≤ 2 ^ 64
  last_wrap : P.toNat + L ≤ 2 ^ 64
  scr_wrap : S.toNat + 2176 ≤ 2 ^ 64
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  len : L ≤ 16

theorem FPre.of {s₀ : State} (h : finalizeAArch64.pre s₀) :
    VG.Proof.CmacAes.AArch64.FPre s₀ (s₀.gpr .x0) (s₀.gpr .x2) (s₀.gpr .x3) (s₀.gpr .x5) (s₀.gpr .x4).toNat (s₀.gpr .x1).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m⟩ := h
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i, j, k, l, m⟩

/-- The last block `Mₙ` (§6.2 step 4), from the key and the last bytes in `m`. -/
abbrev mn (m : Mem) (W P : Addr) (L : Nat) : List Byte :=
  Spec.Cmac.lastBlock 16 (Spec.Aes.bytesAt m (W + BitVec.ofNat 64 240) 16)
    (Spec.Aes.bytesAt m (W + BitVec.ofNat 64 256) 16) (Spec.Aes.bytesAt m P L)

/-- What the branch on the length leaves: `Mₙ` in the counter block. -/
structure BPost (s₀ : State) (W St P S : Addr) (L : Nat) (s : State) : Prop where
  x0 : s.gpr .x0 = W
  x2 : s.gpr .x2 = St
  x5 : s.gpr .x5 = S
  x1 : s.gpr .x1 = s₀.gpr .x1
  saved : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨S + BitVec.ofNat 64 2048, 16⟩] s₀.mem s.mem
  blk : Spec.Aes.bytesAt s.mem (S + BitVec.ofNat 64 2048) 16 = VG.Proof.CmacAes.AArch64.mn s₀.mem W P L

section
variable {s₀ : State} {W St P S : Addr} {L R : Nat} (hp : VG.Proof.CmacAes.AArch64.FPre s₀ W St P S L R)
include hp

theorem FPre.inScr {d n : Nat} (h : d + n ≤ 2176) : InRegions s₀.wr (S + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact VG.Proof.CmacAes.AArch64.in_rw (r := ⟨S, 2176⟩) (by simp) (Offset.contains_base _ h (by have := hp.scr_wrap; omega))

theorem FPre.inKey {d n : Nat} (h : d + n ≤ 272) : InRegions (s₀.rd ++ s₀.wr) (W + BitVec.ofNat 64 d) n := by
  rw [hp.rd]; exact VG.Proof.CmacAes.AArch64.in_rw (r := ⟨W, 272⟩) (by simp) (Offset.contains_base _ h (by have := hp.key_wrap; omega))

theorem FPre.inLast {d n : Nat} (h : d + n ≤ L) : InRegions (s₀.rd ++ s₀.wr) (P + BitVec.ofNat 64 d) n := by
  rw [hp.rd]; exact VG.Proof.CmacAes.AArch64.in_rw (r := ⟨P, L⟩) (by simp) (Offset.contains_base _ h (by have := hp.len; omega))

end

theorem FPre.scrD {S : Addr} {d n : Nat} (h : d + n ≤ 2176) : Region.Sub ⟨S + BitVec.ofNat 64 d, n⟩ ⟨S, 2176⟩ :=
  Offset.sub_base _ h

theorem wr_in {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n := by
  obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem not_x9 {r : Reg} (hr : r ∈ preserved) : r ≠ .x9 := by rintro rfl; simp [preserved] at hr
theorem not_x10 {r : Reg} (hr : r ∈ preserved) : r ≠ .x10 := by rintro rfl; simp [preserved] at hr
theorem not_x6 {r : Reg} (hr : r ∈ preserved) : r ≠ .x6 := by rintro rfl; simp [preserved] at hr
theorem not_x7 {r : Reg} (hr : r ∈ preserved) : r ≠ .x7 := by rintro rfl; simp [preserved] at hr
theorem not_x8 {r : Reg} (hr : r ∈ preserved) : r ≠ .x8 := by rintro rfl; simp [preserved] at hr

theorem full_wp {s₀ : State} {W St P S : Addr} {L R : Nat} (hp : VG.Proof.CmacAes.AArch64.FPre s₀ W St P S L R) (hL : L = 16)
    {s : State} (hg : ∀ r, r ≠ .x9 → s.gpr r = s₀.gpr r) (hm : s.mem = s₀.mem) (hsp : s.sp = s₀.sp)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block full) s (VG.Proof.CmacAes.AArch64.BPost s₀ W St P S L) := by
  subst hL
  have sw := hp.scr_wrap
  have kw := hp.key_wrap
  obtain ⟨s', run, mem, g, sp, rd, wr⟩ := VG.Proof.CmacAes.AArch64.xor2_ok s .x3 .x0 .x5 0 240 2048
    (P := P) (Q := W + BitVec.ofNat 64 240) (C := S + BitVec.ofNat 64 2048)
    (by decide) (by decide) (by decide)
    (by rw [hg _ (by decide), hp.x3, VG.Proof.CmacAes.AArch64.k0]) (by rw [hg _ (by decide), hp.x3])
    (by rw [hg _ (by decide), hp.x0]) (by rw [hg _ (by decide), hp.x0, Offset.add_add])
    (by rw [hg _ (by decide), hp.x5]) (by rw [hg _ (by decide), hp.x5, Offset.add_add])
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
    (by rw [hrd, hwr]; simpa using hp.inLast (d := 0) (n := 8) (by decide))
    (by rw [hrd, hwr]; exact hp.inLast (d := 8) (n := 8) (by decide))
    (by rw [hrd, hwr]; exact hp.inKey (d := 240) (n := 8) (by decide))
    (by rw [hrd, hwr, Offset.add_add]; exact hp.inKey (d := 248) (n := 8) (by decide))
    (by rw [hwr]; exact hp.inScr (d := 2048) (n := 8) (by decide))
    (by rw [hwr, Offset.add_add]; exact hp.inScr (d := 2056) (n := 8) (by decide))
  rw [VG.Proof.CmacAes.AArch64.full_eq]
  refine WP.of_runBlock ⟨s', run, ?_⟩
  have gg (r : Reg) (h₁ : r ≠ .x9) (h₂ : r ≠ .x10) : s'.gpr r = s₀.gpr r := by rw [g r h₁ h₂, hg r h₁]
  refine ⟨by rw [gg _ (by decide) (by decide), hp.x0], by rw [gg _ (by decide) (by decide), hp.x2],
    by rw [gg _ (by decide) (by decide), hp.x5], gg _ (by decide) (by decide),
    fun r hr => gg r (VG.Proof.CmacAes.AArch64.not_x9 hr) (VG.Proof.CmacAes.AArch64.not_x10 hr), by rw [sp, hsp], by rw [rd, hrd],
    by rw [wr, hwr], by rw [mem, hm]; exact Proof.Cmac.xor2Mem_frame _ _ _ _, ?_⟩
  rw [mem, hm, Proof.Cmac.xor2Mem_bytes]
  · simp only [VG.Proof.CmacAes.AArch64.mn, Spec.Cmac.lastBlock, Proof.Cmac.bytesAt_length, ite_true]
    exact Proof.Cmac.xor_comm _ _
  · exact (hp.last_scr.symm.sub_left (FPre.scrD (d := 2048) (n := 8) (by decide))).sub_right
      (Offset.sub_base P (d := 8) (n := 8) (k := 16) (by decide))
  · rw [Offset.add_add]
    exact (hp.key_scr.symm.sub_left (FPre.scrD (d := 2048) (n := 8) (by decide))).sub_right
      (Offset.sub_base W (d := 248) (n := 8) (k := 272) (by decide))

open VG.WriteBytes in
theorem partial_wp {s₀ : State} {W St P S : Addr} {L R : Nat} (hp : VG.Proof.CmacAes.AArch64.FPre s₀ W St P S L R) (hL : L < 16)
    {s : State} (hg : ∀ r, r ≠ .x9 → s.gpr r = s₀.gpr r) (hm : s.mem = s₀.mem) (hsp : s.sp = s₀.sp)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa partialBlock s (VG.Proof.CmacAes.AArch64.BPost s₀ W St P S L) := by
  have sw := hp.scr_wrap
  have kw := hp.key_wrap
  have hb : L < 2 ^ 64 := by omega
  have h4 : s₀.gpr .x4 = BitVec.ofNat 64 L := by rw [← hp.x4]; apply BitVec.eq_of_toNat_eq; simp
  obtain ⟨C, hC⟩ : ∃ C, S + BitVec.ofNat 64 2048 = C := ⟨_, rfl⟩
  have hc : s.gpr .x5 + BitVec.ofNat 64 2048 = C := by rw [hg _ (by decide), hp.x5, hC]
  have hc8 : s.gpr .x5 + BitVec.ofNat 64 2056 = C + BitVec.ofNat 64 8 := by
    rw [hg _ (by decide), hp.x5, ← hC, Offset.add_add]
  have dPC : (⟨P, L⟩ : Region).Disjoint ⟨C, 16⟩ := by rw [← hC]; exact hp.last_scr.sub_right (FPre.scrD (by decide))
  have dKC (d n : Nat) (h : d + n ≤ 272) : (⟨W + BitVec.ofNat 64 d, n⟩ : Region).Disjoint ⟨C, 16⟩ := by
    rw [← hC]; exact (hp.key_scr.sub_left (Offset.sub_base _ h)).sub_right (FPre.scrD (by decide))
  -- Zero the block.
  obtain ⟨s₁, run₁, mem₁, x6₁, x7₁, x8₁, g₁, sp₁, rd₁, wr₁⟩ := VG.Proof.CmacAes.AArch64.zero_ok s hc hc8
    (by rw [hwr, ← hC]; exact hp.inScr (d := 2048) (n := 8) (by decide))
    (by rw [hwr, ← hC, Offset.add_add]; exact hp.inScr (d := 2056) (n := 8) (by decide))
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have zf : s₁.mem = Proof.Cmac.zero2 s₀.mem C := by rw [mem₁, hm]
  have fz : Frame [⟨C, 16⟩] s₀.mem (Proof.Cmac.zero2 s₀.mem C) := Proof.Cmac.frame_store2 _ _ _
  have lastZ : Spec.Aes.bytesAt (Proof.Cmac.zero2 s₀.mem C) P L = Spec.Aes.bytesAt s₀.mem P L :=
    Proof.Cmac.bytesAt_frame fz (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dPC) (by omega)
  have g₁' (r : Reg) (h₁ : r ≠ .x6) (h₂ : r ≠ .x7) (h₃ : r ≠ .x8) (h₄ : r ≠ .x9) : s₁.gpr r = s₀.gpr r := by
    rw [g₁ r h₁ h₂ h₃ h₄, hg r h₄]
  -- Copy the last bytes.
  refine WP.seq (WP.mono (Q := fun (s₂ : State) =>
      s₂.mem = writeBytes (Proof.Cmac.zero2 s₀.mem C) C (Spec.Aes.bytesAt s₀.mem P L) ∧
      s₂.gpr .x6 = C + BitVec.ofNat 64 L ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → s₂.gpr r = s₀.gpr r) ∧
      s₂.sp = s₀.sp ∧ s₂.rd = s₀.rd ∧ s₂.wr = s₀.wr) ?_ fun s₂ h₂ => ?_)
  · have ev : isa.eval (.zero .x .x4) s₁ = some (decide (L = 0)) := by
      show some (s₁.read .x .x4 == 0) = _
      rw [State.read, g₁' _ (by decide) (by decide) (by decide) (by decide), h4, BitVec.setWidth_eq]
      have := VG.Proof.CmacAes.AArch64.ofNat_ne_zero hb
      rw [bne] at this
      cases hx : (BitVec.ofNat 64 L == 0) <;> rw [hx] at this <;> cases hd : decide (L = 0) <;> simp_all
    by_cases hL0 : L = 0
    · subst hL0
      refine WP.ite true (by rw [ev]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      refine ⟨by rw [zf]; simp [Spec.Aes.bytesAt, writeBytes_nil], by rw [x6₁]; simp,
        fun r h₁ h₂ h₃ h₄ => g₁' r h₁ h₂ h₃ h₄, by rw [sp₁, hsp], by rw [rd₁, hrd], by rw [wr₁, hwr]⟩
    · refine WP.ite false (by rw [ev]; simp [hL0]) (fun h => by cases h) fun _ => ?_
      refine WP.mono (VG.Proof.CmacAes.AArch64.copy_ok s₁ (P := P) (C := C) (by omega) hL
        (by rw [x7₁, hg _ (by decide), hp.x3]) x6₁
        (by rw [x8₁, hg _ (by decide), h4])
        (fun i hi => by rw [rd₁, wr₁, hrd, hwr]; exact hp.inLast (d := i) (n := 1) (by omega))
        (fun i hi => by
          rw [wr₁, hwr, ← hC, Offset.add_add]; exact hp.inScr (d := 2048 + i) (n := 1) (by omega)) dPC) ?_
      rintro s₂ ⟨m₂, x6₂, g₂, sp₂, rd₂, wr₂⟩
      refine ⟨by rw [m₂, zf, lastZ], x6₂, fun r h₁ h₂ h₃ h₄ => by rw [g₂ r h₁ h₂ h₃ h₄, g₁' r h₁ h₂ h₃ h₄],
        by rw [sp₂, sp₁, hsp], by rw [rd₂, rd₁, hrd], by rw [wr₂, wr₁, hwr]⟩
  · obtain ⟨m₂, x6₂, g₂, sp₂, rd₂, wr₂⟩ := h₂
    rw [VG.Proof.CmacAes.AArch64.padK2_eq, WP.block_append_iff]
    obtain ⟨s₃, run₃, m₃, g₃, sp₃, rd₃, wr₃⟩ := VG.Proof.CmacAes.AArch64.pad_ok s₂ (B := C + BitVec.ofNat 64 L)
      (by rw [x6₂, BitVec.add_zero])
      (by rw [wr₂, ← hC, Offset.add_add]; exact hp.inScr (d := 2048 + L) (n := 1) (by omega))
    refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
    have x5₃ : s₃.gpr .x5 = S := by
      rw [g₃ _ (by decide), g₂ _ (by decide) (by decide) (by decide) (by decide), hp.x5]
    have x0₃ : s₃.gpr .x0 = W := by
      rw [g₃ _ (by decide), g₂ _ (by decide) (by decide) (by decide) (by decide), hp.x0]
    obtain ⟨s₄, run₄, m₄, g₄, sp₄, rd₄, wr₄⟩ := VG.Proof.CmacAes.AArch64.xor2_ok s₃ .x5 .x0 .x5 2048 256 2048
      (P := C) (Q := W + BitVec.ofNat 64 256) (C := C) (by decide) (by decide) (by decide)
      (by rw [x5₃, hC]) (by rw [x5₃, ← hC, Offset.add_add]) (by rw [x0₃]) (by rw [x0₃, Offset.add_add])
      (by rw [x5₃, hC]) (by rw [x5₃, ← hC, Offset.add_add])
      ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
      (by rw [rd₃, wr₃, rd₂, wr₂, ← hC]; exact VG.Proof.CmacAes.AArch64.wr_in (hp.inScr (d := 2048) (n := 8) (by decide)))
      (by rw [rd₃, wr₃, rd₂, wr₂, ← hC, Offset.add_add]; exact VG.Proof.CmacAes.AArch64.wr_in (hp.inScr (d := 2056) (n := 8) (by decide)))
      (by rw [rd₃, wr₃, rd₂, wr₂]; exact hp.inKey (d := 256) (n := 8) (by decide))
      (by rw [rd₃, wr₃, rd₂, wr₂, Offset.add_add]; exact hp.inKey (d := 264) (n := 8) (by decide))
      (by rw [wr₃, wr₂, ← hC]; exact hp.inScr (d := 2048) (n := 8) (by decide))
      (by rw [wr₃, wr₂, ← hC, Offset.add_add]; exact hp.inScr (d := 2056) (n := 8) (by decide))
    refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
    have gg (r : Reg) (h₁ : r ≠ .x6) (h₂ : r ≠ .x7) (h₃ : r ≠ .x8) (h₄ : r ≠ .x9) (h₅ : r ≠ .x10) :
        s₄.gpr r = s₀.gpr r := by rw [g₄ r h₄ h₅, g₃ r h₄, g₂ r h₁ h₂ h₃ h₄]
    have hlen : (Spec.Aes.bytesAt s₀.mem P L).length = L := Proof.Cmac.bytesAt_length _ _ _
    have fW : Frame [⟨C, 16⟩] (writeBytes (Proof.Cmac.zero2 s₀.mem C) C (Spec.Aes.bytesAt s₀.mem P L)) s₃.mem := by
      rw [m₃, m₂]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
    have fB : Frame [⟨C, 16⟩] (Proof.Cmac.zero2 s₀.mem C)
        (writeBytes (Proof.Cmac.zero2 s₀.mem C) C (Spec.Aes.bytesAt s₀.mem P L)) :=
      writeBytes_frame _ _ _ (by
        rw [hlen]; simpa using Offset.contains_base C (d := 0) (n := L) (k := 16) (by omega) (by decide))
    have f₃ : Frame [⟨C, 16⟩] s₀.mem s₃.mem := (fz.trans fB).trans fW
    have k2 : Spec.Aes.bytesAt s₃.mem (W + BitVec.ofNat 64 256) 16 =
        Spec.Aes.bytesAt s₀.mem (W + BitVec.ofNat 64 256) 16 :=
      Proof.Cmac.bytesAt_frame16 f₃ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dKC 256 16 (by decide)
    have pad : Spec.Aes.bytesAt s₃.mem C 16 =
        Spec.Aes.bytesAt s₀.mem P L ++ [0x80] ++ Spec.Cmac.zeros (16 - L - 1) := by
      have := Proof.Cmac.padded_bytes (Proof.Cmac.zero2 s₀.mem C) C (Spec.Aes.bytesAt s₀.mem P L)
        (by rw [hlen]; exact hL) (Proof.Cmac.zero2_bytes _ _)
      rw [hlen] at this
      rw [m₃, m₂]; exact this
    refine ⟨by rw [gg _ (by decide) (by decide) (by decide) (by decide) (by decide), hp.x0],
      by rw [gg _ (by decide) (by decide) (by decide) (by decide) (by decide), hp.x2],
      by rw [gg _ (by decide) (by decide) (by decide) (by decide) (by decide), hp.x5],
      gg _ (by decide) (by decide) (by decide) (by decide) (by decide),
      fun r hr => gg r (VG.Proof.CmacAes.AArch64.not_x6 hr) (VG.Proof.CmacAes.AArch64.not_x7 hr) (VG.Proof.CmacAes.AArch64.not_x8 hr) (VG.Proof.CmacAes.AArch64.not_x9 hr) (VG.Proof.CmacAes.AArch64.not_x10 hr),
      by rw [sp₄, sp₃, sp₂], by rw [rd₄, rd₃, rd₂], by rw [wr₄, wr₃, wr₂], ?_, ?_⟩
    · rw [m₄, hC]; exact f₃.trans (Proof.Cmac.xor2Mem_frame _ _ _ _)
    · rw [m₄, hC, Proof.Cmac.xor2Mem_bytes, pad, k2]
      · simp only [VG.Proof.CmacAes.AArch64.mn, Spec.Cmac.lastBlock, hlen, show L ≠ 16 by omega, ite_false]
        exact Proof.Cmac.xor_comm _ _
      · simpa using Offset.disjoint C (d := 0) (n := 8) (e := 8) (k := 8) (by decide) (by decide) (by decide)
      · rw [Offset.add_add]
        exact (dKC 264 8 (by decide)).symm.sub_left (Region.sub_prefix (by decide))

/-! ## Up to the call -/

/-- What the code before the call leaves. -/
structure FMid (s₀ : State) (W St P S : Addr) (L R : Nat) (s : State) : Prop where
  pre : VG.Proof.CmacAes.AArch64.CallPre s W (S + BitVec.ofNat 64 2048) St S R
  blk : Spec.Aes.bytesAt s.mem (S + BitVec.ofNat 64 2048) 16 =
    Spec.Cmac.xor (VG.Proof.CmacAes.AArch64.mn s₀.mem W P L) (Spec.Aes.bytesAt s₀.mem St 16)
  frame : Frame [⟨S + BitVec.ofNat 64 2048, 16⟩, ⟨St, 16⟩, ⟨S + BitVec.ofNat 64 2064, 16⟩] s₀.mem s.mem
  slot19 : s.mem.readW (S + BitVec.ofNat 64 2064) 64 = s₀.gpr .x19
  slot30 : s.mem.readW (S + BitVec.ofNat 64 2072) 64 = s₀.gpr .x30
  x19 : s.gpr .x19 = S
  saved : ∀ r ∈ preserved, r ≠ .x19 → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem finArgs_wp {s₀ : State} {W St P S : Addr} {L R : Nat} (hp : VG.Proof.CmacAes.AArch64.FPre s₀ W St P S L R) {s : State}
    (h : VG.Proof.CmacAes.AArch64.BPost s₀ W St P S L s) : WP isa (.block finArgs) s (VG.Proof.CmacAes.AArch64.FMid s₀ W St P S L R) := by
  have sw := hp.scr_wrap
  have tw := hp.st_wrap
  rw [VG.Proof.CmacAes.AArch64.finArgs_eq, WP.block_append_iff]
  have hRegs : s.rd ++ s.wr = [⟨W, 272⟩, ⟨P, L⟩, ⟨St, 16⟩, ⟨S, 2176⟩] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have inC (d : Nat) (hd : d + 8 ≤ 2176) : InRegions s.wr (S + BitVec.ofNat 64 d) 8 := by
    rw [h.wr]; exact hp.inScr (by omega)
  have inSt (d : Nat) (hd : d + 8 ≤ 16) : InRegions s.wr (St + BitVec.ofNat 64 d) 8 := by
    rw [h.wr, hp.wr]; exact VG.Proof.CmacAes.AArch64.in_rw (r := ⟨St, 16⟩) (by simp) (Offset.contains_base _ hd (by omega))
  obtain ⟨s₁, run₁, m₁, g₁, sp₁, rd₁, wr₁⟩ := VG.Proof.CmacAes.AArch64.xor2_ok s .x5 .x2 .x5 2048 0 2048
    (P := S + BitVec.ofNat 64 2048) (Q := St) (C := S + BitVec.ofNat 64 2048) (by decide) (by decide) (by decide)
    (by rw [h.x5]) (by rw [h.x5, Offset.add_add]) (by rw [h.x2, VG.Proof.CmacAes.AArch64.k0]) (by rw [h.x2])
    (by rw [h.x5]) (by rw [h.x5, Offset.add_add]) ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
    (VG.Proof.CmacAes.AArch64.wr_in (inC 2048 (by decide))) (by rw [Offset.add_add]; exact VG.Proof.CmacAes.AArch64.wr_in (inC 2056 (by decide)))
    (by simpa using VG.Proof.CmacAes.AArch64.wr_in (inSt 0 (by decide))) (VG.Proof.CmacAes.AArch64.wr_in (inSt 8 (by decide)))
    (inC 2048 (by decide)) (by rw [Offset.add_add]; exact inC 2056 (by decide))
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain ⟨s₂, run₂, m₂, x3₂, x2₂, x4₂, x19₂, g₂, sp₂, rd₂, wr₂⟩ := VG.Proof.CmacAes.AArch64.args_ok s₁ (D := St) (S := S)
    (by rw [g₁ _ (by decide) (by decide), h.x2]) (by rw [g₁ _ (by decide) (by decide), h.x5])
    (by rw [wr₁]; exact inSt 0 (by decide)) (by rw [wr₁]; exact inSt 8 (by decide))
    (by rw [wr₁]; exact inC 2064 (by decide)) (by rw [wr₁]; exact inC 2072 (by decide))
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have g (r : Reg) (h₁ : r ≠ .x2) (h₂ : r ≠ .x3) (h₃ : r ≠ .x4) (h₄ : r ≠ .x9) (h₅ : r ≠ .x19) (h₆ : r ≠ .x10) :
      s₂.gpr r = s.gpr r := by
    rw [g₂ r h₁ h₂ h₃ h₄ h₅, g₁ r h₄ h₆]
  have dCSt : (⟨S + BitVec.ofNat 64 2048, 16⟩ : Region).Disjoint ⟨St, 16⟩ :=
    hp.st_scr.symm.sub_left (FPre.scrD (by decide))
  have dSlSt : (⟨S + BitVec.ofNat 64 2064, 16⟩ : Region).Disjoint ⟨St, 16⟩ :=
    hp.st_scr.symm.sub_left (FPre.scrD (by decide))
  have dSlC : (⟨S + BitVec.ofNat 64 2064, 16⟩ : Region).Disjoint ⟨S + BitVec.ofNat 64 2048, 16⟩ :=
    Offset.disjoint S (by decide) (by omega) (by omega)
  -- The memory: the state zeroed, then the two slots.
  obtain ⟨Z, hZ⟩ : ∃ Z, (s₁.mem.writeW (St + BitVec.ofNat 64 0) (0 : BitVec 64)).writeW (St + BitVec.ofNat 64 8)
      (0 : BitVec 64) = Z := ⟨_, rfl⟩
  have e72 : S + BitVec.ofNat 64 2072 = S + BitVec.ofNat 64 2064 + BitVec.ofNat 64 8 :=
    (Offset.add_add_eq S (a := 2064) (b := 8) (c := 2072) rfl).symm
  have fSl : Frame [⟨S + BitVec.ofNat 64 2064, 16⟩] Z s₂.mem := by
    rw [m₂, hZ, e72]; exact Proof.Cmac.frame_store2 _ _ _
  have fZ : Frame [⟨St, 16⟩] s₁.mem Z := by rw [← hZ]; exact VG.Proof.CmacAes.AArch64.frame_store2' _ _ _
  have stS : Spec.Aes.bytesAt s.mem St 16 = Spec.Aes.bytesAt s₀.mem St 16 :=
    Proof.Cmac.bytesAt_frame16 h.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dCSt.symm
  have hR := hp.rounds
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [rd₂, rd₁, h.rd], by rw [wr₂, wr₁, h.wr]⟩
  · exact
    { x0 := by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.x0]
      x1 := by
        rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.x1]
        apply BitVec.eq_of_toNat_eq; simp [hp.x1]; omega
      x2 := x2₂
      x3 := x3₂
      x4 := x4₂
      x5 := by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.x5]
      rounds := hR
      wc := (hp.key_scr.sub_left (Region.sub_prefix (by decide))).sub_right (FPre.scrD (by decide))
      wd := hp.key_st.sub_left (Region.sub_prefix (by decide))
      ws := (hp.key_scr.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
      cd := dCSt
      cs := Offset.disjoint_base _ (by decide) (by omega)
      ds := hp.st_scr.sub_right (Region.sub_prefix (by decide))
      wrap := hp.st_wrap
      reads := by
        rw [rd₂, wr₂, rd₁, wr₁, hRegs]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact ⟨⟨W, 272⟩, by simp, 0, by simp, by simp⟩
        · exact ⟨⟨S, 2176⟩, by simp, 2048, rfl, by simp⟩
        · exact ⟨⟨St, 16⟩, by simp, 0, by simp, by simp⟩
        · exact ⟨⟨S, 2176⟩, by simp, 0, by simp, by simp⟩
      writes := by
        rw [wr₂, wr₁, h.wr, hp.wr]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨⟨S, 2176⟩, by simp, 2048, rfl, by simp⟩
        · exact ⟨⟨St, 16⟩, by simp, 0, by simp, by simp⟩
        · exact ⟨⟨S, 2176⟩, by simp, 0, by simp, by simp⟩
      zero := by
        rw [Proof.Cmac.bytesAt_frame16 fSl (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact dSlSt.symm), ← hZ, VG.Proof.CmacAes.AArch64.k0,
          Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_zero, Proof.Cmac.zeros_8_8] }
  · rw [Proof.Cmac.bytesAt_frame16 fSl (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dSlC.symm),
      Proof.Cmac.bytesAt_frame16 fZ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dCSt),
      m₁, Proof.Cmac.xor2Mem_bytes, h.blk, stS]
    · simpa using Offset.disjoint (S + BitVec.ofNat 64 2048) (d := 0) (n := 8) (e := 8) (k := 8) (by decide)
        (by decide) (by decide)
    · exact (dCSt.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base _ (by decide))
  · refine (((h.frame.trans (m₁ ▸ Proof.Cmac.xor2Mem_frame _ _ _ _)).mono (by simp)).trans
      (fZ.mono (by simp))).trans (fSl.mono (by simp))
  · rw [m₂, VG.Proof.CmacAes.AArch64.readW_writeW_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64,
      g₁ _ (by decide) (by decide), h.saved _ (by simp [preserved])]
  · rw [m₂, Mem.readW_writeW_self64, g₁ _ (by decide) (by decide), h.saved _ (by simp [preserved])]
  · exact x19₂
  · intro r hr h19
    have n2 : r ≠ .x2 := by rintro rfl; simp [preserved] at hr
    have n3 : r ≠ .x3 := by rintro rfl; simp [preserved] at hr
    have n4 : r ≠ .x4 := by rintro rfl; simp [preserved] at hr
    rw [g r n2 n3 n4 (VG.Proof.CmacAes.AArch64.not_x9 hr) h19 (VG.Proof.CmacAes.AArch64.not_x10 hr), h.saved r hr]
  · rw [sp₂, sp₁, h.sp]

theorem finPre_wp {s₀ : State} {W St P S : Addr} {L R : Nat} (hp : VG.Proof.CmacAes.AArch64.FPre s₀ W St P S L R) :
    WP isa finPre s₀ (VG.Proof.CmacAes.AArch64.FMid s₀ W St P S L R) := by
  have h4 : s₀.gpr .x4 = BitVec.ofNat 64 L := by rw [← hp.x4]; apply BitVec.eq_of_toNat_eq; simp
  obtain ⟨s₁, run₁, ev₁, g₁, sp₁, m₁, rd₁, wr₁⟩ := VG.Proof.CmacAes.AArch64.sub16_ok s₀ h4 hp.len
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (Q := VG.Proof.CmacAes.AArch64.BPost s₀ W St P S L) ?_ fun _ h => VG.Proof.CmacAes.AArch64.finArgs_wp hp h)
  by_cases hL : L = 16
  · exact WP.ite true (by rw [ev₁]; simp [hL]) (fun _ => VG.Proof.CmacAes.AArch64.full_wp hp hL g₁ m₁ sp₁ rd₁ wr₁)
      (fun h => by cases h)
  · exact WP.ite false (by rw [ev₁]; simp [hL]) (fun h => by cases h)
      (fun _ => VG.Proof.CmacAes.AArch64.partial_wp hp (by have := hp.len; omega) g₁ m₁ sp₁ rd₁ wr₁)

theorem restoreF_ok (s : State) {B : Addr} (hb : s.gpr .x19 = B)
    (r₁ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 2072) 8)
    (r₂ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 2064) 8) :
    ∃ s', runBlock isa [.ldr .x .x30 .x19 2072, .ldr .x .x19 .x19 2064] s = some s' ∧
      s'.gpr .x30 = s.mem.readW (B + BitVec.ofNat 64 2072) 64 ∧
      s'.gpr .x19 = s.mem.readW (B + BitVec.ofNat 64 2064) 64 ∧
      (∀ r, r ≠ .x19 → r ≠ .x30 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul, Nat.reduceMod, and_self, runBlock_cons, runStep_some, runBlock_nil, exec, addr,
      State.load, Size.bytes, Size.bits, gpr_write, mem_write, rd_write, wr_write,
      Option.bind_some, Option.map_some, hb, r₁, r₂]
    rfl, ?_⟩
  refine ⟨by simp [gpr_write, Mem.readW], by simp [gpr_write, Mem.readW],
    fun r h₁ h₂ => by simp [gpr_write, h₁, h₂], rfl, rfl⟩

theorem finalize_wp (v : Ctr32Impl) {s₀ : State} (h0 : finalizeAArch64.pre s₀) :
    WP isa (finalize v.callee) s₀ fun s' => GprAbi s₀ s' ∧ finalizeAArch64.post s₀ s' := by
  have hp := FPre.of h0
  generalize s₀.gpr .x0 = W at hp
  generalize s₀.gpr .x2 = St at hp
  generalize s₀.gpr .x3 = P at hp
  generalize s₀.gpr .x5 = S at hp
  generalize (s₀.gpr .x4).toNat = L at hp
  generalize (s₀.gpr .x1).toNat = R at hp
  have hR := hp.rounds
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with h | h | h <;> omega
  have sw := hp.scr_wrap
  refine WP.seq (WP.mono (VG.Proof.CmacAes.AArch64.finPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (VG.Proof.CmacAes.AArch64.ctr_call v h₁.pre) fun s₂ h₂ => ?_)
  have x19₂ : s₂.gpr .x19 = S := by rw [h₂.saved .x19 (by simp [preserved]) (by decide), h₁.x19]
  have rdwr₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr]
  obtain ⟨s₃, run₃, x30₃, x19₃, g₃, sp₃, mem₃⟩ := VG.Proof.CmacAes.AArch64.restoreF_ok s₂ x19₂
    (by rw [rdwr₂]; exact VG.Proof.CmacAes.AArch64.wr_in (hp.inScr (d := 2072) (n := 8) (by decide)))
    (by rw [rdwr₂]; exact VG.Proof.CmacAes.AArch64.wr_in (hp.inScr (d := 2064) (n := 8) (by decide)))
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  -- The slots, which the call does not write.
  have slots (d : Nat) (h₁' : 2064 ≤ d) (h₂' : d + 8 ≤ 2080) :
      s₂.mem.readW (S + BitVec.ofNat 64 d) 64 = s₁.mem.readW (S + BitVec.ofNat 64 d) 64 := by
    refine h₂.frame.readW (r := ⟨S + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint S (by omega) (by omega) (by omega)
    · exact (hp.st_scr.symm.sub_left (FPre.scrD (by omega)))
    · exact Offset.disjoint_base _ (by omega) (by omega)
  have big : Frame [⟨St, 16⟩, ⟨S, 2176⟩] s₀.mem s₂.mem := by
    refine (h₁.frame.sub fun r hr => ?_).trans (h₂.frame.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨⟨S, 2176⟩, by simp, FPre.scrD (by decide)⟩
      · exact ⟨⟨St, 16⟩, by simp, fun _ h => h⟩
      · exact ⟨⟨S, 2176⟩, by simp, FPre.scrD (by decide)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨⟨S, 2176⟩, by simp, FPre.scrD (by decide)⟩
      · exact ⟨⟨St, 16⟩, by simp, fun _ h => h⟩
      · exact ⟨⟨S, 2176⟩, by simp, Region.sub_prefix (by decide)⟩
  have sch : Spec.Aes.bytesAt s₁.mem W (16 * (R + 1)) = Spec.Aes.bytesAt s₀.mem W (16 * (R + 1)) :=
    Proof.Cmac.bytesAt_frame h₁.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (hp.key_scr.sub_left (Region.sub_prefix (by omega))).sub_right (FPre.scrD (by decide))
      · exact hp.key_st.sub_left (Region.sub_prefix (by omega))
      · exact (hp.key_scr.sub_left (Region.sub_prefix (by omega))).sub_right (FPre.scrD (by decide))) (by omega)
  refine ⟨⟨fun r hr => ?_, by rw [sp₃, h₂.sp, h₁.sp]⟩, ?_⟩
  · by_cases h19 : r = .x19
    · subst h19; rw [x19₃, slots 2064 (by decide) (by decide), h₁.slot19]
    by_cases h30 : r = .x30
    · subst h30; rw [x30₃, slots 2072 (by decide) (by decide), h₁.slot30]
    rw [g₃ r h19 h30, h₂.saved r hr h30, h₁.saved r hr h19]
  · intro hk msg hm hne hst
    rw [hp.x0, hp.x1] at hk hst ⊢
    rw [hp.x2] at hst ⊢
    rw [hp.x4] at hne
    rw [hp.x3, hp.x4]
    obtain ⟨e1, e2⟩ := Proof.Cmac.k1k2 (Proof.Cmac.subkeys_aes_length _ _) hk
    rw [mem₃, h₂.out, sch, h₁.blk, VG.Proof.CmacAes.AArch64.mn, e1, e2, hst,
      Proof.Cmac.macFull_split _ hm (by rw [Proof.Cmac.bytesAt_length]; exact hp.len)
        (by rw [Proof.Cmac.bytesAt_length]; exact hne), Proof.Cmac.xor_comm]

end VG.Proof.CmacAes.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.AArch64.UpdateCT`. -/
section

/-!
# AES-CMAC on AArch64: `vg_cmac_aes_update` is constant time

Two runs from states that agree on the public arguments are related piece by
piece (`RelCT`): the taint analysis covers the code between the calls, from
the registers the correctness proof pins to the public arguments (`LInv`), and
each call of `vg_aes_ctr32` is constant time by its own proof (`ctr_rel`).
-/

namespace VG.Proof.CmacAes.AArch64

open VG VG.AArch64 VG.Impl.CmacAes.AArch64
open VG.Proof.Aes.AArch64 (Ctr32Impl)

/-- States agree on the registers `rs` and the stack pointer. -/
theorem agree_of {rs : List Reg} {s₁ s₂ : State} (hsp : s₁.sp = s₂.sp)
    (h : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) : VG.AArch64.Taint.Agree (Taint.ofRegs rs) s₁ s₂ :=
  ⟨hsp, fun r hr => h r (VG.AArch64.Taint.mem_ofRegs.mp hr)⟩

section
variable {s₀ s₀' : State} (hq : updateAArch64.pub s₀ s₀')
include hq

theorem pub_W : VG.Proof.CmacAes.AArch64.W s₀ = VG.Proof.CmacAes.AArch64.W s₀' := hq.1
theorem pub_x1 : s₀.gpr .x1 = s₀'.gpr .x1 := hq.2.1
theorem pub_R : VG.Proof.CmacAes.AArch64.R s₀ = VG.Proof.CmacAes.AArch64.R s₀' := by rw [VG.Proof.CmacAes.AArch64.R, VG.Proof.CmacAes.AArch64.R, VG.Proof.CmacAes.AArch64.pub_x1 hq]
theorem pub_St : VG.Proof.CmacAes.AArch64.St s₀ = VG.Proof.CmacAes.AArch64.St s₀' := hq.2.2.1
theorem pub_Dp : VG.Proof.CmacAes.AArch64.Dp s₀ = VG.Proof.CmacAes.AArch64.Dp s₀' := hq.2.2.2.1
theorem pub_N : VG.Proof.CmacAes.AArch64.N s₀ = VG.Proof.CmacAes.AArch64.N s₀' := by rw [VG.Proof.CmacAes.AArch64.N, VG.Proof.CmacAes.AArch64.N, hq.2.2.2.2.1]
theorem pub_S : VG.Proof.CmacAes.AArch64.S s₀ = VG.Proof.CmacAes.AArch64.S s₀' := hq.2.2.2.2.2.1
theorem pub_sp : s₀.sp = s₀'.sp := hq.2.2.2.2.2.2

/-- The registers the invariant pins agree in both runs. -/
theorem LInv.agree {k : Nat} {s₁ s₂ : State} (h₁ : VG.Proof.CmacAes.AArch64.LInv s₀ k s₁) (h₂ : VG.Proof.CmacAes.AArch64.LInv s₀' k s₂) :
    VG.AArch64.Taint.Agree (Taint.ofRegs [.x19, .x20, .x21, .x22, .x23, .x24]) s₁ s₂ := by
  refine VG.Proof.CmacAes.AArch64.agree_of (by rw [h₁.sp, h₂.sp, VG.Proof.CmacAes.AArch64.pub_sp hq]) fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h₁.x19, h₂.x19, VG.Proof.CmacAes.AArch64.pub_W hq]
  · rw [h₁.x20, h₂.x20, VG.Proof.CmacAes.AArch64.pub_x1 hq]
  · rw [h₁.x21, h₂.x21, VG.Proof.CmacAes.AArch64.pub_St hq]
  · rw [h₁.x22, h₂.x22, VG.Proof.CmacAes.AArch64.pub_Dp hq]
  · rw [h₁.x23, h₂.x23, VG.Proof.CmacAes.AArch64.pub_N hq]
  · rw [h₁.x24, h₂.x24, VG.Proof.CmacAes.AArch64.pub_S hq]

end

/-! ## One block -/

/-- What is known between the code before the call and the call. -/
structure Mid (s₀ : State) (k : Nat) (s : State) : Prop where
  pre : VG.Proof.CmacAes.AArch64.CallPre s (VG.Proof.CmacAes.AArch64.W s₀) (VG.Proof.CmacAes.AArch64.S s₀ + BitVec.ofNat 64 2048) (VG.Proof.CmacAes.AArch64.St s₀) (VG.Proof.CmacAes.AArch64.S s₀) (VG.Proof.CmacAes.AArch64.R s₀)
  x22 : s.gpr .x22 = VG.Proof.CmacAes.AArch64.Dp s₀ + BitVec.ofNat 64 (16 * k)
  x23 : s.gpr .x23 = BitVec.ofNat 64 (VG.Proof.CmacAes.AArch64.N s₀ - k)
  sp : s.sp = s₀.sp

theorem bodyMid_wp {s₀ : State} (hp : VG.Proof.CmacAes.AArch64.UPre s₀) {k : Nat} (hk : k < VG.Proof.CmacAes.AArch64.N s₀) {s : State} (h : VG.Proof.CmacAes.AArch64.LInv s₀ k s) :
    WP isa (.block (chainIn ++ updArgs)) s (VG.Proof.CmacAes.AArch64.Mid s₀ k) :=
  WP.mono (VG.Proof.CmacAes.AArch64.bodyA_wp hp hk h) fun _ hb =>
    ⟨hb.pre, by rw [hb.saved .x22 (by simp [preserved]), h.x22],
      by rw [hb.saved .x23 (by simp [preserved]), h.x23], by rw [hb.sp, h.sp]⟩

/-- What is known after the call. -/
structure After (s₀ : State) (k : Nat) (s : State) : Prop where
  x22 : s.gpr .x22 = VG.Proof.CmacAes.AArch64.Dp s₀ + BitVec.ofNat 64 (16 * k)
  x23 : s.gpr .x23 = BitVec.ofNat 64 (VG.Proof.CmacAes.AArch64.N s₀ - k)
  sp : s.sp = s₀.sp

theorem body_ct (v : Ctr32Impl) {s₀ s₀' : State} (hp : VG.Proof.CmacAes.AArch64.UPre s₀) (hp' : VG.Proof.CmacAes.AArch64.UPre s₀')
    (hq : updateAArch64.pub s₀ s₀') (k : Nat) :
    RelCT isa (fun s₁ s₂ => k < VG.Proof.CmacAes.AArch64.N s₀ ∧ VG.Proof.CmacAes.AArch64.LInv s₀ k s₁ ∧ VG.Proof.CmacAes.AArch64.LInv s₀' k s₂) (VG.Impl.CmacAes.AArch64.body v.callee) fun _ _ => True := by
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x22, .x23, .x24])
      (.block (chainIn ++ updArgs)) h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.x22, .x23]) (.block advance) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun s₁ s₂ => k < VG.Proof.CmacAes.AArch64.N s₀ ∧ VG.Proof.CmacAes.AArch64.LInv s₀ k s₁ ∧ VG.Proof.CmacAes.AArch64.LInv s₀' k s₂) _
    (fun _ _ h => LInv.agree hq h.2.1 h.2.2) hA).wp
    (F₁ := VG.Proof.CmacAes.AArch64.Mid s₀ k) (F₂ := VG.Proof.CmacAes.AArch64.Mid s₀' k) fun _ _ h =>
      ⟨VG.Proof.CmacAes.AArch64.bodyMid_wp hp h.1 h.2.1, VG.Proof.CmacAes.AArch64.bodyMid_wp hp' (by rw [← VG.Proof.CmacAes.AArch64.pub_N hq]; exact h.1) h.2.2⟩
  have c := (VG.Proof.CmacAes.AArch64.ctr_rel v (P := fun s₁ s₂ => VG.Proof.CmacAes.AArch64.Mid s₀ k s₁ ∧ VG.Proof.CmacAes.AArch64.Mid s₀' k s₂) fun s₁ s₂ h =>
      ⟨h.1.pre, by rw [VG.Proof.CmacAes.AArch64.pub_W hq, VG.Proof.CmacAes.AArch64.pub_S hq, VG.Proof.CmacAes.AArch64.pub_St hq, VG.Proof.CmacAes.AArch64.pub_R hq]; exact h.2.pre,
        by rw [h.1.sp, h.2.sp, VG.Proof.CmacAes.AArch64.pub_sp hq]⟩).wp
    (F₁ := VG.Proof.CmacAes.AArch64.After s₀ k) (F₂ := VG.Proof.CmacAes.AArch64.After s₀' k) fun s₁ s₂ h =>
      ⟨WP.mono (VG.Proof.CmacAes.AArch64.ctr_call v h.1.pre) fun _ hc =>
        ⟨by rw [hc.saved .x22 (by simp [preserved]) (by decide), h.1.x22],
          by rw [hc.saved .x23 (by simp [preserved]) (by decide), h.1.x23], by rw [hc.sp, h.1.sp]⟩,
       WP.mono (VG.Proof.CmacAes.AArch64.ctr_call v h.2.pre) fun _ hc =>
        ⟨by rw [hc.saved .x22 (by simp [preserved]) (by decide), h.2.x22],
          by rw [hc.saved .x23 (by simp [preserved]) (by decide), h.2.x23], by rw [hc.sp, h.2.sp]⟩⟩
  have b := RelCT.taint (A := taint) (P := fun s₁ s₂ => VG.Proof.CmacAes.AArch64.After s₀ k s₁ ∧ VG.Proof.CmacAes.AArch64.After s₀' k s₂) _
    (fun s₁ s₂ h => VG.Proof.CmacAes.AArch64.agree_of (by rw [h.1.sp, h.2.sp, VG.Proof.CmacAes.AArch64.pub_sp hq]) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.x22, h.2.x22, VG.Proof.CmacAes.AArch64.pub_Dp hq]
      · rw [h.1.x23, h.2.x23, VG.Proof.CmacAes.AArch64.pub_N hq]) hB
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((c.mono (fun _ _ h => h) fun _ _ h => h.2).seq b)

/-! ## The loop -/

/-- The loop's relation, with the number of iterations left. -/
def LRel (s₀ s₀' : State) (n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ k, n = VG.Proof.CmacAes.AArch64.N s₀ - k ∧ k < VG.Proof.CmacAes.AArch64.N s₀ ∧ VG.Proof.CmacAes.AArch64.LInv s₀ k s₁ ∧ VG.Proof.CmacAes.AArch64.LInv s₀' k s₂

theorem loop_ct (v : Ctr32Impl) {s₀ s₀' : State} (hp : VG.Proof.CmacAes.AArch64.UPre s₀) (hp' : VG.Proof.CmacAes.AArch64.UPre s₀')
    (hq : updateAArch64.pub s₀ s₀') (n : Nat) :
    RelCT isa (VG.Proof.CmacAes.AArch64.LRel s₀ s₀' n) (.loop (VG.Impl.CmacAes.AArch64.body v.callee) (.nonzero .x .x23))
      fun s₁ s₂ => VG.Proof.CmacAes.AArch64.LInv s₀ (VG.Proof.CmacAes.AArch64.N s₀) s₁ ∧ VG.Proof.CmacAes.AArch64.LInv s₀' (VG.Proof.CmacAes.AArch64.N s₀') s₂ := by
  refine RelCT.loop (M := isa) (VG.Proof.CmacAes.AArch64.LRel s₀ s₀') (fun n => ?_) n
  have hN := VG.Proof.CmacAes.AArch64.pub_N hq
  refine (RelCT.exists_ fun k => ?_).mono (fun s₁ s₂ (h : VG.Proof.CmacAes.AArch64.LRel s₀ s₀' n s₁ s₂) => h) fun _ _ h => h
  by_cases hn : n = VG.Proof.CmacAes.AArch64.N s₀ - k
  swap
  · exact RelCT.of_false fun _ _ h => hn h.1
  subst hn
  by_cases hk : k < VG.Proof.CmacAes.AArch64.N s₀
  swap
  · exact RelCT.of_false fun _ _ h => hk h.2.1
  have ct := (VG.Proof.CmacAes.AArch64.body_ct v hp hp' hq k).wp
    (F₁ := VG.Proof.CmacAes.AArch64.LInv s₀ (k + 1)) (F₂ := VG.Proof.CmacAes.AArch64.LInv s₀' (k + 1))
    fun _ _ h => ⟨VG.Proof.CmacAes.AArch64.body_ok v hp h.1 h.2.1, VG.Proof.CmacAes.AArch64.body_ok v hp' (by rw [← hN]; exact h.1) h.2.2⟩
  refine ct.mono (fun _ _ h => h.2) fun s₁ s₂ ⟨_, l₁, l₂⟩ => ?_
  have hb : VG.Proof.CmacAes.AArch64.N s₀ < 2 ^ 64 := (s₀.gpr .x4).isLt
  have e₁ := VG.Proof.CmacAes.AArch64.eval_x23 (x := VG.Proof.CmacAes.AArch64.N s₀ - (k + 1)) (by omega) l₁.x23
  have e₂ := VG.Proof.CmacAes.AArch64.eval_x23 (x := VG.Proof.CmacAes.AArch64.N s₀ - (k + 1)) (by omega) (by rw [l₂.x23, ← hN])
  refine ⟨by rw [e₁, e₂], fun hf => ?_, fun ht => ?_⟩
  · rw [e₁] at hf
    have h0 : VG.Proof.CmacAes.AArch64.N s₀ = k + 1 := by
      have : VG.Proof.CmacAes.AArch64.N s₀ - (k + 1) = 0 := by simpa using hf
      omega
    exact ⟨h0 ▸ l₁, by rw [← hN, h0]; exact l₂⟩
  · rw [e₁] at ht
    have h0 : VG.Proof.CmacAes.AArch64.N s₀ - (k + 1) ≠ 0 := by simpa using ht
    exact ⟨VG.Proof.CmacAes.AArch64.N s₀ - (k + 1), by omega, k + 1, rfl, by omega, l₁, l₂⟩

/-! ## The whole function -/

theorem update_rel (v : Ctr32Impl) {s₀ s₀' : State} (h0 : updateAArch64.pre s₀)
    (h0' : updateAArch64.pre s₀') (hq : updateAArch64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (update v.callee) fun _ _ => True := by
  have hp := UPre.of h0
  have hp' := UPre.of h0'
  have hN := VG.Proof.CmacAes.AArch64.pub_N hq
  have hb : VG.Proof.CmacAes.AArch64.N s₀ < 2 ^ 64 := (s₀.gpr .x4).isLt
  obtain ⟨_, hpro⟩ : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5])
      (.block (save ++ setup)) h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hepi⟩ : ∃ h, (taint.check (Taint.ofRegs [.x24]) (.block restore) h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hnil⟩ : ∃ h, (taint.check (Taint.ofRegs []) (.block []) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have pro := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hq
      refine VG.Proof.CmacAes.AArch64.agree_of h7 fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption) hpro).wp
    (F₁ := VG.Proof.CmacAes.AArch64.LInv s₀ 0) (F₂ := VG.Proof.CmacAes.AArch64.LInv s₀' 0)
    fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨VG.Proof.CmacAes.AArch64.prologue_wp hp, VG.Proof.CmacAes.AArch64.prologue_wp hp'⟩
  have ev {k : Nat} {s : State} (h : VG.Proof.CmacAes.AArch64.LInv s₀ 0 s) :
      isa.eval (.zero .x .x23) s = some (decide (VG.Proof.CmacAes.AArch64.N s₀ = 0)) :=
    VG.Proof.CmacAes.AArch64.eval_zero_x23 hb (by rw [h.x23]; rfl)
  have ev' {s : State} (h : VG.Proof.CmacAes.AArch64.LInv s₀' 0 s) : isa.eval (.zero .x .x23) s = some (decide (VG.Proof.CmacAes.AArch64.N s₀ = 0)) :=
    VG.Proof.CmacAes.AArch64.eval_zero_x23 hb (by rw [h.x23, ← hN]; rfl)
  have nil := RelCT.taint (A := taint)
    (P := fun a b => (VG.Proof.CmacAes.AArch64.LInv s₀ 0 a ∧ VG.Proof.CmacAes.AArch64.LInv s₀' 0 b) ∧ isa.eval (.zero .x .x23) a = some true) _
    (fun a b h => VG.Proof.CmacAes.AArch64.agree_of (by rw [h.1.1.sp, h.1.2.sp, VG.Proof.CmacAes.AArch64.pub_sp hq]) fun r hr => by simp at hr) hnil
  have mid : RelCT isa (fun a b => VG.Proof.CmacAes.AArch64.LInv s₀ 0 a ∧ VG.Proof.CmacAes.AArch64.LInv s₀' 0 b)
      (.ite (.zero .x .x23) (.block []) (.loop (VG.Impl.CmacAes.AArch64.body v.callee) (.nonzero .x .x23)))
      (fun a b => VG.Proof.CmacAes.AArch64.LInv s₀ (VG.Proof.CmacAes.AArch64.N s₀) a ∧ VG.Proof.CmacAes.AArch64.LInv s₀' (VG.Proof.CmacAes.AArch64.N s₀') b) := by
    refine RelCT.ite (fun a b h => by rw [ev (k := 0) h.1, ev' h.2]) ?_ ?_
    · refine (nil.wp (F₁ := VG.Proof.CmacAes.AArch64.LInv s₀ (VG.Proof.CmacAes.AArch64.N s₀)) (F₂ := VG.Proof.CmacAes.AArch64.LInv s₀' (VG.Proof.CmacAes.AArch64.N s₀')) fun a b h => ?_).mono
        (fun _ _ h => h) fun _ _ h => h.2
      have h0 : VG.Proof.CmacAes.AArch64.N s₀ = 0 := by
        have := h.2; rw [ev (k := 0) h.1.1] at this; simpa using this
      exact ⟨WP.block_nil (h0 ▸ h.1.1), WP.block_nil (by rw [← hN, h0]; exact h.1.2)⟩
    · refine (VG.Proof.CmacAes.AArch64.loop_ct v hp hp' hq (VG.Proof.CmacAes.AArch64.N s₀ - 0)).mono (fun a b h => ⟨0, rfl, ?_, h.1.1, h.1.2⟩)
        fun _ _ h => h
      have := h.2; rw [ev (k := 0) h.1.1] at this
      have : VG.Proof.CmacAes.AArch64.N s₀ ≠ 0 := by simpa using this
      omega
  have epi := RelCT.taint (A := taint) (P := fun a b => VG.Proof.CmacAes.AArch64.LInv s₀ (VG.Proof.CmacAes.AArch64.N s₀) a ∧ VG.Proof.CmacAes.AArch64.LInv s₀' (VG.Proof.CmacAes.AArch64.N s₀') b) _
    (fun a b h => VG.Proof.CmacAes.AArch64.agree_of (by rw [h.1.sp, h.2.sp, VG.Proof.CmacAes.AArch64.pub_sp hq]) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [h.1.x24, h.2.x24, VG.Proof.CmacAes.AArch64.pub_S hq]) hepi
  exact (pro.mono (fun _ _ h => h) fun _ _ h => h.2).seq (mid.seq epi)

theorem update_ct (v : Ctr32Impl) :
    ConstantTime isa updateAArch64.pre updateAArch64.pub (update v.callee) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (VG.Proof.CmacAes.AArch64.update_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.AArch64.Verified`. -/
section

section

/-!
# AES-CMAC on AArch64: `vg_cmac_aes_subkeys` is constant time

The code before the call and after it is checked by the taint analysis, from
the registers the correctness proof pins (the arguments, then `x19` and
`x20`); the call of `vg_aes_ctr32` is constant time by its own proof
(`ctr_rel`).
-/

namespace VG.Proof.CmacAes.AArch64

open VG VG.AArch64 VG.Impl.CmacAes.AArch64
open VG.Proof.Aes.AArch64 (Ctr32Impl)

/-- What is known between the code before the call and the call. -/
structure SMid (s₀ : State) (W K S : Addr) (R : Nat) (s : State) : Prop where
  pre : VG.Proof.CmacAes.AArch64.CallPre s W (S + BitVec.ofNat 64 2048) K S R
  x19 : s.gpr .x19 = K
  x20 : s.gpr .x20 = S
  sp : s.sp = s₀.sp

theorem smid_wp {s₀ : State} {W K S : Addr} {R : Nat} (hp : VG.Proof.CmacAes.AArch64.SPre s₀ W K S R) :
    WP isa (.block subkeysPre) s₀ (VG.Proof.CmacAes.AArch64.SMid s₀ W K S R) := by
  have sw := hp.scr_wrap
  have kw := hp.k_wrap
  have inS (d : Nat) (h : d + 8 ≤ 2176) : InRegions s₀.wr (s₀.gpr .x3 + BitVec.ofNat 64 d) 8 := by
    rw [hp.wr, hp.x3]; exact VG.Proof.CmacAes.AArch64.in_rw (r := ⟨S, 2176⟩) (by simp) (Offset.contains_base _ h (by omega))
  have inK (d : Nat) (h : d + 8 ≤ 32) : InRegions s₀.wr (s₀.gpr .x2 + BitVec.ofNat 64 d) 8 := by
    rw [hp.wr, hp.x2]; exact VG.Proof.CmacAes.AArch64.in_rw (r := ⟨K, 32⟩) (by simp) (Offset.contains_base _ h (by omega))
  obtain ⟨s₁, run₁, x0₁, x1₁, x2₁, x3₁, x4₁, x5₁, x19₁, x20₁, _, sp₁, mem₁, rd₁, wr₁⟩ :=
    VG.Proof.CmacAes.AArch64.subkeysPre_ok s₀ (inS _ (by decide)) (inS _ (by decide)) (inS _ (by decide)) (inS _ (by decide))
      (inS _ (by decide)) (inK _ (by decide)) (inK _ (by decide))
  exact WP.of_runBlock ⟨s₁, run₁,
    VG.Proof.CmacAes.AArch64.callPre_of hp x0₁ x1₁ x2₁ x3₁ x4₁ x5₁ mem₁ rd₁ wr₁, by rw [x19₁, hp.x2], by rw [x20₁, hp.x3], sp₁⟩

theorem subkeys_rel (v : Ctr32Impl) {s₀ s₀' : State} (h0 : subkeysAArch64.pre s₀)
    (h0' : subkeysAArch64.pre s₀') (hq : subkeysAArch64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (subkeys v.callee) fun _ _ => True := by
  obtain ⟨q1, q2, q3, q4, q5⟩ := hq
  have hp := SPre.of h0
  have hp' : VG.Proof.CmacAes.AArch64.SPre s₀' (s₀.gpr .x0) (s₀.gpr .x2) (s₀.gpr .x3) (s₀.gpr .x1).toNat := by
    rw [q1, q2, q3, q4]; exact SPre.of h0'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3]) (.block subkeysPre) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.x19, .x20]) (.block subkeysPost) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine VG.Proof.CmacAes.AArch64.agree_of q5 fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption) hA).wp
    (F₁ := VG.Proof.CmacAes.AArch64.SMid s₀ _ _ _ _) (F₂ := VG.Proof.CmacAes.AArch64.SMid s₀' _ _ _ _) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨VG.Proof.CmacAes.AArch64.smid_wp hp, VG.Proof.CmacAes.AArch64.smid_wp hp'⟩
  have c := (VG.Proof.CmacAes.AArch64.ctr_rel v (P := fun s₁ s₂ =>
      VG.Proof.CmacAes.AArch64.SMid s₀ (s₀.gpr .x0) (s₀.gpr .x2) (s₀.gpr .x3) (s₀.gpr .x1).toNat s₁ ∧
      VG.Proof.CmacAes.AArch64.SMid s₀' (s₀.gpr .x0) (s₀.gpr .x2) (s₀.gpr .x3) (s₀.gpr .x1).toNat s₂) fun s₁ s₂ h =>
      ⟨h.1.pre, h.2.pre, by rw [h.1.sp, h.2.sp, q5]⟩).wp
    (F₁ := fun (s : State) => s.gpr .x19 = s₀.gpr .x2 ∧ s.gpr .x20 = s₀.gpr .x3 ∧ s.sp = s₀.sp)
    (F₂ := fun (s : State) => s.gpr .x19 = s₀.gpr .x2 ∧ s.gpr .x20 = s₀.gpr .x3 ∧ s.sp = s₀'.sp)
    fun s₁ s₂ h =>
      ⟨WP.mono (VG.Proof.CmacAes.AArch64.ctr_call v h.1.pre) fun _ hc =>
        ⟨by rw [hc.saved .x19 (by simp [preserved]) (by decide), h.1.x19],
          by rw [hc.saved .x20 (by simp [preserved]) (by decide), h.1.x20], by rw [hc.sp, h.1.sp]⟩,
       WP.mono (VG.Proof.CmacAes.AArch64.ctr_call v h.2.pre) fun _ hc =>
        ⟨by rw [hc.saved .x19 (by simp [preserved]) (by decide), h.2.x19],
          by rw [hc.saved .x20 (by simp [preserved]) (by decide), h.2.x20], by rw [hc.sp, h.2.sp]⟩⟩
  have b := RelCT.taint (A := taint)
    (P := fun s₁ s₂ => (s₁.gpr .x19 = s₀.gpr .x2 ∧ s₁.gpr .x20 = s₀.gpr .x3 ∧ s₁.sp = s₀.sp) ∧
      (s₂.gpr .x19 = s₀.gpr .x2 ∧ s₂.gpr .x20 = s₀.gpr .x3 ∧ s₂.sp = s₀'.sp)) _
    (fun s₁ s₂ h => VG.Proof.CmacAes.AArch64.agree_of (by rw [h.1.2.2, h.2.2.2, q5]) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.1, h.2.1]
      · rw [h.1.2.1, h.2.2.1]) hB
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((c.mono (fun _ _ h => h) fun _ _ h => h.2).seq b)

theorem subkeys_ct (v : Ctr32Impl) :
    ConstantTime isa subkeysAArch64.pre subkeysAArch64.pub (subkeys v.callee) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (VG.Proof.CmacAes.AArch64.subkeys_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.AArch64

end

section

/-!
# AES-CMAC on AArch64: `vg_cmac_aes_finalize` is constant time

The code before the call is checked by the taint analysis (its branches and
the copy loop depend only on `last_len`), the call of `vg_aes_ctr32` is
constant time by its own proof (`ctr_rel`), its arguments pinned by the
correctness proof (`FMid`), and the restore after it by the taint analysis
again, from `x19` (the scratch buffer).
-/

namespace VG.Proof.CmacAes.AArch64

open VG VG.AArch64 VG.Impl.CmacAes.AArch64
open VG.Proof.Aes.AArch64 (Ctr32Impl)

theorem finalize_rel (v : Ctr32Impl) {s₀ s₀' : State} (h0 : finalizeAArch64.pre s₀)
    (h0' : finalizeAArch64.pre s₀') (hq : finalizeAArch64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (finalize v.callee) fun _ _ => True := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := hq
  have hp := FPre.of h0
  have hp' : VG.Proof.CmacAes.AArch64.FPre s₀' (s₀.gpr .x0) (s₀.gpr .x2) (s₀.gpr .x3) (s₀.gpr .x5) (s₀.gpr .x4).toNat
      (s₀.gpr .x1).toNat := by
    rw [q1, q2, q3, q4, q5, q6]; exact FPre.of h0'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5]) finPre h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.x19])
      (.block [.ldr .x .x30 .x19 2072, .ldr .x .x19 .x19 2064]) h).isSome = true := ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine VG.Proof.CmacAes.AArch64.agree_of q7 fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption) hA).wp
    (F₁ := VG.Proof.CmacAes.AArch64.FMid s₀ _ _ _ _ _ _) (F₂ := VG.Proof.CmacAes.AArch64.FMid s₀' _ _ _ _ _ _) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨VG.Proof.CmacAes.AArch64.finPre_wp hp, VG.Proof.CmacAes.AArch64.finPre_wp hp'⟩
  have c := (VG.Proof.CmacAes.AArch64.ctr_rel v (P := fun s₁ s₂ =>
      VG.Proof.CmacAes.AArch64.FMid s₀ (s₀.gpr .x0) (s₀.gpr .x2) (s₀.gpr .x3) (s₀.gpr .x5) (s₀.gpr .x4).toNat (s₀.gpr .x1).toNat s₁ ∧
      VG.Proof.CmacAes.AArch64.FMid s₀' (s₀.gpr .x0) (s₀.gpr .x2) (s₀.gpr .x3) (s₀.gpr .x5) (s₀.gpr .x4).toNat (s₀.gpr .x1).toNat s₂)
    fun s₁ s₂ h => ⟨h.1.pre, h.2.pre, by rw [h.1.sp, h.2.sp, q7]⟩).wp
    (F₁ := fun (s : State) => s.gpr .x19 = s₀.gpr .x5 ∧ s.sp = s₀.sp)
    (F₂ := fun (s : State) => s.gpr .x19 = s₀.gpr .x5 ∧ s.sp = s₀'.sp) fun s₁ s₂ h =>
      ⟨WP.mono (VG.Proof.CmacAes.AArch64.ctr_call v h.1.pre) fun _ hc =>
        ⟨by rw [hc.saved .x19 (by simp [preserved]) (by decide), h.1.x19], by rw [hc.sp, h.1.sp]⟩,
       WP.mono (VG.Proof.CmacAes.AArch64.ctr_call v h.2.pre) fun _ hc =>
        ⟨by rw [hc.saved .x19 (by simp [preserved]) (by decide), h.2.x19], by rw [hc.sp, h.2.sp]⟩⟩
  have b := RelCT.taint (A := taint)
    (P := fun s₁ s₂ => (s₁.gpr .x19 = s₀.gpr .x5 ∧ s₁.sp = s₀.sp) ∧ (s₂.gpr .x19 = s₀.gpr .x5 ∧ s₂.sp = s₀'.sp)) _
    (fun s₁ s₂ h => VG.Proof.CmacAes.AArch64.agree_of (by rw [h.1.2, h.2.2, q7]) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [h.1.1, h.2.1]) hB
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((c.mono (fun _ _ h => h) fun _ _ h => h.2).seq b)

theorem finalize_ct (v : Ctr32Impl) :
    ConstantTime isa finalizeAArch64.pre finalizeAArch64.pub (finalize v.callee) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (VG.Proof.CmacAes.AArch64.finalize_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.AArch64

end

/-!
# AES-CMAC on AArch64: `Verified`

Correctness and constant time (for any implementation `v` of `vg_aes_ctr32`),
a state satisfying each precondition, and the shared contracts of
`Spec/Cmac/Contract.lean` (with no stack: the calls keep the return address in
`x30`, which each function saves in the scratch buffer).
-/

namespace VG.Proof.CmacAes.AArch64

open VG VG.AArch64 VG.Impl.CmacAes.AArch64
open VG.Proof.Aes.AArch64 (Ctr32Impl)

theorem update_keepsV (v : Ctr32Impl) : (update v.callee).allInstrs keepsV = true := by
  simp only [update, body, Code.allInstrs, v.keepsV]; decide +kernel

theorem subkeys_keepsV (v : Ctr32Impl) : (subkeys v.callee).allInstrs keepsV = true := by
  simp only [subkeys, Code.allInstrs, v.keepsV]; decide +kernel

theorem finalize_keepsV (v : Ctr32Impl) : (finalize v.callee).allInstrs keepsV = true := by
  simp only [finalize, finPre, partialBlock, copy, Code.allInstrs, v.keepsV]; decide +kernel

theorem update_correct (v : Ctr32Impl) (s : State) (hs : updateAArch64.pre s) :
    ∃ t s', Exec isa (update v.callee) s t s' ∧ abiPreserved s s' ∧ updateAArch64.post s s' :=
  WP.withPreservedV (VG.Proof.CmacAes.AArch64.update_wp v hs) (VG.Proof.CmacAes.AArch64.update_keepsV v)

theorem subkeys_correct (v : Ctr32Impl) (s : State) (hs : subkeysAArch64.pre s) :
    ∃ t s', Exec isa (subkeys v.callee) s t s' ∧ abiPreserved s s' ∧ subkeysAArch64.post s s' :=
  WP.withPreservedV (VG.Proof.CmacAes.AArch64.subkeys_wp v hs) (VG.Proof.CmacAes.AArch64.subkeys_keepsV v)

theorem finalize_correct (v : Ctr32Impl) (s : State) (hs : finalizeAArch64.pre s) :
    ∃ t s', Exec isa (finalize v.callee) s t s' ∧ abiPreserved s s' ∧ finalizeAArch64.post s s' :=
  WP.withPreservedV (VG.Proof.CmacAes.AArch64.finalize_wp v hs) (VG.Proof.CmacAes.AArch64.finalize_keepsV v)

/-- A state satisfying `vg_cmac_aes_update`'s precondition (with no blocks). -/
def updSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x2 => 0x2000 | .x3 => 0x3000 | .x5 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 240⟩, ⟨0x3000, 0⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x4000, 2176⟩]

theorem update_verified (v : Ctr32Impl) :
    Verified AArch64.target (update v.callee) (Spec.Cmac.aesUpdateContract AArch64.abi) :=
  Verified.of_correct (VG.Proof.CmacAes.AArch64.update_correct v) (VG.Proof.CmacAes.AArch64.update_ct v) (by
    sig_implies [Spec.Cmac.aesUpdateContract, Spec.Cmac.aesUpdateSig, VG.Proof.CmacAes.AArch64.updateAArch64, AArch64.abi,
      AArch64.argRegs] [updSat] using VG.Proof.CmacAes.AArch64.updSat)

/-- A state satisfying `vg_cmac_aes_subkeys`'s precondition. -/
def subSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x2 => 0x2000 | .x3 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 240⟩]
  wr := [⟨0x2000, 32⟩, ⟨0x4000, 2176⟩]

theorem subkeys_verified (v : Ctr32Impl) :
    Verified AArch64.target (subkeys v.callee) (Spec.Cmac.aesSubkeysContract AArch64.abi) :=
  Verified.of_correct (VG.Proof.CmacAes.AArch64.subkeys_correct v) (VG.Proof.CmacAes.AArch64.subkeys_ct v) (by
    sig_implies [Spec.Cmac.aesSubkeysContract, Spec.Cmac.aesSubkeysSig, VG.Proof.CmacAes.AArch64.subkeysAArch64, AArch64.abi,
      AArch64.argRegs] [subSat] using VG.Proof.CmacAes.AArch64.subSat)

/-- A state satisfying `vg_cmac_aes_finalize`'s precondition (with no last bytes). -/
def finSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x2 => 0x2000 | .x3 => 0x3000 | .x5 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 272⟩, ⟨0x3000, 0⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x4000, 2176⟩]

theorem finalize_verified (v : Ctr32Impl) :
    Verified AArch64.target (finalize v.callee) (Spec.Cmac.aesFinalizeContract AArch64.abi) :=
  Verified.of_correct (VG.Proof.CmacAes.AArch64.finalize_correct v) (VG.Proof.CmacAes.AArch64.finalize_ct v) (by
    sig_implies [Spec.Cmac.aesFinalizeContract, Spec.Cmac.aesFinalizeSig, VG.Proof.CmacAes.AArch64.finalizeAArch64, AArch64.abi,
      AArch64.argRegs] [finSat] using VG.Proof.CmacAes.AArch64.finSat)

end VG.Proof.CmacAes.AArch64

end
