module

public import VerifiedGarbage.Impl.CmacAes.Stream.RISCV64
public import VerifiedGarbage.Proof.Aes.RISCV64.ExpandKeyVerified
public import VerifiedGarbage.Proof.Cmac.Stream
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Framework.RISCV64.Inline
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.AesCbc.RISCV64.Body
public import VerifiedGarbage.Proof.AesCbc.RISCV64.Loop
import VerifiedGarbage.Proof.Aes.RISCV64.CodeLit
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.Framework.RISCV64.Loops
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Proof.Framework.RISCV64.Align
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.RISCV64.Isa
public import VerifiedGarbage.Impl.CmacAes.RISCV64
public import VerifiedGarbage.Spec.Cmac.Contract
public import VerifiedGarbage.Proof.AesCbc.RISCV64.Chain
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.AesCbc.RISCV64.CT
import VerifiedGarbage.Proof.Aes.RISCV64.BlocksVerified
meta import VerifiedGarbage.Proof.AesCbc.RISCV64.CT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Block
import VerifiedGarbage.Proof.Framework.RISCV64.XorBytes
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Cmac.RISCV64.Dbl
import VerifiedGarbage.Proof.AesCbc.Spec
import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
public import VerifiedGarbage.Impl.AesCbc.RISCV64
public import VerifiedGarbage.Spec.Cmac
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Impl.CmacAes.RISCV64
meta import VerifiedGarbage.Proof.AesCbc.RISCV64.Loop
meta import VerifiedGarbage.Proof.Framework.RISCV64.Spill
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.AesCbc.RISCV64.Body
meta import VerifiedGarbage.Proof.Aes.RISCV64.BlocksVerified
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Cmac.Block
meta import VerifiedGarbage.Proof.Cmac.Mem
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RISCV64.XorBytes
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Cmac.RISCV64.Dbl
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.TCB.RISCV64.Isa
meta import VerifiedGarbage.Proof.Framework.RISCV64.Align
meta import VerifiedGarbage.Proof.AesCbc.Spec
meta import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
meta import VerifiedGarbage.Impl.AesCbc.RISCV64
meta import VerifiedGarbage.Spec.Cmac
meta import Batteries.Tactic.Init
meta import Batteries.Tactic.PermuteGoals
meta import Batteries.Tactic.SeqFocus
meta import VerifiedGarbage.Proof.Framework.GetElem
meta import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.TCB.Artifact

/-! ### `CmacAes.RISCV64.Verified`, which this module and modules that import it used -/

section

/-! ### `CmacAes.RISCV64.CT`, which this module and modules that import it used -/

section

/-! ### `CmacAes.RISCV64.Finalize`, which this module and modules that import it used -/

section

/-! ### `CmacAes.RISCV64.Subkeys`, which this module and modules that import it used -/

section

/-! ### `CmacAes.RISCV64.Contract`, which this module and modules that import it used -/

section

/-!
# AES-CMAC on RISC-V: the contracts the proofs are written against

The artifacts' contracts are the shared ones of `Spec/Cmac/Contract.lean`,
which imply these (`Verified.lean`). A call (`jal`) stores nothing in memory,
so no stack is used.
-/

@[expose] public section

namespace VG.Proof.CmacAes.RISCV64

open VG VG.RISCV64

/-- `CIPH_K` for AES with the key schedule at `w` for `R` rounds, in `m`. -/
abbrev ciphAt (m : Mem) (w : Addr) (R : Nat) : Spec.Cmac.Cipher :=
  Spec.Cmac.aesWith R (Spec.Aes.bytesAt m w (16 * (R + 1)))

/-- `vg_cmac_aes_subkeys(schedule = a0, rounds = a1, subkeys = a2, scratch = a3)`. -/
def subkeysRISCV64 : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .a0, 240⟩
    let subk : Region := ⟨s.gpr .a2, 32⟩
    let scr : Region := ⟨s.gpr .a3, 2176⟩
    s.rd = [sched] ∧ s.wr = [subk, scr] ∧
      sched.Disjoint subk ∧ sched.Disjoint scr ∧ subk.Disjoint scr ∧
      (s.gpr .a2).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .a3).toNat + 2176 ≤ 2 ^ 64 ∧
      ((s.gpr .a1).toNat = 10 ∨ (s.gpr .a1).toNat = 12 ∨ (s.gpr .a1).toNat = 14)
  post s s' :=
    let ks := Spec.Cmac.subkeys (ciphAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) 16
    Spec.Aes.bytesAt s'.mem (s.gpr .a2) 32 = ks.1 ++ ks.2
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp

/-- `vg_cmac_aes_update(schedule = a0, rounds = a1, state = a2, data = a3, n = a4, scratch = a5)`. -/
def updateRISCV64 : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .a0, 240⟩
    let state : Region := ⟨s.gpr .a2, 16⟩
    let data : Region := ⟨s.gpr .a3, 16 * (s.gpr .a4).toNat⟩
    let scr : Region := ⟨s.gpr .a5, 2176⟩
    s.rd = [sched, data] ∧ s.wr = [state, scr] ∧
      sched.Disjoint state ∧ sched.Disjoint scr ∧ data.Disjoint state ∧ data.Disjoint scr ∧
      state.Disjoint scr ∧
      (s.gpr .a2).toNat + 16 ≤ 2 ^ 64 ∧ (s.gpr .a3).toNat + 16 * (s.gpr .a4).toNat ≤ 2 ^ 64 ∧
      (s.gpr .a5).toNat + 2176 ≤ 2 ^ 64 ∧
      ((s.gpr .a1).toNat = 10 ∨ (s.gpr .a1).toNat = 12 ∨ (s.gpr .a1).toNat = 14)
  post s s' :=
    Spec.Aes.bytesAt s'.mem (s.gpr .a2) 16 =
      Spec.Cmac.chain (ciphAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) (Spec.Aes.bytesAt s.mem (s.gpr .a2) 16)
        (Spec.Cmac.blocksAt s.mem (s.gpr .a3) 16 (s.gpr .a4).toNat)
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧ s₁.sp = s₂.sp

/-- `vg_cmac_aes_finalize(key = a0, rounds = a1, state = a2, last = a3, last_len = a4, scratch = a5)`. -/
def finalizeRISCV64 : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .a0, 272⟩
    let state : Region := ⟨s.gpr .a2, 16⟩
    let last : Region := ⟨s.gpr .a3, (s.gpr .a4).toNat⟩
    let scr : Region := ⟨s.gpr .a5, 2176⟩
    s.rd = [key, last] ∧ s.wr = [state, scr] ∧
      key.Disjoint state ∧ key.Disjoint scr ∧ last.Disjoint state ∧ last.Disjoint scr ∧
      state.Disjoint scr ∧
      (s.gpr .a0).toNat + 272 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 16 ≤ 2 ^ 64 ∧
      (s.gpr .a3).toNat + (s.gpr .a4).toNat ≤ 2 ^ 64 ∧ (s.gpr .a5).toNat + 2176 ≤ 2 ^ 64 ∧
      ((s.gpr .a1).toNat = 10 ∨ (s.gpr .a1).toNat = 12 ∨ (s.gpr .a1).toNat = 14) ∧
      (s.gpr .a4).toNat ≤ 16
  post s s' :=
    let ciph := ciphAt s.mem (s.gpr .a0) (s.gpr .a1).toNat
    let ks := Spec.Cmac.subkeys ciph 16
    Spec.Aes.bytesAt s.mem (s.gpr .a0 + 240) 32 = ks.1 ++ ks.2 →
    ∀ msg : List Byte, msg.length % 16 = 0 → (msg = [] ∨ 0 < (s.gpr .a4).toNat) →
      Spec.Aes.bytesAt s.mem (s.gpr .a2) 16 = Spec.Cmac.chain ciph (Spec.Cmac.zeros 16) (Spec.Cmac.blocks 16 msg) →
      Spec.Aes.bytesAt s'.mem (s.gpr .a2) 16 =
        Spec.Cmac.macFull ciph 16 (msg ++ Spec.Aes.bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat)
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧ s₁.sp = s₂.sp

end VG.Proof.CmacAes.RISCV64

end

end

/-!
# AES-CMAC on RISC-V: `vg_cmac_aes_subkeys`

As on PPC64LE (`Proof/CmacAes/PPC64LE/Subkeys.lean`): the return address and
`s1`, `s2` saved in the scratch buffer at `svOf S` (`Spill.save_ok`), the
first block of `subkeys` zeroed (`Bytes.storeBytes_ok`) and enciphered in
place (`blk_call`), doubled there and into the second block (`dbl_wp`), and
the registers restored (`Spill.restore_wp`).
-/

@[expose] public section

namespace VG.Proof.CmacAes.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Align VG.Impl.CmacAes.RISCV64
open VG.Proof.AesCbc.RISCV64 (CallPre CallPost blk_call in_rw savePtr_ok encryptBlocks_noFrames)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac.RISCV64 (dbl_wp wp_xori dbl_spec16)

/-- Where the registers are saved, from the scratch buffer `S`: `S + 2048`
rounded up to a multiple of 8. -/
abbrev svOf (S : Addr) : Addr := S + BitVec.ofNat 64 2048 + BitVec.ofNat 64 (pad (S + BitVec.ofNat 64 2048))

theorem svOf_add (S : Addr) (d : Nat) :
    svOf S + BitVec.ofNat 64 d = S + BitVec.ofNat 64 (2048 + pad (S + BitVec.ofNat 64 2048) + d) :=
  align_add _ _ _

/-- A slot at `svOf S + d`, within the scratch buffer. -/
theorem svOf_sub (S : Addr) {d n : Nat} (h : d + n ≤ 121) :
    Region.Sub ⟨svOf S + BitVec.ofNat 64 d, n⟩ ⟨S, 2176⟩ := by
  have := pad_lt (S + BitVec.ofNat 64 2048)
  rw [svOf_add]; exact Offset.sub_base _ (by omega_using [h, this])

/-- A slot at `svOf S + d`, above the working space of the block function. -/
theorem svOf_ws (S : Addr) {d n : Nat} (h : d + n ≤ 121) :
    Region.Disjoint ⟨svOf S + BitVec.ofNat 64 d, n⟩ ⟨S, 2048⟩ := by
  have := pad_lt (S + BitVec.ofNat 64 2048)
  rw [svOf_add]; exact Offset.disjoint_base _ (by omega_using []) (by omega_using [h, this])

/-- The precondition, by name: the schedule `W`, the subkeys `K`, the scratch
buffer `S` and the rounds `R`. -/
structure SPre (s₀ : State) (W K S : Addr) (R : Nat) : Prop where
  a0 : s₀.gpr .a0 = W
  a2 : s₀.gpr .a2 = K
  a3 : s₀.gpr .a3 = S
  a1 : (s₀.gpr .a1).toNat = R
  rd : s₀.rd = [⟨W, 240⟩]
  wr : s₀.wr = [⟨K, 32⟩, ⟨S, 2176⟩]
  sch_k : (⟨W, 240⟩ : Region).Disjoint ⟨K, 32⟩
  sch_scr : (⟨W, 240⟩ : Region).Disjoint ⟨S, 2176⟩
  k_scr : (⟨K, 32⟩ : Region).Disjoint ⟨S, 2176⟩
  k_wrap : K.toNat + 32 ≤ 2 ^ 64
  scr_wrap : S.toNat + 2176 ≤ 2 ^ 64
  rounds : R = 10 ∨ R = 12 ∨ R = 14

theorem SPre.of {s₀ : State} (h : subkeysRISCV64.pre s₀) :
    SPre s₀ (s₀.gpr .a0) (s₀.gpr .a2) (s₀.gpr .a3) (s₀.gpr .a1).toNat :=
  let ⟨a, b, c, d, e, f, g, h⟩ := h
  ⟨rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h⟩

theorem sk_bound : ∀ p ∈ skSaved, 16 ≤ p.2 ∧ p.2 + 8 ≤ 40 := by decide

/-- The values saved: `t0` holds `svOf S`. -/
abbrev skG (s₀ : State) (S : Addr) : Reg → BitVec 64 := (s₀.write .t0 (svOf S)).gpr

/-- The slots, from `svOf S`. -/
abbrev skSlots (S : Addr) : Region := ⟨svOf S + BitVec.ofNat 64 16, 24⟩

/-- What `subkeysPre` leaves. -/
structure SkMid (s₀ : State) (W K S : Addr) (R : Nat) (s : State) : Prop where
  pre : CallPre s W K S R
  s1 : s.gpr .s1 = K
  s2 : s.gpr .s2 = S
  keep : ∀ r ∈ preserved, r ≠ .s1 → r ≠ .s2 → s.gpr r = s₀.gpr r
  saved : Spill.Saved (svOf S) (skG s₀ S) skSaved s.mem
  zero : bytesAt s.mem K 16 = Spec.Cmac.zeros 16
  frame : Frame [⟨K, 16⟩, skSlots S] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

theorem preserved_ne (r : Reg) (hr : r ∈ preserved) :
    r ≠ .t0 ∧ r ≠ .t1 ∧ r ≠ .t2 ∧ r ≠ .t3 ∧ r ≠ .t4 ∧ r ≠ .t5 ∧ r ≠ .t6 ∧ r ≠ .ra ∧ r ≠ .a0 ∧
      r ≠ .a1 ∧ r ≠ .a2 ∧ r ≠ .a3 ∧ r ≠ .a4 ∧ r ≠ .a5 := by
  revert hr; cases r <;> decide

theorem subkeysPre_wp {s₀ : State} {W K S : Addr} {R : Nat} (hp : SPre s₀ W K S R) :
    WP isa (.block subkeysPre) s₀ (SkMid s₀ W K S R) := by
  have hRr := hp.rounds
  have kw := hp.k_wrap
  have sw := hp.scr_wrap
  have inK (d : Nat) (h : d + 1 ≤ 32) : InRegions s₀.wr (K + BitVec.ofNat 64 d) 1 := by
    rw [hp.wr]; exact in_rw (r := ⟨K, 32⟩) (by simp) (Offset.contains_base _ h (by omega_using [h]))
  rw [subkeysPre, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (savePtr_ok .a3) fun s₁ e => ?_
  subst e
  rw [hp.a3, show skSaved.map (fun (r, d) => Instr.store .d r .t0 d) = Spill.saveCode .t0 skSaved from rfl]
  obtain t₀ : (s₀.write .t0 (svOf S)).gpr .t0 = svOf S := RegUpd.gpr_write_self _ _ _
  have g₀ (r : Reg) (hr : r ≠ .t0) : (s₀.write .t0 (svOf S)).gpr r = s₀.gpr r := RegUpd.gpr_write_of_ne _ _ hr
  refine Spill.save_ok (b := .t0) (l := skSaved) (by rw [t₀]; exact align_al _) (by decide)
    (fun p hp' => ?_) ?_
  · have := sk_bound p hp'
    rw [t₀]
    show InRegions s₀.wr _ 8
    rw [hp.wr]
    have := pad_lt (S + BitVec.ofNat 64 2048)
    exact ⟨⟨S, 2176⟩, by simp, by rw [svOf_add]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  generalize ht : ({ (s₀.write .t0 (svOf S)) with
    mem := Spill.saveMem (s₀.write .t0 (svOf S)).mem ((s₀.write .t0 (svOf S)).gpr .t0)
      (s₀.write .t0 (svOf S)).gpr skSaved } : State) = t
  obtain memt : t.mem = Spill.saveMem s₀.mem (svOf S) (skG s₀ S) skSaved := by
    rw [← ht]; show Spill.saveMem _ _ _ _ = _; rw [t₀]; rfl
  have gt (r : Reg) (hr : r ≠ .t0) : t.gpr r = s₀.gpr r := by rw [← ht]; exact g₀ r hr
  obtain rdt : t.rd = s₀.rd := by rw [← ht]; rfl
  obtain wrt : t.wr = s₀.wr := by rw [← ht]; rfl
  obtain spt : t.sp = s₀.sp := by rw [← ht]; rfl
  simp only [List.cons_append, List.nil_append]
  unfold Impl.AesCbc.RISCV64.mov
  refine wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => ?_
  obtain k₃ : s₃.gpr .s1 = K := by rw [u₃.other _ (by decide), u₂.gpr, gt _ (by decide), hp.a2]
  rw [WP.block_append_iff]
  refine WP.mono (Bytes.storeBytes_ok (tmp := .t1) (dst := .s1) (doff := 0) (bs := List.replicate 16 0)
    (by decide) (by decide) (by decide) (fun i hi => ?_)) fun s₄ h₄ => ?_
  · rw [u₃.wr, u₂.wr, wrt, k₃, Nat.zero_add]; exact inK i (by simp at hi; omega_using [hi])
  refine wp_mv fun s₅ u₅ => wp_li (by decide) fun s₆ u₆ => wp_mv fun s₇ u₇ => WP.block_nil ?_
  obtain rd₇ : s₇.rd = s₀.rd := by rw [u₇.rd, u₆.rd, u₅.rd, h₄.rd, u₃.rd, u₂.rd, rdt]
  obtain wr₇ : s₇.wr = s₀.wr := by rw [u₇.wr, u₆.wr, u₅.wr, h₄.wr, u₃.wr, u₂.wr, wrt]
  obtain mem₇ : s₇.mem = s₄.mem := by rw [u₇.mem, u₆.mem, u₅.mem]
  obtain k₄ : s₄.gpr .s1 = K := by rw [h₄.gpr _ (by decide), k₃]
  obtain s2₄ : s₄.gpr .s2 = S := by
    rw [h₄.gpr _ (by decide), u₃.gpr, u₂.other _ (by decide), gt _ (by decide), hp.a3]
  -- The memory.
  obtain f₃ : Frame [⟨K, 16⟩] s₃.mem s₄.mem := by
    have := h₄.frame; rwa [k₃, BitVec.add_zero, List.length_replicate] at this
  obtain m₃ : s₃.mem = Spill.saveMem s₀.mem (svOf S) (skG s₀ S) skSaved := by rw [u₃.mem, u₂.mem, memt]
  obtain slotK : ∀ p ∈ skSaved, ∀ r ∈ [(⟨K, 16⟩ : Region)], Region.Disjoint ⟨svOf S + BitVec.ofNat 64 p.2, 8⟩ r := by
    intro p hp' r hr
    simp only [List.mem_singleton] at hr; subst hr
    have := sk_bound p hp'
    exact (hp.k_scr.symm.sub_left (svOf_sub S (by omega_using [this]))).sub_right (Region.sub_prefix (by decide))
  refine ⟨CallPre.mk ?_ ?_ ?_ ?_ ?_ hRr (hp.sch_k.sub_right (Region.sub_prefix (by decide)))
      (hp.sch_scr.sub_right (Region.sub_prefix (by decide)))
      ((hp.k_scr.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide)))
      (by omega_using [kw]) ?_ ?_, ?_, ?_, fun r hr h1 h2 => ?_, ?_, ?_, ?_, rd₇, wr₇, ?_⟩
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), h₄.gpr _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), gt _ (by decide), hp.a0]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), h₄.gpr _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), gt _ (by decide), ← hp.a1, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, k₄]
  · rw [u₇.other _ (by decide), u₆.gpr]
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), s2₄]
  · rw [rd₇, wr₇, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨W, 240⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨K, 32⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨S, 2176⟩, by simp, 0, by simp, by simp⟩
  · rw [wr₇, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨K, 32⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨S, 2176⟩, by simp, 0, by simp, by simp⟩
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), k₄]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), s2₄]
  · obtain ⟨h0, h1', -, -, -, -, -, -, -, -, h₂, h₃, h₄', -⟩ := preserved_ne r hr
    rw [u₇.other _ h₄', u₆.other _ h₃, u₅.other _ h₂, h₄.gpr _ h1', u₃.other _ h2, u₂.other _ h1, gt _ h0]
  · have sv₃ : Spill.Saved (svOf S) (skG s₀ S) skSaved s₃.mem := by
      rw [m₃]; exact Spill.saveMem_saved (by decide) s₀.mem (svOf S) _
    rw [mem₇]; exact sv₃.frame f₃ slotK
  · rw [mem₇]
    apply List.ext_getElem (by simp [bytesAt, Spec.Cmac.zeros])
    intro j h₁ _
    simp only [bytesAt, List.length_map, List.length_range] at h₁
    simp only [bytesAt, List.getElem_map, List.getElem_range, Spec.Cmac.zeros, List.getElem_replicate]
    have := h₄.stored j (by simpa using h₁)
    rw [k₃, Nat.zero_add] at this
    obtain hz : ∀ j < 16, (List.replicate 16 (0 : Nat)).getD j 0 = 0 := by decide
    rw [this, hz j h₁]; rfl
  · have fa : Frame [⟨K, 16⟩, skSlots S] s₀.mem s₃.mem := by
      rw [m₃]
      exact (Spill.saveMem_frame (lo := 16) (n := 24) sk_bound (by omega_using []) s₀.mem (svOf S) _).mono (by simp)
    rw [mem₇]; exact fa.trans (f₃.mono (by simp))
  · rw [u₇.sp, u₆.sp, u₅.sp, h₄.sp, u₃.sp, u₂.sp, spt]

/-- `CIPH_K` of a block as `vg_aes_encrypt_blocks` computes it. -/
theorem cipher_bytes (R : Nat) (w : List Byte) (m : Mem) (p : Addr) :
    (Spec.Aes.cipher R w (Spec.Aes.stateAt m p)).toList = Spec.Cmac.aesWith R w (bytesAt m p 16) :=
  (Proof.AesCbc.aesWith_state R w m p).symm

theorem subkeys_wp {s₀ : State} (h0 : subkeysRISCV64.pre s₀) :
    WP isa subkeys s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧
      s'.sp = s₀.sp ∧ subkeysRISCV64.post s₀ s' := by
  obtain hp := SPre.of h0
  generalize hW : s₀.gpr .a0 = W at hp
  generalize hK : s₀.gpr .a2 = K at hp
  generalize hS : s₀.gpr .a3 = S at hp
  generalize hR : (s₀.gpr .a1).toNat = R at hp
  obtain hRb : 16 * (R + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega_using [h]
  have kw := hp.k_wrap
  have sw := hp.scr_wrap
  have inK (d : Nat) (h : d + 1 ≤ 32) : InRegions s₀.wr (K + BitVec.ofNat 64 d) 1 := by
    rw [hp.wr]; exact in_rw (r := ⟨K, 32⟩) (by simp) (Offset.contains_base _ h (by omega_using [h]))
  have rIn (a : Addr) (h : InRegions s₀.wr a 1) : InRegions (s₀.rd ++ s₀.wr) a 1 := by
    obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.seq (WP.mono (subkeysPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (blk_call (name := "vg_aes_encrypt_blocks") Proof.Aes.RISCV64.encryptBlocks_correct
    encryptBlocks_noFrames h₁.pre) fun s₂ c => ?_)
  have g₂ (r : Reg) (hr : r ∈ preserved) : s₂.gpr r = s₁.gpr r := c.saved r hr
  obtain rdwr₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [c.rd, c.wr, h₁.rd, h₁.wr]
  obtain wr₂ : s₂.wr = s₀.wr := by rw [c.wr, h₁.wr]
  rw [subkeysPost, List.append_assoc, List.append_assoc]
  refine dbl_wp (K := K) (src := 0) (dst := 0) (by decide) (by decide) dbl_spec16
    (by rw [g₂ _ (by decide), h₁.s1]) (.inl rfl) (by decide)
    (by decide) (by omega_using [kw]) (fun j hj => by rw [rdwr₂, Nat.zero_add]; exact rIn _ (inK j (by omega_using [hj])))
    (fun j hj => by rw [wr₂, Nat.zero_add]; exact inK j (by omega_using [hj])) fun s₃ g₃ rd₃ wr₃ sp₃ f₃ b₃ => ?_
  refine dbl_wp (K := K) (src := 0) (dst := 16) (by decide) (by decide) dbl_spec16
    (by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), g₂ _ (by decide), h₁.s1]) (.inr (by decide))
    (by decide) (by decide) (by omega_using [kw])
    (fun j hj => by rw [rd₃, wr₃, rdwr₂, Nat.zero_add]; exact rIn _ (inK j (by omega_using [hj])))
    (fun j hj => by rw [wr₃, wr₂]; exact inK (16 + j) (by omega_using [hj])) fun s₄ g₄ rd₄ wr₄ sp₄ f₄ b₄ => ?_
  -- The registers restored.
  obtain s2₄ : s₄.gpr .s2 = S := by
    rw [g₄ _ (by decide) (by decide) (by decide) (by decide), g₃ _ (by decide) (by decide) (by decide) (by decide),
      g₂ _ (by decide), h₁.s2]
  rw [WP.block_append_iff]
  refine WP.mono (savePtr_ok .s2) fun s₅ e => ?_
  subst e
  rw [s2₄]
  -- The slots, kept by the call and the doublings.
  have slotS (p : Reg × Nat) (hp' : p ∈ skSaved) : Region.Sub ⟨svOf S + BitVec.ofNat 64 p.2, 8⟩ ⟨S, 2176⟩ := by
    have := sk_bound p hp'; exact svOf_sub S (by omega_using [this])
  have slotK (p : Reg × Nat) (hp' : p ∈ skSaved) (e : Nat) (he : e ≤ 16) :
      (⟨svOf S + BitVec.ofNat 64 p.2, 8⟩ : Region).Disjoint ⟨K + BitVec.ofNat 64 e, 16⟩ :=
    (hp.k_scr.symm.sub_left (slotS p hp')).sub_right (Offset.sub_base _ (by omega_using [he]))
  obtain sv₂ := h₁.saved.frame c.frame fun p hp' r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have := slotK p hp' 0 (by decide); rwa [BitVec.add_zero] at this
    · exact svOf_ws S (by have := sk_bound p hp'; omega_using [this])
  obtain sv₄ : Spill.Saved (svOf S) (skG s₀ S) skSaved s₄.mem :=
    (sv₂.frame f₃ fun p hp' r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact slotK p hp' 0 (by decide)).frame f₄
      fun p hp' r hr => by simp only [List.mem_singleton] at hr; subst hr; exact slotK p hp' 16 (by decide)
  rw [show skSaved.map (fun (r, d) => Instr.load .d r .t0 d) = Spill.restoreCode .t0 skSaved from rfl]
  refine WP.mono (Spill.restore_wp (b := .t0) (l := skSaved) (B := svOf S) (align_al _)
    (RegUpd.gpr_write_self _ _ _) (by decide) (by decide) (fun p hp' => ?_) sv₄) fun s₆ r₆ => ?_
  · show InRegions (s₄.rd ++ s₄.wr) _ 8
    rw [rd₄, wr₄, rd₃, wr₃, rdwr₂, hp.rd, hp.wr]
    have := pad_lt (S + BitVec.ofNat 64 2048)
    have := sk_bound p hp'
    exact ⟨⟨S, 2176⟩, by simp, by rw [svOf_add]; exact Offset.contains_base _ (by omega) (by omega)⟩
  have g₀ (r : Reg) (hr : r ≠ .t0) : skG s₀ S r = s₀.gpr r := RegUpd.gpr_write_of_ne _ _ hr
  refine ⟨fun r hr => ?_, ?_, ?_, ?_⟩
  · obtain ⟨h0', h1', h2', h3', h4', -, -, -, -, -, -, -, -, -⟩ := preserved_ne r hr
    rw [r₆.gpr_of (r := r) ?_, g₀ r h0']
    by_cases hv : r = .s1 ∨ r = .s2
    · left; rcases hv with rfl | rfl <;> decide
    · right
      rw [RegUpd.gpr_write_of_ne _ _ h0', g₄ r h1' h2' h3' h4', g₃ r h1' h2' h3' h4', g₂ r hr,
        h₁.keep r hr (fun e => hv (.inl e)) (fun e => hv (.inr e)), g₀ r h0']
  · rw [r₆.gpr (.ra, 16) (by decide), g₀ .ra (by decide)]
  · rw [r₆.sp, RegUpd.sp_write, sp₄, sp₃, c.sp, h₁.sp]
  · show bytesAt s₆.mem (s₀.gpr .a2) 32 = _
    obtain schB : bytesAt s₁.mem W (16 * (R + 1)) = bytesAt s₀.mem W (16 * (R + 1)) := by
      refine Proof.Cmac.bytesAt_frame h₁.frame (fun r hr => ?_) (by omega_using [hRb])
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hp.sch_k.sub_left (Region.sub_prefix hRb)).sub_right (Region.sub_prefix (by decide))
      · exact (hp.sch_scr.sub_left (Region.sub_prefix hRb)).sub_right (svOf_sub S (by decide))
    obtain L : bytesAt s₂.mem K 16 = ciphAt s₀.mem W R (Spec.Cmac.zeros 16) := by
      rw [c.out, cipher_bytes, schB, h₁.zero]
    obtain b3 : bytesAt s₃.mem K 16 = Spec.Cmac.dbl 16 (bytesAt s₂.mem K 16) := by
      rw [BitVec.add_zero] at b₃; exact b₃
    obtain b4lo : bytesAt s₄.mem K 16 = bytesAt s₃.mem K 16 :=
      Proof.Cmac.bytesAt_frame16 f₄ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (Offset.disjoint_base K (by decide) (by omega_using [])).symm
    obtain b4hi : bytesAt s₄.mem (K + BitVec.ofNat 64 16) 16 = Spec.Cmac.dbl 16 (bytesAt s₃.mem K 16) := by
      rw [BitVec.add_zero] at b₄; exact b₄
    rw [r₆.mem, RegUpd.mem_write, hK, Proof.Cmac.bytesAt_32, b4lo, b4hi, b3, L, hW, hR]
    rfl

end VG.Proof.CmacAes.RISCV64

end

end

/-!
# AES-CMAC on RISC-V: `vg_cmac_aes_finalize`

The return address and `s1` saved at `svOf S` (`Spill.save_ok`), the last
block `Mₙ` XORed into the state as it is formed (`full_wp` for a complete
block, `partial_wp` for a partial one: `BPost`), the state enciphered in
place, and the registers restored: `CIPH_K(Cₙ₋₁ ⊕ Mₙ)`, the MAC
(`Proof.Cmac.macFull_split`), as on PPC64LE
(`Proof/CmacAes/PPC64LE/Verified.lean`), which forms `Mₙ` in the scratch
buffer first.
-/

@[expose] public section

namespace VG.Proof.CmacAes.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Align VG.Impl.CmacAes.RISCV64
open VG.Proof.AesCbc.RISCV64 (CallPre blk_call in_rw savePtr_ok xorInto_wp encryptBlocks_noFrames)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac.RISCV64 (dbl_wp wp_xori dbl_spec16)

/-- The precondition, by name: the key (schedule and subkeys) `W`, the state
`St`, the last bytes `P` (`L` of them), the scratch buffer `S` and the
rounds `R`. -/
structure FPre (s₀ : State) (W St P S : Addr) (L R : Nat) : Prop where
  a0 : s₀.gpr .a0 = W
  a2 : s₀.gpr .a2 = St
  a3 : s₀.gpr .a3 = P
  a4 : (s₀.gpr .a4).toNat = L
  a5 : s₀.gpr .a5 = S
  a1 : (s₀.gpr .a1).toNat = R
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

theorem FPre.of {s₀ : State} (h : finalizeRISCV64.pre s₀) :
    FPre s₀ (s₀.gpr .a0) (s₀.gpr .a2) (s₀.gpr .a3) (s₀.gpr .a5) (s₀.gpr .a4).toNat (s₀.gpr .a1).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m⟩ := h
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i, j, k, l, m⟩

/-- The last block `Mₙ` (§6.2 step 4), from the key and the last bytes in `m`. -/
abbrev mn (m : Mem) (W P : Addr) (L : Nat) : List Byte :=
  Spec.Cmac.lastBlock 16 (bytesAt m (W + BitVec.ofNat 64 240) 16)
    (bytesAt m (W + BitVec.ofNat 64 256) 16) (bytesAt m P L)

/-- The values `finalize` saves: `t0` holds `svOf S`. -/
abbrev finG (s₀ : State) (S : Addr) : Reg → BitVec 64 := (s₀.write .t0 (svOf S)).gpr

/-- The memory after saving `s1` and the return address. -/
abbrev finMem (s₀ : State) (S : Addr) : Mem := Spill.saveMem s₀.mem (svOf S) (finG s₀ S) finSaved

theorem fin_bound : ∀ p ∈ finSaved, 16 ≤ p.2 ∧ p.2 + 8 ≤ 32 := by decide

/-- The slots, from `svOf S`. -/
abbrev finSlots (S : Addr) : Region := ⟨svOf S + BitVec.ofNat 64 16, 16⟩

/-- Saving the registers changes only their slots. -/
theorem finMem_frame (s₀ : State) (S : Addr) : Frame [finSlots S] s₀.mem (finMem s₀ S) :=
  Spill.saveMem_frame (lo := 16) (n := 16) fin_bound (by decide) _ _ _

theorem FPre.slots_scr {S : Addr} : Region.Sub (finSlots S) ⟨S, 2176⟩ := svOf_sub S (by decide)

theorem FPre.key_sub {W : Addr} {d n : Nat} (h : d + n ≤ 272) : Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 272⟩ :=
  Offset.sub_base _ h

theorem FPre.fin_frame {s₀ : State} {St S : Addr} : Frame [⟨St, 16⟩, ⟨S, 2176⟩] s₀.mem (finMem s₀ S) :=
  (finMem_frame s₀ S).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨S, 2176⟩, by simp, FPre.slots_scr⟩

section
variable {s₀ : State} {W St P S : Addr} {L R : Nat} (hp : FPre s₀ W St P S L R)
include hp

theorem FPre.rKey {s : State} (hr : s.rd = s₀.rd) {d n : Nat} (h : d + n ≤ 272) :
    ∃ r ∈ s.rd ++ s.wr, Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ r :=
  ⟨⟨W, 272⟩, by rw [hr, hp.rd]; simp, FPre.key_sub h⟩

theorem FPre.wSt {s : State} (hw : s.wr = s₀.wr) : ∃ r ∈ s.wr, Region.Sub ⟨St, 16⟩ r :=
  ⟨⟨St, 16⟩, by rw [hw, hp.wr]; simp, fun _ h => h⟩

/-- Bytes of the key, unchanged by writes to the state and the scratch buffer. -/
theorem FPre.key_frame {m m' : Mem} (hf : Frame [⟨St, 16⟩, ⟨S, 2176⟩] m m') {d n : Nat} (h : d + n ≤ 272) :
    bytesAt m' (W + BitVec.ofNat 64 d) n = bytesAt m (W + BitVec.ofNat 64 d) n := by
  have := hp.key_wrap
  refine Proof.Cmac.bytesAt_frame hf (fun r hr => ?_) (by omega_using [h])
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.key_st.sub_left (FPre.key_sub h)
  · exact hp.key_scr.sub_left (FPre.key_sub h)

/-- The last bytes, unchanged likewise. -/
theorem FPre.last_frame {m m' : Mem} (hf : Frame [⟨St, 16⟩, ⟨S, 2176⟩] m m') :
    bytesAt m' P L = bytesAt m P L := by
  have := hp.last_wrap
  refine Proof.Cmac.bytesAt_frame hf (fun r hr => ?_) (by omega_using [this])
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.last_st
  · exact hp.last_scr

end

/-! ## Bytes -/

theorem getD_padded {xs : List Byte} {L : Nat} (hxs : xs.length = L) (hL : L < 16) {k : Nat} (hk : k < 16) :
    (xs ++ [0x80] ++ Spec.Cmac.zeros (16 - L - 1)).getD k 0 =
      if k < L then xs.getD k 0 else if k = L then 0x80 else 0 := by
  subst hxs
  rcases Nat.lt_trichotomy k xs.length with h | h | h
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h, h]
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · obtain ⟨j, hj⟩ : ∃ j, k - xs.length = j + 1 := ⟨k - xs.length - 1, by omega_using [h]⟩
    rw [List.getD_eq_getElem?_getD, List.append_assoc, List.getElem?_append_right (show xs.length ≤ k by omega_using [h]),
      hj, List.singleton_append, List.getElem?_cons_succ, Spec.Cmac.zeros, List.getElem?_replicate]
    simp only [show j < 16 - xs.length - 1 by omega_using [hk, hj], ite_true, Option.getD_some, show ¬ k < xs.length by omega_using [h],
      show k ≠ xs.length by omega_using [h], ite_false]

theorem length_mn (m : Mem) (W P : Addr) {L : Nat} (hL : L ≤ 16) : (mn m W P L).length = 16 := by
  unfold mn Spec.Cmac.lastBlock
  split
  · rename_i h
    rw [Proof.Cmac.bytesAt_length] at h
    simp [Proof.Cmac.length_xor, Proof.Cmac.bytesAt_length, h]
  · rename_i h
    rw [Proof.Cmac.bytesAt_length] at h
    simp [Proof.Cmac.length_xor, Proof.Cmac.bytesAt_length, Spec.Cmac.zeros]; omega

/-- Byte `k` of the last block. -/
theorem getD_mn (m : Mem) (W P : Addr) {L : Nat} (hL : L ≤ 16) {k : Nat} (hk : k < 16) :
    (mn m W P L).getD k 0 = m (W + BitVec.ofNat 64 (if L = 16 then 240 else 256) + BitVec.ofNat 64 k) ^^^
      (if k < L then m (P + BitVec.ofNat 64 k) else if k = L then 0x80 else 0) := by
  unfold mn Spec.Cmac.lastBlock
  rw [Proof.Cmac.bytesAt_length]
  split
  · rename_i h
    obtain rfl : L = 16 := h
    rw [Proof.Cmac.getD_xor (by simp [Proof.Cmac.bytesAt_length]) (by simp [Proof.Cmac.bytesAt_length]; exact hk),
      Proof.Cmac.getD_bytesAt _ _ hk, Proof.Cmac.getD_bytesAt _ _ hk]
    simp [hk]
  · rename_i h
    rw [Proof.Cmac.getD_xor (by simp [Proof.Cmac.bytesAt_length, Spec.Cmac.zeros]; omega_using [hL, h])
      (by simp [Proof.Cmac.bytesAt_length]; exact hk), Proof.Cmac.getD_bytesAt _ _ hk,
      getD_padded (Proof.Cmac.bytesAt_length _ _ _) (by omega_using [hL, h]) hk]
    split
    · rw [Proof.Cmac.getD_bytesAt _ _ (by assumption)]
    · rfl

/-! ## Saving -/

/-- What the code before the branch leaves. -/
structure FA (s₀ : State) (W St P S : Addr) (L : Nat) (s : State) : Prop where
  a0 : s.gpr .a0 = W
  a1 : s.gpr .a1 = s₀.gpr .a1
  a2 : s.gpr .a2 = St
  a3 : s.gpr .a3 = P
  a4 : s.gpr .a4 = BitVec.ofNat 64 L
  s1 : s.gpr .s1 = S
  keep : ∀ r ∈ preserved, r ≠ .s1 → s.gpr r = s₀.gpr r
  mem : s.mem = finMem s₀ S
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

theorem finSave_wp {s₀ : State} {W St P S : Addr} {L R : Nat} (hp : FPre s₀ W St P S L R) :
    WP isa (.block finSave) s₀ fun s => FA s₀ W St P S L s ∧ isa.eval (.zero .t1) s = some (decide (L = 16)) := by
  have hL := hp.len
  obtain h4 : s₀.gpr .a4 = BitVec.ofNat 64 L := by rw [← hp.a4]; apply BitVec.eq_of_toNat_eq; simp
  rw [finSave, List.append_assoc, WP.block_append_iff]
  refine WP.mono (savePtr_ok .a5) fun s₁ e => ?_
  subst e
  rw [hp.a5, show finSaved.map (fun (r, d) => Instr.store .d r .t0 d) = Spill.saveCode .t0 finSaved from rfl]
  obtain t₀ : (s₀.write .t0 (svOf S)).gpr .t0 = svOf S := RegUpd.gpr_write_self _ _ _
  have g₀ (r : Reg) (hr : r ≠ .t0) : (s₀.write .t0 (svOf S)).gpr r = s₀.gpr r := RegUpd.gpr_write_of_ne _ _ hr
  refine Spill.save_ok (b := .t0) (l := finSaved) (by rw [t₀]; exact align_al _) (by decide)
    (fun p hp' => ?_) ?_
  · have := fin_bound p hp'
    have := pad_lt (S + BitVec.ofNat 64 2048)
    have := hp.scr_wrap
    rw [t₀]
    show InRegions s₀.wr _ 8
    rw [hp.wr]
    exact ⟨⟨S, 2176⟩, by simp, by rw [svOf_add]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  generalize ht : ({ (s₀.write .t0 (svOf S)) with
    mem := Spill.saveMem (s₀.write .t0 (svOf S)).mem ((s₀.write .t0 (svOf S)).gpr .t0)
      (s₀.write .t0 (svOf S)).gpr finSaved } : State) = t
  obtain memt : t.mem = finMem s₀ S := by
    rw [← ht]; show Spill.saveMem _ _ _ _ = _; rw [t₀, RegUpd.mem_write]
  have gt (r : Reg) (hr : r ≠ .t0) : t.gpr r = s₀.gpr r := by rw [← ht]; exact g₀ r hr
  obtain rdt : t.rd = s₀.rd := by rw [← ht]; rfl
  obtain wrt : t.wr = s₀.wr := by rw [← ht]; rfl
  obtain spt : t.sp = s₀.sp := by rw [← ht]; rfl
  unfold Impl.AesCbc.RISCV64.mov
  refine wp_mv fun s₂ u₂ => wp_subi (imm := 16) (by decide) fun s₃ u₃ => WP.block_nil ⟨⟨?_, ?_, ?_, ?_, ?_, ?_,
    fun r hr h1 => ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), gt _ (by decide), hp.a0]
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), gt _ (by decide)]
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), gt _ (by decide), hp.a2]
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), gt _ (by decide), hp.a3]
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), gt _ (by decide), h4]
  · rw [u₃.other _ (by decide), u₂.gpr, gt _ (by decide), hp.a5]
  · obtain ⟨h0, h1', -⟩ := preserved_ne r hr
    rw [u₃.other _ h1', u₂.other _ h1, gt _ h0]
  · rw [u₃.mem, u₂.mem, memt]
  · rw [u₃.rd, u₂.rd, rdt]
  · rw [u₃.wr, u₂.wr, wrt]
  · rw [u₃.sp, u₂.sp, spt]
  · rw [eval_zero, u₃.gpr, u₂.other _ (by decide), gt _ (by decide), h4]
    congr 1
    by_cases h : L = 16
    · subst h; decide
    · have hne : BitVec.ofNat 64 L - BitVec.ofNat 64 16 ≠ 0 := by
        intro e
        have := congrArg BitVec.toNat e
        rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show L < 2 ^ 64 by omega_using [hL]),
          Nat.mod_eq_of_lt (show 16 < 2 ^ 64 by decide)] at this
        obtain h0 : (2 ^ 64 - 16 + L) % 2 ^ 64 = 0 := this.trans rfl
        omega_using [hL, h, h0]
      rw [beq_eq_false_iff_ne.mpr hne]; simp [h]

/-! ## The last block -/

/-- What the branch on the length leaves: `C ⊕ Mₙ` in the state. -/
structure BPost (s₀ : State) (W St P S : Addr) (L : Nat) (s : State) : Prop where
  a0 : s.gpr .a0 = W
  a1 : s.gpr .a1 = s₀.gpr .a1
  a2 : s.gpr .a2 = St
  s1 : s.gpr .s1 = S
  keep : ∀ r ∈ preserved, r ≠ .s1 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [⟨St, 16⟩] (finMem s₀ S) s.mem
  st : bytesAt s.mem St 16 = Spec.Cmac.xor (bytesAt s₀.mem St 16) (mn s₀.mem W P L)

/-- The state, unchanged by saving the registers. -/
theorem FPre.st_fin {s₀ : State} {W St P S : Addr} {L R : Nat} (hp : FPre s₀ W St P S L R) :
    bytesAt (finMem s₀ S) St 16 = bytesAt s₀.mem St 16 :=
  Proof.Cmac.bytesAt_frame16 (finMem_frame s₀ S) fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.st_scr.sub_right FPre.slots_scr

/-- Byte `k` of `C ⊕ Mₙ`. -/
theorem getD_xor_mn (m : Mem) (St W P : Addr) {L : Nat} (hL : L ≤ 16) {k : Nat} (hk : k < 16) :
    (Spec.Cmac.xor (bytesAt m St 16) (mn m W P L)).getD k 0 = m (St + BitVec.ofNat 64 k) ^^^
      (m (W + BitVec.ofNat 64 (if L = 16 then 240 else 256) + BitVec.ofNat 64 k) ^^^
        (if k < L then m (P + BitVec.ofNat 64 k) else if k = L then 0x80 else 0)) := by
  rw [Proof.Cmac.getD_xor (by rw [Proof.Cmac.bytesAt_length, length_mn _ _ _ hL])
    (by rw [Proof.Cmac.bytesAt_length]; exact hk), Proof.Cmac.getD_bytesAt _ _ hk, getD_mn _ _ _ hL hk]

theorem full_wp {s₀ : State} {W St P S : Addr} {L R : Nat} (hp : FPre s₀ W St P S L R) (hL : L = 16)
    {s : State} (h : FA s₀ W St P S L s) : WP isa (.block full) s (BPost s₀ W St P S L) := by
  subst hL
  have kw := hp.key_wrap
  have hr : s.rd = s₀.rd := h.rd
  rw [full, List.append_assoc]
  refine xorInto_wp (P := St) (Q := P) (by decide) (by decide) (by decide) (by decide) h.a2 h.a3
    ⟨⟨P, 16⟩, by rw [h.rd, hp.rd]; simp, fun _ h => h⟩ (hp.wSt h.wr) hp.last_st.symm
    fun s₁ g₁ x₁ f₁ rd₁ wr₁ sp₁ => ?_
  simp only [List.cons_append]
  refine wp_addi (imm := 240) (by decide) fun s₂ u₂ => ?_
  rw [List.nil_append]
  refine xorInto_wp (P := St) (Q := W + BitVec.ofNat 64 240) (by decide) (by decide) (by decide) (by decide)
    (by rw [u₂.other _ (by decide), g₁ _ (by decide) (by decide), h.a2])
    (by rw [u₂.gpr, g₁ _ (by decide) (by decide), h.a0])
    (hp.rKey (s := s₂) (by rw [u₂.rd, rd₁, h.rd]) (by decide)) (hp.wSt (by rw [u₂.wr, wr₁, h.wr]))
    (hp.key_st.symm.sub_right (FPre.key_sub (by decide))) fun s₃ g₃ x₃ f₃ rd₃ wr₃ sp₃ => WP.block_nil ?_
  have g (r : Reg) (h3 : r ≠ .t3) (h4 : r ≠ .t4) (h5 : r ≠ .t5) : s₃.gpr r = s.gpr r := by
    rw [g₃ r h3 h4, u₂.other _ h5, g₁ r h3 h4]
  obtain fr : Frame [⟨St, 16⟩] s.mem s₃.mem := f₁.trans (by rw [← u₂.mem]; exact f₃)
  obtain hfm : Frame [⟨St, 16⟩, ⟨S, 2176⟩] s₀.mem s.mem := by rw [h.mem]; exact FPre.fin_frame
  refine ⟨by rw [g _ (by decide) (by decide) (by decide), h.a0], by rw [g _ (by decide) (by decide) (by decide), h.a1],
    by rw [g _ (by decide) (by decide) (by decide), h.a2], by rw [g _ (by decide) (by decide) (by decide), h.s1],
    fun r hr h1 => ?_, by rw [rd₃, u₂.rd, rd₁, h.rd], by rw [wr₃, u₂.wr, wr₁, h.wr], by rw [sp₃, u₂.sp, sp₁, h.sp],
    by rw [← h.mem]; exact fr, ?_⟩
  · obtain ⟨-, -, -, h3, h4, h5, -⟩ := preserved_ne r hr
    rw [g r h3 h4 h5, h.keep r hr h1]
  · -- `(C ⊕ Mₙ*) ⊕ K1`, byte by byte.
    obtain k1 : bytesAt s₁.mem (W + BitVec.ofNat 64 240) 16 = bytesAt s₀.mem (W + BitVec.ofNat 64 240) 16 := by
      rw [hp.key_frame (f₁.mono (by simp)) (by decide), hp.key_frame hfm (by decide)]
    obtain lst : bytesAt s.mem P 16 = bytesAt s₀.mem P 16 := hp.last_frame hfm
    obtain st : bytesAt s.mem St 16 = bytesAt s₀.mem St 16 := by rw [h.mem, hp.st_fin]
    rw [x₃, u₂.mem, x₁, k1, lst, st]
    refine Proof.Cmac.ext16 (by simp [Spec.Cbc.xor, Proof.Cmac.bytesAt_length])
      (by rw [Proof.Cmac.length_xor, Proof.Cmac.bytesAt_length, length_mn _ _ _ (by decide)]; rfl) fun k hk => ?_
    rw [getD_xor_mn _ _ _ _ (by decide) hk]
    simp only [Spec.Cbc.xor]
    rw [← Spec.Cmac.xor, Proof.Cmac.getD_xor (by simp [Proof.Cmac.bytesAt_length])
        (by simp [Proof.Cmac.bytesAt_length]; exact hk),
      Proof.Cmac.getD_bytesAt _ _ hk, ← Spec.Cmac.xor,
      Proof.Cmac.getD_xor (by simp [Proof.Cmac.bytesAt_length]) (by simp [Proof.Cmac.bytesAt_length]; exact hk),
      Proof.Cmac.getD_bytesAt _ _ hk, Proof.Cmac.getD_bytesAt _ _ hk]
    simp only [hk, ite_true]
    rw [Offset.add_add]
    simp only [BitVec.xor_assoc, BitVec.xor_comm (s₀.mem (P + BitVec.ofNat 64 k))]

/-! ### A partial last block -/

theorem cbc_xor : Spec.Cbc.xor = Spec.Cmac.xor := rfl

/-- After `i` bytes XORed into the state, from `s`. -/
structure XInv (s : State) (St P : Addr) (L i : Nat) (t : State) : Prop where
  le : i ≤ L
  t5 : t.gpr .t5 = P + BitVec.ofNat 64 i
  t6 : t.gpr .t6 = St + BitVec.ofNat 64 i
  t1 : t.gpr .t1 = BitVec.ofNat 64 (L - i)
  gpr : ∀ r, r ≠ .t1 → r ≠ .t3 → r ≠ .t4 → r ≠ .t5 → r ≠ .t6 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  bytes : ∀ j < 16, t.mem (St + BitVec.ofNat 64 j) =
    if j < i then s.mem (P + BitVec.ofNat 64 j) ^^^ s.mem (St + BitVec.ofNat 64 j) else s.mem (St + BitVec.ofNat 64 j)
  frame : Frame [⟨St, 16⟩] s.mem t.mem

section
variable {s₀ : State} {W St P S : Addr} {L R : Nat} (hp : FPre s₀ W St P S L R)
include hp

theorem xorStep_wp (hL : L < 16) {s : State} (hs : FA s₀ W St P S L s) {i : Nat} (hi : i < L) {t : State}
    (h : XInv s St P L i t) :
    WP isa (.block [.load .b .t3 .t5 0, .load .b .t4 .t6 0, .logic .xor .t3 .t3 .t4, .store .b .t3 .t6 0,
      .addi .t5 .t5 1, .addi .t6 .t6 1, .addi .t1 .t1 (-1)]) t (XInv s St P L (i + 1)) := by
  have sw := hp.st_wrap
  have lw := hp.last_wrap
  obtain hsep : ∀ j < 16, ¬ (⟨St, 16⟩ : Region).Contains (P + BitVec.ofNat 64 j) 1 → True := fun _ _ _ => trivial
  obtain pS : ¬ (⟨St, 16⟩ : Region).Contains (P + BitVec.ofNat 64 i) 1 := fun hc =>
    hp.last_st _ (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hL, hi])) hc
  refine wp_lbu (a := P + BitVec.ofNat 64 i) (by decide) (by rw [h.t5, BitVec.add_zero])
    (by rw [h.rd, h.wr, hs.rd, hs.wr, hp.rd]; exact ⟨⟨P, L⟩, by simp, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hL, hi])⟩)
    fun t₁ v₁ => ?_
  refine wp_lbu (a := St + BitVec.ofNat 64 i) (by decide)
    (by rw [v₁.other _ (by decide), h.t6, BitVec.add_zero])
    (by rw [v₁.rd, v₁.wr, h.rd, h.wr, hs.rd, hs.wr, hp.wr]
        exact ⟨⟨St, 16⟩, by simp, Offset.contains_base _ (by omega_using [hL, hi]) (by omega_using [hL, hi])⟩) fun t₂ v₂ => ?_
  refine wp_xor fun t₃ v₃ => ?_
  refine wp_sb (a := St + BitVec.ofNat 64 i) (by decide)
    (by rw [v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide), h.t6, BitVec.add_zero])
    (by rw [v₃.wr, v₂.wr, v₁.wr, h.wr, hs.wr, hp.wr]
        exact ⟨⟨St, 16⟩, by simp, Offset.contains_base _ (by omega_using [hL, hi]) (by omega_using [hL, hi])⟩) fun t₄ g₄ => ?_
  refine wp_addi (imm := 1) (by decide) fun t₅ v₅ => wp_addi (imm := 1) (by decide) fun t₆ v₆ =>
    wp_subi (imm := 1) (by decide) fun t₇ v₇ => WP.block_nil ?_
  obtain rP : t.mem (P + BitVec.ofNat 64 i) = s.mem (P + BitVec.ofNat 64 i) :=
    h.frame _ fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact pS
  obtain rS : t.mem (St + BitVec.ofNat 64 i) = s.mem (St + BitVec.ofNat 64 i) := by
    rw [h.bytes i (by omega_using [hL, hi])]; simp
  obtain hv : (t₃.gpr .t3).setWidth 8 = s.mem (P + BitVec.ofNat 64 i) ^^^ s.mem (St + BitVec.ofNat 64 i) := by
    rw [v₃.gpr, v₂.other _ (by decide), v₂.gpr, v₁.gpr, v₁.mem, rP, rS, Bytes.xor_setWidth]
  obtain hm : t₇.mem = t.mem.writeW (St + BitVec.ofNat 64 i)
      (s.mem (P + BitVec.ofNat 64 i) ^^^ s.mem (St + BitVec.ofNat 64 i)) := by
    rw [v₇.mem, v₆.mem, v₅.mem, g₄.mem, hv, v₃.mem, v₂.mem, v₁.mem]
  refine ⟨by omega_using [hi], ?_, ?_, ?_, fun r h1 h3 h4 h5 h6 => ?_, ?_, ?_, ?_, fun j hj => ?_, ?_⟩
  · rw [v₇.other _ (by decide), v₆.other _ (by decide), v₅.gpr, g₄.gpr, v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.other _ (by decide), h.t5, Offset.add_add]
  · rw [v₇.other _ (by decide), v₆.gpr, v₅.other _ (by decide), g₄.gpr, v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.other _ (by decide), h.t6, Offset.add_add]
  · rw [v₇.gpr, v₆.other _ (by decide), v₅.other _ (by decide), g₄.gpr, v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.other _ (by decide), h.t1, Offset.ofNat_sub_ofNat (by omega_using [hi]), Nat.sub_sub]
  · rw [v₇.other _ h1, v₆.other _ h6, v₅.other _ h5, g₄.gpr, v₃.other _ h3, v₂.other _ h4, v₁.other _ h3,
      h.gpr r h1 h3 h4 h5 h6]
  · rw [v₇.rd, v₆.rd, v₅.rd, g₄.rd, v₃.rd, v₂.rd, v₁.rd, h.rd]
  · rw [v₇.wr, v₆.wr, v₅.wr, g₄.wr, v₃.wr, v₂.wr, v₁.wr, h.wr]
  · rw [v₇.sp, v₆.sp, v₅.sp, g₄.sp, v₃.sp, v₂.sp, v₁.sp, h.sp]
  · rw [hm, WriteBytes.writeW8_apply]
    by_cases e : j = i
    · subst e; simp
    · have hne : ¬ (St + BitVec.ofNat 64 j = St + BitVec.ofNat 64 i) := fun h' => e (by
        have := congrArg (fun a => (a - St).toNat) h'
        simp only [Mem.sub_ofNat_toNat St (show j < 2 ^ 64 by omega_using [hj]),
          Mem.sub_ofNat_toNat St (show i < 2 ^ 64 by omega_using [hL, hi])] at this
        exact this)
      simp only [hne, ite_false]
      rw [h.bytes j hj]
      by_cases hj' : j < i
      · simp [hj', show j < i + 1 by omega_using [hj']]
      · simp [hj', show ¬ j < i + 1 by omega_using [e, hj']]
  · rw [hm]
    exact h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_using [hL, hi]) (by omega_using [hL, hi]))

theorem xorLoop_wp (hL : L < 16) {s : State} (hs : FA s₀ W St P S L s) {i : Nat} (hi : i < L) {t : State}
    (h : XInv s St P L i t) : WP isa xorLoop t (XInv s St P L L) := by
  refine WP.loop (M := isa) (Q := XInv s St P L L)
    (fun (n : Nat) (u : State) => ∃ j, n = L - j ∧ j < L ∧ XInv s St P L j u) ?_ (L - i) t ⟨i, rfl, hi, h⟩
  rintro n u ⟨j, rfl, hj, hu⟩
  refine WP.mono (xorStep_wp hp hL hs hj hu) fun u' h' => ?_
  obtain ev := eval_nonzero_ofNat u' .t1 (k := L - (j + 1)) (by omega_using [hL]) h'.t1
  by_cases hz : L - (j + 1) = 0
  · left
    refine ⟨by rw [ev]; simp [hz], ?_⟩
    obtain e : j + 1 = L := by omega_using [hj, hz]
    rw [e] at h'; exact h'
  · right
    exact ⟨by rw [ev]; simp [hz], L - (j + 1), by omega_using [hj], j + 1, rfl, by omega_using [hz], h'⟩

theorem partial_wp (hL : L < 16) {s : State} (h : FA s₀ W St P S L s) :
    WP isa partialBlock s (BPost s₀ W St P S L) := by
  have sw := hp.st_wrap
  have kw := hp.key_wrap
  unfold partialBlock Impl.AesCbc.RISCV64.mov
  obtain A : WP isa (.block [.addi .t5 .a3 0, .addi .t6 .a2 0, .addi .t1 .a4 0]) s (XInv s St P L 0) := by
    refine wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => WP.block_nil ?_
    refine ⟨by omega_using [], ?_, ?_, ?_, fun r h1 _ _ h5 h6 => ?_, ?_, ?_, ?_,
      fun j hj => by rw [u₃.mem, u₂.mem, u₁.mem]; simp, ?_⟩
    · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.a3, BitVec.add_zero]
    · rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h.a2, BitVec.add_zero]
    · rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.a4, Nat.sub_zero]
    · rw [u₃.other _ h1, u₂.other _ h6, u₁.other _ h5]
    · rw [u₃.rd, u₂.rd, u₁.rd]
    · rw [u₃.wr, u₂.wr, u₁.wr]
    · rw [u₃.sp, u₂.sp, u₁.sp]
    · rw [u₃.mem, u₂.mem, u₁.mem]; exact Frame.refl _ _
  refine WP.seq (WP.mono A fun t₀ h₀ => ?_)
  refine WP.seq (WP.mono (Q := XInv s St P L L) ?_ fun t₁ h₁ => ?_)
  · have ev := eval_zero_ofNat t₀ .t1 (k := L - 0) (by omega_using [hL]) h₀.t1
    rw [Nat.sub_zero] at ev
    by_cases hz : L = 0
    · refine WP.ite true (by rw [ev, hz]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      rw [hz]; rw [hz] at h₀; exact h₀
    · exact WP.ite false (by rw [ev]; simp [hz]) (fun h => by cases h)
        fun _ => xorLoop_wp hp hL h (by omega_using [hz]) h₀
  -- `0x80` after the bytes, and `K2`.
  rw [padK2, List.cons_append, List.cons_append, List.cons_append, List.cons_append, List.nil_append]
  refine wp_lbu (a := St + BitVec.ofNat 64 L) (by decide) (by rw [h₁.t6, BitVec.add_zero])
    (by rw [h₁.rd, h₁.wr, h.rd, h.wr, hp.wr]
        exact ⟨⟨St, 16⟩, by simp, Offset.contains_base _ (by omega_using [hL]) (by omega_using [hL])⟩) fun t₂ v₂ => ?_
  refine wp_xori (by decide) fun t₃ v₃ => ?_
  refine wp_sb (a := St + BitVec.ofNat 64 L) (by decide)
    (by rw [v₃.other _ (by decide), v₂.other _ (by decide), h₁.t6, BitVec.add_zero])
    (by rw [v₃.wr, v₂.wr, h₁.wr, h.wr, hp.wr]
        exact ⟨⟨St, 16⟩, by simp, Offset.contains_base _ (by omega_using [hL]) (by omega_using [hL])⟩) fun t₄ g₄ => ?_
  refine wp_addi (imm := 256) (by decide) fun t₅ v₅ => ?_
  have g₅ (r : Reg) (h1 : r ≠ .t1) (h3 : r ≠ .t3) (h4 : r ≠ .t4) (h5 : r ≠ .t5) (h6 : r ≠ .t6) :
      t₅.gpr r = s.gpr r := by
    rw [v₅.other _ h5, g₄.gpr, v₃.other _ h3, v₂.other _ h3, h₁.gpr r h1 h3 h4 h5 h6]
  obtain rd₅ : t₅.rd = s.rd := by rw [v₅.rd, g₄.rd, v₃.rd, v₂.rd, h₁.rd]
  obtain wr₅ : t₅.wr = s.wr := by rw [v₅.wr, g₄.wr, v₃.wr, v₂.wr, h₁.wr]
  refine xorInto_wp (P := St) (Q := W + BitVec.ofNat 64 256) (by decide) (by decide) (by decide) (by decide)
    (by rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide), h.a2])
    (by rw [v₅.gpr, g₄.gpr, v₃.other _ (by decide), v₂.other _ (by decide),
      h₁.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide), h.a0])
    (hp.rKey (by rw [rd₅, h.rd]) (by decide)) (hp.wSt (by rw [wr₅, h.wr]))
    (hp.key_st.symm.sub_right (FPre.key_sub (by decide))) fun t₆ g₆ x₆ f₆ rd₆ wr₆ sp₆ => WP.block_nil ?_
  obtain hb : (t₃.gpr .t3).setWidth 8 = s.mem (St + BitVec.ofNat 64 L) ^^^ 0x80 := by
    rw [v₃.gpr, v₂.gpr, h₁.bytes L (by omega_using [hL])]; simp
  obtain hm₄ : t₄.mem = t₁.mem.writeW (St + BitVec.ofNat 64 L) (s.mem (St + BitVec.ofNat 64 L) ^^^ 0x80) := by
    rw [g₄.mem, hb, v₃.mem, v₂.mem]
  obtain hfm : Frame [⟨St, 16⟩, ⟨S, 2176⟩] s₀.mem s.mem := by rw [h.mem]; exact FPre.fin_frame
  obtain f₅ : Frame [⟨St, 16⟩] s.mem t₅.mem := by
    rw [v₅.mem, hm₄]
    exact h₁.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_using [hL]) (by omega_using [hL]))
  obtain fr : Frame [⟨St, 16⟩] s.mem t₆.mem := f₅.trans f₆
  refine ⟨by rw [g₆ _ (by decide) (by decide), g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide), h.a0],
    by rw [g₆ _ (by decide) (by decide), g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide), h.a1],
    by rw [g₆ _ (by decide) (by decide), g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide), h.a2],
    by rw [g₆ _ (by decide) (by decide), g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide), h.s1],
    fun r hr h1 => ?_, by rw [rd₆, rd₅, h.rd], by rw [wr₆, wr₅, h.wr], by rw [sp₆, v₅.sp, g₄.sp, v₃.sp, v₂.sp, h₁.sp, h.sp],
    by rw [← h.mem]; exact fr, ?_⟩
  · obtain ⟨-, h1', -, h3, h4, h5, h6, -⟩ := preserved_ne r hr
    rw [g₆ r h3 h4, g₅ r h1' h3 h4 h5 h6, h.keep r hr h1]
  · -- Byte by byte.
    obtain k2 : bytesAt t₅.mem (W + BitVec.ofNat 64 256) 16 = bytesAt s₀.mem (W + BitVec.ofNat 64 256) 16 :=
      hp.key_frame (hfm.trans (f₅.mono (by simp))) (by decide)
    rw [x₆, k2]
    refine Proof.Cmac.ext16 (by simp [Spec.Cbc.xor, Proof.Cmac.bytesAt_length])
      (by rw [Proof.Cmac.length_xor, Proof.Cmac.bytesAt_length, length_mn _ _ _ (by omega_using [hL])]; rfl) fun k hk => ?_
    rw [getD_xor_mn _ _ _ _ (by omega_using [hL]) hk, cbc_xor,
      Proof.Cmac.getD_xor (by simp [Proof.Cmac.bytesAt_length]) (by simp [Proof.Cmac.bytesAt_length]; exact hk),
      Proof.Cmac.getD_bytesAt _ _ hk, Proof.Cmac.getD_bytesAt _ _ hk, v₅.mem, hm₄, WriteBytes.writeW8_apply,
      h₁.bytes k hk]
    simp only [show L ≠ 16 by omega_using [hL], ite_false]
    obtain cS : s.mem (St + BitVec.ofNat 64 k) = s₀.mem (St + BitVec.ofNat 64 k) := by
      have := congrArg (fun l => l.getD k 0) hp.st_fin
      simp only [Proof.Cmac.getD_bytesAt _ _ hk] at this
      rw [h.mem]; exact this
    obtain heq : (St + BitVec.ofNat 64 k = St + BitVec.ofNat 64 L) ↔ k = L := by
      constructor
      · intro e
        have := congrArg (fun a => (a - St).toNat) e
        simp only [Mem.sub_ofNat_toNat St (show k < 2 ^ 64 by omega_using [hk]),
          Mem.sub_ofNat_toNat St (show L < 2 ^ 64 by omega_using [hL])] at this
        exact this
      · intro e; rw [e]
    rcases Nat.lt_trichotomy k L with hkL | hkL | hkL
    · have pS : s.mem (P + BitVec.ofNat 64 k) = s₀.mem (P + BitVec.ofNat 64 k) := by
        have := congrArg (fun l => l.getD k 0) (hp.last_frame hfm)
        simp only [Proof.Cmac.getD_bytesAt _ _ hkL] at this
        exact this
      simp only [show ¬ (St + BitVec.ofNat 64 k = St + BitVec.ofNat 64 L) by rw [heq]; omega_using [hkL], hkL, ite_false,
        ite_true, pS, cS]
      ac_rfl
    · subst hkL
      simp only [Nat.lt_irrefl, ite_false, ite_true, cS]
      ac_rfl
    · simp only [show ¬ (St + BitVec.ofNat 64 k = St + BitVec.ofNat 64 L) by rw [heq]; omega_using [hkL],
        show ¬ k < L by omega_using [hkL], show k ≠ L by omega_using [hkL], ite_false, cS]
      exact congrArg _ BitVec.xor_zero.symm

/-! ## Before and after the call -/

/-- What the code before the call leaves. -/
structure FMid (s₀ : State) (W St P S : Addr) (L R : Nat) (s : State) : Prop where
  pre : CallPre s W St S R
  s1 : s.gpr .s1 = S
  keep : ∀ r ∈ preserved, r ≠ .s1 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [⟨St, 16⟩] (finMem s₀ S) s.mem
  st : bytesAt s.mem St 16 = Spec.Cmac.xor (bytesAt s₀.mem St 16) (mn s₀.mem W P L)

theorem args_wp {s : State} (h : BPost s₀ W St P S L s) :
    WP isa (.block [.li .a3 1, Impl.AesCbc.RISCV64.mov .a4 .s1]) s (FMid s₀ W St P S L R) := by
  have := hp.st_wrap
  unfold Impl.AesCbc.RISCV64.mov
  refine wp_li (imm := 1) (by decide) fun s₁ u₁ => wp_mv fun s₂ u₂ => WP.block_nil ?_
  obtain rd₂ : s₂.rd = s₀.rd := by rw [u₂.rd, u₁.rd, h.rd]
  obtain wr₂ : s₂.wr = s₀.wr := by rw [u₂.wr, u₁.wr, h.wr]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, hp.rounds, hp.key_st.sub_left (Region.sub_prefix (by decide)),
      (hp.key_scr.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide)),
      hp.st_scr.sub_right (Region.sub_prefix (by decide)), hp.st_wrap, ?_, ?_⟩,
    by rw [u₂.other _ (by decide), u₁.other _ (by decide), h.s1], fun r hr h1 => ?_, rd₂, wr₂,
    by rw [u₂.sp, u₁.sp, h.sp], by rw [u₂.mem, u₁.mem]; exact h.frame, by rw [u₂.mem, u₁.mem]; exact h.st⟩
  · rw [u₂.other _ (by decide), u₁.other _ (by decide), h.a0]
  · rw [u₂.other _ (by decide), u₁.other _ (by decide), h.a1, ← hp.a1, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [u₂.other _ (by decide), u₁.other _ (by decide), h.a2]
  · rw [u₂.other _ (by decide), u₁.gpr]
  · rw [u₂.gpr, u₁.other _ (by decide), h.s1]
  · rw [rd₂, wr₂, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨W, 272⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨St, 16⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨S, 2176⟩, by simp, 0, by simp, by simp⟩
  · rw [wr₂, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨St, 16⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨S, 2176⟩, by simp, 0, by simp, by simp⟩
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h3, h4, -⟩ := preserved_ne r hr
    rw [u₂.other _ h4, u₁.other _ h3, h.keep r hr h1]

theorem finPre_wp : WP isa finPre s₀ (FMid s₀ W St P S L R) := by
  refine WP.seq (WP.mono (finSave_wp hp) fun s₁ ⟨h₁, ev₁⟩ => ?_)
  refine WP.seq (WP.mono (Q := BPost s₀ W St P S L) ?_ fun _ h => args_wp hp h)
  by_cases hL : L = 16
  · exact WP.ite true (by rw [ev₁]; simp [hL]) (fun _ => full_wp hp hL h₁) (fun h => by cases h)
  · exact WP.ite false (by rw [ev₁]; simp [hL]) (fun h => by cases h)
      (fun _ => partial_wp hp (by have := hp.len; omega_using [hL, this]) h₁)

end

theorem finalize_wp {s₀ : State} (h0 : finalizeRISCV64.pre s₀) :
    WP isa finalize s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧
      s'.sp = s₀.sp ∧ finalizeRISCV64.post s₀ s' := by
  obtain hp := FPre.of h0
  generalize hW : s₀.gpr .a0 = W at hp
  generalize hSt : s₀.gpr .a2 = St at hp
  generalize hP : s₀.gpr .a3 = P at hp
  generalize hS : s₀.gpr .a5 = S at hp
  generalize hL : (s₀.gpr .a4).toNat = L at hp
  generalize hR : (s₀.gpr .a1).toNat = R at hp
  obtain hRb : 16 * (R + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega_using [h]
  have sw := hp.scr_wrap
  refine WP.seq (WP.mono (finPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (blk_call (name := "vg_aes_encrypt_blocks") Proof.Aes.RISCV64.encryptBlocks_correct
    encryptBlocks_noFrames h₁.pre) fun s₂ c => ?_)
  obtain slotD : ∀ p ∈ finSaved, ∀ r ∈ [(⟨St, 16⟩ : Region), ⟨S, 2048⟩],
      Region.Disjoint ⟨svOf S + BitVec.ofNat 64 p.2, 8⟩ r := by
    intro p hp' r hr
    obtain hb := fin_bound p hp'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.st_scr.symm.sub_left (svOf_sub S (by omega_using [hb]))
    · exact svOf_ws S (by omega_using [hb])
  obtain hsv : Spill.Saved (svOf S) (finG s₀ S) finSaved s₂.mem :=
    ((Spill.saveMem_saved (by decide) s₀.mem (svOf S) _).frame h₁.frame fun p hp' r hr =>
      slotD p hp' r (by simp only [List.mem_singleton] at hr; subst hr; simp)).frame
      c.frame fun p hp' r hr => slotD p hp' r hr
  obtain s1₂ : s₂.gpr .s1 = S := by rw [c.saved _ (by decide), h₁.s1]
  obtain rdwr₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [c.rd, c.wr, h₁.rd, h₁.wr]
  rw [finRestore, WP.block_append_iff]
  refine WP.mono (savePtr_ok .s1) fun s₃ e => ?_
  subst e
  rw [s1₂, show finSaved.map (fun (r, d) => Instr.load .d r .t0 d) = Spill.restoreCode .t0 finSaved from rfl]
  refine WP.mono (Spill.restore_wp (b := .t0) (l := finSaved) (B := svOf S) (align_al _)
    (RegUpd.gpr_write_self _ _ _) (by decide) (by decide) (fun p hp' => ?_) hsv) fun s₄ r₄ => ?_
  · have := fin_bound p hp'
    have := pad_lt (S + BitVec.ofNat 64 2048)
    show InRegions (s₂.rd ++ s₂.wr) _ 8
    rw [rdwr₂, hp.rd, hp.wr]
    exact ⟨⟨S, 2176⟩, by simp, by rw [svOf_add]; exact Offset.contains_base _ (by omega) (by omega)⟩
  have g₀ (r : Reg) (hr : r ≠ .t0) : finG s₀ S r = s₀.gpr r := RegUpd.gpr_write_of_ne _ _ hr
  refine ⟨fun r hr => ?_, ?_, ?_, ?_⟩
  · have h0 := (preserved_ne r hr).1
    rw [r₄.gpr_of (r := r) ?_, g₀ r h0]
    by_cases h1 : r = .s1
    · left; subst h1; decide
    · right; rw [RegUpd.gpr_write_of_ne _ _ h0, c.saved r hr, h₁.keep r hr h1, g₀ r h0]
  · rw [r₄.gpr (.ra, 16) (by decide), g₀ .ra (by decide)]
  · rw [r₄.sp, RegUpd.sp_write, c.sp, h₁.sp]
  · intro hk msg hm hne hst
    rw [hW, hR] at hk hst ⊢
    rw [hSt] at hst ⊢
    rw [hL] at hne
    rw [hP, hL]
    obtain hfm : Frame [⟨St, 16⟩, ⟨S, 2176⟩] s₀.mem s₁.mem :=
      FPre.fin_frame.trans (h₁.frame.mono (by simp))
    obtain sch : bytesAt s₁.mem W (16 * (R + 1)) = bytesAt s₀.mem W (16 * (R + 1)) := by
      have := hp.key_frame hfm (d := 0) (n := 16 * (R + 1)) (by omega_using [hRb])
      rwa [BitVec.add_zero] at this
    obtain ⟨e1, e2⟩ := Proof.Cmac.k1k2 (Proof.Cmac.subkeys_aes_length _ _) hk
    rw [r₄.mem, RegUpd.mem_write, c.out, cipher_bytes, sch, h₁.st, mn, e1, e2, hst,
      Proof.Cmac.macFull_split _ hm (by rw [Proof.Cmac.bytesAt_length]; exact hp.len)
        (by rw [Proof.Cmac.bytesAt_length]; exact hne)]

end VG.Proof.CmacAes.RISCV64

end

end

/-!
# AES-CMAC on RISC-V: constant time

As on PPC64LE (`Proof/CmacAes/PPC64LE/Verified.lean`): two runs from states that
agree on the public arguments are related piece by piece (`RelCT`): the
taint analysis covers the code between the calls, from the registers the
correctness proofs pin to public values and the stack pointer, which no code
changes, and each call of `vg_aes_encrypt_blocks` is constant time by its
own proof (`blk_rel`). The branches of `finalize` are on `last_len`, which
is public. (`update`, a call of the chain, is constant time by
`Proof.AesCbc.RISCV64.wrap_ct`: `Verified.lean`.)
-/

@[expose] public section

namespace VG.Proof.CmacAes.RISCV64

open VG VG.RISCV64 VG.Impl.CmacAes.RISCV64
open VG.Proof.AesCbc.RISCV64 (blk_call blk_rel taintRegs encryptBlocks_noFrames)

/-! ## `vg_cmac_aes_subkeys` -/

theorem subkeys_rel {s₀ s₀' : State} (h0 : subkeysRISCV64.pre s₀) (h0' : subkeysRISCV64.pre s₀')
    (hq : subkeysRISCV64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') subkeys fun _ _ => True := by
  obtain ⟨q1, q2, q3, q4, q5⟩ := hq
  have hp := SPre.of h0
  have hp' : SPre s₀' (s₀.gpr .a0) (s₀.gpr .a2) (s₀.gpr .a3) (s₀.gpr .a1).toNat := by
    rw [q1, q2, q3, q4]; exact SPre.of h0'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.a0, .a1, .a2, .a3]) (.block subkeysPre) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.s1, .s2]) (.block subkeysPost) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := (taintRegs (P := fun a b => a = s₀ ∧ b = s₀') [.a0, .a1, .a2, .a3]
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨q5, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption) hA).wp
    (F₁ := SkMid s₀ (s₀.gpr .a0) (s₀.gpr .a2) (s₀.gpr .a3) (s₀.gpr .a1).toNat)
    (F₂ := SkMid s₀' (s₀.gpr .a0) (s₀.gpr .a2) (s₀.gpr .a3) (s₀.gpr .a1).toNat)
    fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨subkeysPre_wp hp, subkeysPre_wp hp'⟩
  have c := (blk_rel (name := "vg_aes_encrypt_blocks") Proof.Aes.RISCV64.encryptBlocks_correct
      Proof.Aes.RISCV64.encryptBlocks_ct (P := fun s₁ s₂ =>
      SkMid s₀ (s₀.gpr .a0) (s₀.gpr .a2) (s₀.gpr .a3) (s₀.gpr .a1).toNat s₁ ∧
      SkMid s₀' (s₀.gpr .a0) (s₀.gpr .a2) (s₀.gpr .a3) (s₀.gpr .a1).toNat s₂) fun s₁ s₂ h =>
      ⟨h.1.pre, h.2.pre, by rw [h.1.sp, h.2.sp, q5]⟩).wp
    (F₁ := fun (s : State) => s.gpr .s1 = s₀.gpr .a2 ∧ s.gpr .s2 = s₀.gpr .a3 ∧ s.sp = s₀.sp)
    (F₂ := fun (s : State) => s.gpr .s1 = s₀.gpr .a2 ∧ s.gpr .s2 = s₀.gpr .a3 ∧ s.sp = s₀'.sp)
    fun s₁ s₂ h =>
      ⟨WP.mono (blk_call Proof.Aes.RISCV64.encryptBlocks_correct encryptBlocks_noFrames h.1.pre)
        fun _ hc => ⟨by rw [hc.saved .s1 (by decide), h.1.s1], by rw [hc.saved .s2 (by decide), h.1.s2],
          by rw [hc.sp, h.1.sp]⟩,
       WP.mono (blk_call Proof.Aes.RISCV64.encryptBlocks_correct encryptBlocks_noFrames h.2.pre)
        fun _ hc => ⟨by rw [hc.saved .s1 (by decide), h.2.s1], by rw [hc.saved .s2 (by decide), h.2.s2],
          by rw [hc.sp, h.2.sp]⟩⟩
  have b := taintRegs
    (P := fun s₁ s₂ => (s₁.gpr .s1 = s₀.gpr .a2 ∧ s₁.gpr .s2 = s₀.gpr .a3 ∧ s₁.sp = s₀.sp) ∧
      (s₂.gpr .s1 = s₀.gpr .a2 ∧ s₂.gpr .s2 = s₀.gpr .a3 ∧ s₂.sp = s₀'.sp)) [.s1, .s2]
    (fun s₁ s₂ h => ⟨by rw [h.1.2.2, h.2.2.2, q5], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.1, h.2.1]
      · rw [h.1.2.1, h.2.2.1]⟩) hB
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((c.mono (fun _ _ h => h) fun _ _ h => h.2).seq b)

theorem subkeys_ct : ConstantTime isa subkeysRISCV64.pre subkeysRISCV64.pub subkeys :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (subkeys_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## `vg_cmac_aes_finalize` -/

theorem finalize_rel {s₀ s₀' : State} (h0 : finalizeRISCV64.pre s₀) (h0' : finalizeRISCV64.pre s₀')
    (hq : finalizeRISCV64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') finalize fun _ _ => True := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := hq
  have hp := FPre.of h0
  have hp' : FPre s₀' (s₀.gpr .a0) (s₀.gpr .a2) (s₀.gpr .a3) (s₀.gpr .a5) (s₀.gpr .a4).toNat
      (s₀.gpr .a1).toNat := by
    rw [q1, q2, q3, q4, q5, q6]; exact FPre.of h0'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5]) finPre h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.s1]) (.block finRestore) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := (taintRegs (P := fun a b => a = s₀ ∧ b = s₀') [.a0, .a1, .a2, .a3, .a4, .a5]
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨q7, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption) hA).wp
    (F₁ := FMid s₀ (s₀.gpr .a0) (s₀.gpr .a2) (s₀.gpr .a3) (s₀.gpr .a5) (s₀.gpr .a4).toNat (s₀.gpr .a1).toNat)
    (F₂ := FMid s₀' (s₀.gpr .a0) (s₀.gpr .a2) (s₀.gpr .a3) (s₀.gpr .a5) (s₀.gpr .a4).toNat (s₀.gpr .a1).toNat)
    fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨finPre_wp hp, finPre_wp hp'⟩
  have c := (blk_rel (name := "vg_aes_encrypt_blocks") Proof.Aes.RISCV64.encryptBlocks_correct
      Proof.Aes.RISCV64.encryptBlocks_ct (P := fun s₁ s₂ =>
      FMid s₀ (s₀.gpr .a0) (s₀.gpr .a2) (s₀.gpr .a3) (s₀.gpr .a5) (s₀.gpr .a4).toNat (s₀.gpr .a1).toNat s₁ ∧
      FMid s₀' (s₀.gpr .a0) (s₀.gpr .a2) (s₀.gpr .a3) (s₀.gpr .a5) (s₀.gpr .a4).toNat (s₀.gpr .a1).toNat s₂)
      fun s₁ s₂ h => ⟨h.1.pre, h.2.pre, by rw [h.1.sp, h.2.sp, q7]⟩).wp
    (F₁ := fun (s : State) => s.gpr .s1 = s₀.gpr .a5 ∧ s.sp = s₀.sp)
    (F₂ := fun (s : State) => s.gpr .s1 = s₀.gpr .a5 ∧ s.sp = s₀'.sp) fun s₁ s₂ h =>
      ⟨WP.mono (blk_call Proof.Aes.RISCV64.encryptBlocks_correct encryptBlocks_noFrames h.1.pre)
        fun _ hc => ⟨by rw [hc.saved .s1 (by decide), h.1.s1], by rw [hc.sp, h.1.sp]⟩,
       WP.mono (blk_call Proof.Aes.RISCV64.encryptBlocks_correct encryptBlocks_noFrames h.2.pre)
        fun _ hc => ⟨by rw [hc.saved .s1 (by decide), h.2.s1], by rw [hc.sp, h.2.sp]⟩⟩
  have b := taintRegs
    (P := fun s₁ s₂ => (s₁.gpr .s1 = s₀.gpr .a5 ∧ s₁.sp = s₀.sp) ∧ (s₂.gpr .s1 = s₀.gpr .a5 ∧ s₂.sp = s₀'.sp))
    [.s1] (fun s₁ s₂ h => ⟨by rw [h.1.2, h.2.2, q7], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [h.1.1, h.2.1]⟩) hB
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((c.mono (fun _ _ h => h) fun _ _ h => h.2).seq b)

theorem finalize_ct : ConstantTime isa finalizeRISCV64.pre finalizeRISCV64.pub finalize :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (finalize_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.RISCV64

end

end

/-!
# AES-CMAC on RISC-V: `Verified`

Correctness and constant time (of `update` from the chain's, `wrap_wp` and
`wrap_ct`, `Proof/AesCbc/RISCV64/Chain.lean`: the blocks chained into the
state), a state satisfying each precondition, and the shared contracts of
`Spec/Cmac/Contract.lean` (with no stack: a call stores
nothing in memory, and each function saves the return address in the
scratch buffer).
-/

@[expose] public section

namespace VG.Proof.CmacAes.RISCV64

open VG VG.RISCV64 VG.Impl.CmacAes.RISCV64

theorem subkeys_correct (s : State) (hs : subkeysRISCV64.pre s) :
    ∃ t s', Exec isa subkeys s t s' ∧ abiPreserved s s' ∧ subkeysRISCV64.post s s' := by
  obtain ⟨t, s', he, hg, hra, hsp, hp⟩ := subkeys_wp hs
  exact ⟨t, s', he, ⟨hg, hsp, hra⟩, hp⟩

/-- `update`'s precondition, the chain's (with the scratch buffer of 2176 bytes). -/
theorem update_wpre {s : State} (hs : updateRISCV64.pre s) :
    Proof.AesCbc.RISCV64.WPre false (16 * ·) s :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k⟩ := hs
  ⟨a, b, c, d, e, f, g, h, i, j, k⟩

theorem update_correct (s : State) (hs : updateRISCV64.pre s) :
    ∃ t s', Exec isa update s t s' ∧ abiPreserved s s' ∧ updateRISCV64.post s s' := by
  obtain ⟨t, s', he, hg, hra, hsp, hp, -⟩ :=
    Proof.AesCbc.RISCV64.wrap_wp (Proof.AesCbc.RISCV64.chain_k false) (name := "vg_aes_mac_chain")
      (update_wpre hs)
  exact ⟨t, s', he, ⟨hg, hsp, hra⟩, hp⟩

theorem update_ct : ConstantTime isa updateRISCV64.pre updateRISCV64.pub update :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    Proof.AesCbc.RISCV64.wrap_ct (Proof.AesCbc.RISCV64.chain_k false) "vg_aes_mac_chain" _ _ _ _ _ _
      (update_wpre h₁) (update_wpre h₂) hq e₁ e₂

theorem finalize_correct (s : State) (hs : finalizeRISCV64.pre s) :
    ∃ t s', Exec isa finalize s t s' ∧ abiPreserved s s' ∧ finalizeRISCV64.post s s' := by
  obtain ⟨t, s', he, hg, hra, hsp, hp⟩ := finalize_wp hs
  exact ⟨t, s', he, ⟨hg, hsp, hra⟩, hp⟩

end VG.Proof.CmacAes.RISCV64

end

end

/-!
# Streaming AES-CMAC on RISC-V: the contracts, the calls and the copies

As on PPC64LE (`Proof/CmacAes/Stream/PPC64LE/Common.lean`). The artifacts'
contracts are the shared ones of `Spec/Cmac/Contract.lean`, with the working
space appended (`Proof/CmacAes/Stream/Scratch.lean`), which imply these
(`Verified.lean`). A call (`jal`) stores nothing in memory, so no stack is
used.

A call of each function the streaming functions call
(`vg_aes_expand_key_scratch`, `vg_cmac_aes_subkeys`, `vg_cmac_aes_update` and
`vg_cmac_aes_finalize`), from its contract (with `WP.call`): what it needs
(`…Args`), what it leaves (`…Post`, in terms of the memory before the call),
and that two calls with the same arguments leak the same (`…_rel`). The
callees change only the buffers they are given, and keep every callee-saved
register. Then the number of bytes held back, as the code computes it from
`count` (`held_bv`), and `copy`, which copies the `t2` bytes at `t6` to
`t5`, a byte at a time (none if `t2` is 0), changing only `t2`, `t3`, `t5`
and `t6`.
-/

@[expose] public section

namespace VG.Proof.CmacAes.Stream.RISCV64

open VG VG.RISCV64
open VG.Proof.CmacAes.RISCV64 (subkeysRISCV64 updateRISCV64 finalizeRISCV64)
open VG.Proof.AesCbc.RISCV64 (toNat_rounds)

/-! ## The contracts -/

/-- `vg_cmac_aes_init(state = a0, key = a1, key_len = a2, scratch = a3)`. -/
def initRISCV64 : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 304⟩
    let key : Region := ⟨s.gpr .a1, (s.gpr .a2).toNat⟩
    let scr : Region := ⟨s.gpr .a3, 2304⟩
    s.rd = [key] ∧ s.wr = [state, scr] ∧
      state.Disjoint key ∧ state.Disjoint scr ∧ key.Disjoint scr ∧
      (s.gpr .a0).toNat + 304 ≤ 2 ^ 64 ∧ (s.gpr .a1).toNat + (s.gpr .a2).toNat ≤ 2 ^ 64 ∧
      (s.gpr .a3).toNat + 2304 ≤ 2 ^ 64 ∧
      ((s.gpr .a2).toNat = 16 ∨ (s.gpr .a2).toNat = 24 ∨ (s.gpr .a2).toNat = 32)
  post s s' :=
    Spec.Cmac.Repr s'.mem (s.gpr .a0) (Spec.Aes.bytesAt s.mem (s.gpr .a1) (s.gpr .a2).toNat) []
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp

/-- `vg_cmac_aes_absorb(state = a0, rounds = a1, count = a2, data = a3, len = a4, scratch = a5)`. -/
def absorbRISCV64 : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 304⟩
    let data : Region := ⟨s.gpr .a3, (s.gpr .a4).toNat⟩
    let scr : Region := ⟨s.gpr .a5, 2304⟩
    s.rd = [data] ∧ s.wr = [state, scr] ∧
      state.Disjoint data ∧ state.Disjoint scr ∧ data.Disjoint scr ∧
      (s.gpr .a0).toNat + 304 ≤ 2 ^ 64 ∧ (s.gpr .a3).toNat + (s.gpr .a4).toNat ≤ 2 ^ 64 ∧
      (s.gpr .a5).toNat + 2304 ≤ 2 ^ 64 ∧
      ((s.gpr .a1).toNat = 10 ∨ (s.gpr .a1).toNat = 12 ∨ (s.gpr .a1).toNat = 14)
  post s s' :=
    ∀ key msg, Spec.Cmac.Repr s.mem (s.gpr .a0) key msg →
      (s.gpr .a1).toNat = Spec.Aes.rounds (key.length / 4) →
      s.gpr .a2 = BitVec.ofNat 64 msg.length → msg.length + (s.gpr .a4).toNat < 2 ^ 64 →
      Spec.Cmac.Repr s'.mem (s.gpr .a0) key
        (msg ++ Spec.Aes.bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat)
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧ s₁.sp = s₂.sp

/-- `vg_cmac_aes_finish(state = a0, rounds = a1, count = a2, out = a3, scratch = a4)`. -/
def finishRISCV64 : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 304⟩
    let out : Region := ⟨s.gpr .a3, 16⟩
    let scr : Region := ⟨s.gpr .a4, 2304⟩
    s.rd = [] ∧ s.wr = [state, out, scr] ∧
      state.Disjoint out ∧ state.Disjoint scr ∧ out.Disjoint scr ∧
      (s.gpr .a0).toNat + 304 ≤ 2 ^ 64 ∧ (s.gpr .a3).toNat + 16 ≤ 2 ^ 64 ∧
      (s.gpr .a4).toNat + 2304 ≤ 2 ^ 64 ∧
      ((s.gpr .a1).toNat = 10 ∨ (s.gpr .a1).toNat = 12 ∨ (s.gpr .a1).toNat = 14)
  post s s' :=
    ∀ key msg, Spec.Cmac.Repr s.mem (s.gpr .a0) key msg →
      (s.gpr .a1).toNat = Spec.Aes.rounds (key.length / 4) →
      s.gpr .a2 = BitVec.ofNat 64 msg.length → msg.length < 2 ^ 64 →
      Spec.Aes.bytesAt s'.mem (s.gpr .a3) 16 = Spec.Cmac.aesCmac key 16 msg
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.sp = s₂.sp

/-! ## Arithmetic -/

theorem toNat_ofNat {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem ofNat_toNat_eq {x : BitVec 64} {n : Nat} (h : x.toNat = n) : x = BitVec.ofNat 64 n :=
  BitVec.eq_of_toNat_eq (by rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (h ▸ x.isLt)])

theorem toNat_add_lt (p : Addr) {d k : Nat} (h : p.toNat + k ≤ 2 ^ 64) (hd : d < k) :
    (p + BitVec.ofNat 64 d).toNat = p.toNat + d := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [h, hd] : d < 2 ^ 64)]
  exact Nat.mod_eq_of_lt (by omega_using [h, hd])

theorem and15 (x : BitVec 64) : (x &&& BitVec.ofInt 64 15).toNat = x.toNat % 16 := by
  rw [BitVec.toNat_and, show (BitVec.ofInt 64 15).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

open VG.Proof.Cmac.Stream (held held_pos) in
/-- The number of bytes held back for a nonzero `count`, as `addi -1; andi 15; addi 1` computes it. -/
theorem held_bv (c : BitVec 64) (h : c ≠ 0) :
    ((c - BitVec.ofNat 64 1) &&& BitVec.ofInt 64 15) + BitVec.ofNat 64 1 = BitVec.ofNat 64 (held c.toNat) := by
  have hc : c.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
  rw [held_pos (by omega_using [hc])]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, and15, BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat]
  have := c.isLt
  omega_using [hc]

/-- The rounds, as `srli 2; addi 6` computes them from the key length. -/
theorem rounds_bv {KL : Nat} (h : KL = 16 ∨ KL = 24 ∨ KL = 32) :
    BitVec.ofNat 64 KL >>> 2 + BitVec.ofNat 64 6 = BitVec.ofNat 64 (KL / 4 + 6) := by
  rcases h with rfl | rfl | rfl <;> decide

theorem shr_ofNat {n k : Nat} (hn : n < 2 ^ 64) : BitVec.ofNat 64 n >>> k = BitVec.ofNat 64 (n / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (by have := Nat.div_le_self n (2 ^ k); omega_using [hn, this])]

theorem preserved_ne (r : Reg) (hr : r ∈ preserved) :
    r ≠ .t0 ∧ r ≠ .t1 ∧ r ≠ .t2 ∧ r ≠ .t3 ∧ r ≠ .t4 ∧ r ≠ .t5 ∧ r ≠ .t6 ∧ r ≠ .ra ∧ r ≠ .a0 ∧
      r ≠ .a1 ∧ r ≠ .a2 ∧ r ≠ .a3 ∧ r ≠ .a4 ∧ r ≠ .a5 ∧ r ≠ .a6 ∧ r ≠ .a7 := by
  revert hr; cases r <;> decide

theorem in_wr {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n := by
  obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩

/-! ## Saving registers -/

/-- `addi 2047`, `addi 136` then `andi -8`: `x + 2176` rounded up. -/
theorem sv2_arith (x : Addr) :
    (x + BitVec.ofInt 64 2047 + BitVec.ofInt 64 136) &&& BitVec.ofInt 64 (-8) =
      x + BitVec.ofNat 64 2176 + BitVec.ofNat 64 (Align.pad (x + BitVec.ofNat 64 2176)) := by
  rw [← Align.align_eq, BitVec.add_assoc, BitVec.add_assoc,
    show BitVec.ofInt 64 2047 + BitVec.ofInt 64 136 = BitVec.ofNat 64 2176 + BitVec.ofInt 64 7 by decide]

/-- Where the streaming functions save the registers, from the scratch
buffer `S`: `S + 2176` rounded up to a multiple of 8. -/
abbrev sv2 (S : Addr) : Addr :=
  S + BitVec.ofNat 64 2176 + BitVec.ofNat 64 (Align.pad (S + BitVec.ofNat 64 2176))

/-- `t0 :=` the register `n`'s value plus 2176, rounded up. -/
theorem savePtr2_ok {s : State} (n : Reg) :
    WP isa (.block (Impl.CmacAes.Stream.RISCV64.savePtr2 n)) s (· = s.write .t0 (sv2 (s.gpr n))) := by
  apply WP.of_runBlock
  simp only [Impl.CmacAes.Stream.RISCV64.savePtr2, runBlock_cons, runStep_some, runBlock_nil,
    exec_addi (show imm12 2047 by decide), exec_addi (show imm12 136 by decide),
    exec_logicImm (show imm12 (-8) by decide), RegUpd.gpr_write_self, RegUpd.write_write, Option.some.injEq,
    exists_eq_left']
  rw [sv2_arith]

theorem sv2_add (S : Addr) (d : Nat) :
    sv2 S + BitVec.ofNat 64 d = S + BitVec.ofNat 64 (2176 + Align.pad (S + BitVec.ofNat 64 2176) + d) :=
  Align.align_add _ _ _

/-- A slot at `sv2 S + d`, within the scratch buffer. -/
theorem sv2_sub (S : Addr) {d n : Nat} (h : d + n ≤ 121) : Region.Sub ⟨sv2 S + BitVec.ofNat 64 d, n⟩ ⟨S, 2304⟩ := by
  have := Align.pad_lt (S + BitVec.ofNat 64 2176)
  rw [sv2_add]; exact Offset.sub_base _ (by omega_using [h, this])

theorem sv2_contains (S : Addr) {d n : Nat} (h : d + n ≤ 121) :
    (⟨S, 2304⟩ : Region).Contains (sv2 S + BitVec.ofNat 64 d) n := by
  have := Align.pad_lt (S + BitVec.ofNat 64 2176)
  rw [sv2_add]; exact Offset.contains_base _ (by omega_using [h, this]) (by omega_using [h, this])

/-- A slot at `sv2 S + d`, above the callees' working space. -/
theorem sv2_ws (S : Addr) {d n : Nat} (h : d + n ≤ 121) :
    Region.Disjoint ⟨sv2 S + BitVec.ofNat 64 d, n⟩ ⟨S, 2176⟩ := by
  have := Align.pad_lt (S + BitVec.ofNat 64 2176)
  rw [sv2_add]; exact Offset.disjoint_base _ (by omega_using []) (by omega_using [h, this])

/-- Slots holding registers whose values agree hold either's. -/
theorem saved_congr {B : Addr} {g g' : Reg → BitVec 64} {l : List (Reg × Nat)} {m : Mem}
    (h : Spill.Saved B g l m) (hg : ∀ p ∈ l, g p.1 = g' p.1) : Spill.Saved B g' l m :=
  fun p hp => (h p hp).trans (hg p hp)

/-! ## No frames -/

theorem expandKey_noFrames : Impl.Aes.RISCV64.expandKey.noFrames = true := by lit_decide

theorem subkeys_noFrames : Impl.CmacAes.RISCV64.subkeys.noFrames = true := by
  simp [Impl.CmacAes.RISCV64.subkeys, Impl.AesCbc.RISCV64.encCall, Code.noFrames]
  exact Proof.AesCbc.RISCV64.encryptBlocks_noFrames

theorem update_noFrames : Impl.CmacAes.RISCV64.update.noFrames = true := by
  simp only [Impl.CmacAes.RISCV64.update, Impl.Aes.RISCV64.macChainCall, Code.noFrames, Bool.and_true,
    Bool.true_and]
  exact (Proof.AesCbc.RISCV64.chain_k false).noFrames

theorem finalize_noFrames : Impl.CmacAes.RISCV64.finalize.noFrames = true := by
  simp [Impl.CmacAes.RISCV64.finalize, Impl.CmacAes.RISCV64.finPre, Impl.CmacAes.RISCV64.partialBlock,
    Impl.CmacAes.RISCV64.xorLoop, Impl.AesCbc.RISCV64.encCall, Code.noFrames]
  exact Proof.AesCbc.RISCV64.encryptBlocks_noFrames

/-! ## `vg_cmac_aes_update` -/

/-- What a call of `vg_cmac_aes_update` needs: the key schedule `W`, the
chaining value `C`, `n` blocks at `D`, the working space `S` and the rounds
`R`. -/
structure UArgs (s : State) (W C D S : Addr) (R n : Nat) : Prop where
  a0 : s.gpr .a0 = W
  a1 : s.gpr .a1 = BitVec.ofNat 64 R
  a2 : s.gpr .a2 = C
  a3 : s.gpr .a3 = D
  a4 : s.gpr .a4 = BitVec.ofNat 64 n
  a5 : s.gpr .a5 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  hn : 16 * n < 2 ^ 64
  wc : (⟨W, 240⟩ : Region).Disjoint ⟨C, 16⟩
  ws : (⟨W, 240⟩ : Region).Disjoint ⟨S, 2176⟩
  dc : (⟨D, 16 * n⟩ : Region).Disjoint ⟨C, 16⟩
  ds : (⟨D, 16 * n⟩ : Region).Disjoint ⟨S, 2176⟩
  cs : (⟨C, 16⟩ : Region).Disjoint ⟨S, 2176⟩
  wrapC : C.toNat + 16 ≤ 2 ^ 64
  wrapD : D.toNat + 16 * n ≤ 2 ^ 64
  wrapS : S.toNat + 2176 ≤ 2 ^ 64
  reads : Covers ([⟨W, 240⟩, ⟨D, 16 * n⟩] ++ [⟨C, 16⟩, ⟨S, 2176⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨C, 16⟩, ⟨S, 2176⟩] s.wr

/-- What a call of `vg_cmac_aes_update` leaves. -/
structure UPost (s : State) (W C D S : Addr) (R n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  frame : Frame [⟨C, 16⟩, ⟨S, 2176⟩] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem C 16 =
    Spec.Cmac.chain (Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem W (16 * (R + 1))))
      (Spec.Aes.bytesAt s.mem C 16) (Spec.Cmac.blocksAt s.mem D 16 n)

theorem UArgs.pre {s : State} {W C D S : Addr} {R n : Nat} (h : UArgs s W C D S R n) :
    updateRISCV64.pre (s.callEntry.withRegions [⟨W, 240⟩, ⟨D, 16 * n⟩] [⟨C, 16⟩, ⟨S, 2176⟩]) := by
  have hR := toNat_rounds h.rounds
  have hN := toNat_ofNat (n := n) (by have := h.hn; omega_using [this])
  simp only [updateRISCV64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a3 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a4 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a5 ∉ linkRegs),
    h.a0, h.a1, h.a2, h.a3, h.a4, h.a5, hR, hN]
  exact ⟨trivial, trivial, h.wc, h.ws, h.dc, h.ds, h.cs, h.wrapC, h.wrapD, h.wrapS, h.rounds⟩

theorem upd_call {s : State} {W C D S : Addr} {R n : Nat} (h : UArgs s W C D S R n) :
    WP isa Impl.CmacAes.Stream.RISCV64.updCall s (UPost s W C D S R n) := by
  have hR := toNat_rounds h.rounds
  have hN := toNat_ofNat (n := n) (by have := h.hn; omega_using [this])
  refine WP.call (k := updateRISCV64) Proof.CmacAes.RISCV64.update_correct h.pre h.reads h.writes ?_
    update_noFrames
  intro s' hrd hwr hsp hf hsaved _ hpost
  refine ⟨hrd, hwr, hsp, hsaved, hf, ?_⟩
  simp only [updateRISCV64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a3 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a4 ∉ linkRegs), h.a0, h.a1, h.a2, h.a3, h.a4, hR, hN] at hpost
  exact hpost

theorem upd_rel {W C D S : Addr} {R n : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → UArgs s₁ W C D S R n ∧ UArgs s₂ W C D S R n ∧ s₁.sp = s₂.sp) :
    RelCT isa P Impl.CmacAes.Stream.RISCV64.updCall fun _ _ => True := by
  refine RelCT.call Proof.CmacAes.RISCV64.update_correct Proof.CmacAes.RISCV64.update_ct
    [⟨W, 240⟩, ⟨D, 16 * n⟩] [⟨C, 16⟩, ⟨S, 2176⟩] fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes⟩
  simp only [updateRISCV64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    State.callEntry_gpr _ (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.a2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.a3 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.a4 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.a5 ∉ linkRegs),
    h₁.a0, h₁.a1, h₁.a2, h₁.a3, h₁.a4, h₁.a5, h₂.a0, h₂.a1, h₂.a2, h₂.a3, h₂.a4, h₂.a5, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## `vg_cmac_aes_subkeys` -/

/-- What a call of `vg_cmac_aes_subkeys` needs: the key schedule `W`, the
subkeys `K`, the working space `S` and the rounds `R`. -/
structure SArgs (s : State) (W K S : Addr) (R : Nat) : Prop where
  a0 : s.gpr .a0 = W
  a1 : s.gpr .a1 = BitVec.ofNat 64 R
  a2 : s.gpr .a2 = K
  a3 : s.gpr .a3 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  wk : (⟨W, 240⟩ : Region).Disjoint ⟨K, 32⟩
  ws : (⟨W, 240⟩ : Region).Disjoint ⟨S, 2176⟩
  ks : (⟨K, 32⟩ : Region).Disjoint ⟨S, 2176⟩
  wrapK : K.toNat + 32 ≤ 2 ^ 64
  wrapS : S.toNat + 2176 ≤ 2 ^ 64
  reads : Covers ([⟨W, 240⟩] ++ [⟨K, 32⟩, ⟨S, 2176⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨K, 32⟩, ⟨S, 2176⟩] s.wr

/-- What a call of `vg_cmac_aes_subkeys` leaves. -/
structure SPost (s : State) (W K S : Addr) (R : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  frame : Frame [⟨K, 32⟩, ⟨S, 2176⟩] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem K 32 =
    (Spec.Cmac.subkeys (Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem W (16 * (R + 1)))) 16).1 ++
      (Spec.Cmac.subkeys (Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem W (16 * (R + 1)))) 16).2

theorem SArgs.pre {s : State} {W K S : Addr} {R : Nat} (h : SArgs s W K S R) :
    subkeysRISCV64.pre (s.callEntry.withRegions [⟨W, 240⟩] [⟨K, 32⟩, ⟨S, 2176⟩]) := by
  have hR := toNat_rounds h.rounds
  simp only [subkeysRISCV64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a3 ∉ linkRegs),
    h.a0, h.a1, h.a2, h.a3, hR]
  exact ⟨trivial, trivial, h.wk, h.ws, h.ks, h.wrapK, h.wrapS, h.rounds⟩

theorem sub_call {s : State} {W K S : Addr} {R : Nat} (h : SArgs s W K S R) :
    WP isa Impl.CmacAes.Stream.RISCV64.skCall s (SPost s W K S R) := by
  have hR := toNat_rounds h.rounds
  refine WP.call (k := subkeysRISCV64) Proof.CmacAes.RISCV64.subkeys_correct h.pre h.reads h.writes ?_
    subkeys_noFrames
  intro s' hrd hwr hsp hf hsaved _ hpost
  refine ⟨hrd, hwr, hsp, hsaved, hf, ?_⟩
  simp only [subkeysRISCV64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs), h.a0, h.a1, h.a2, hR] at hpost
  exact hpost

theorem sub_rel {W K S : Addr} {R : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → SArgs s₁ W K S R ∧ SArgs s₂ W K S R ∧ s₁.sp = s₂.sp) :
    RelCT isa P Impl.CmacAes.Stream.RISCV64.skCall fun _ _ => True := by
  refine RelCT.call Proof.CmacAes.RISCV64.subkeys_correct Proof.CmacAes.RISCV64.subkeys_ct
    [⟨W, 240⟩] [⟨K, 32⟩, ⟨S, 2176⟩] fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes⟩
  simp only [subkeysRISCV64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    State.callEntry_gpr _ (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.a2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.a3 ∉ linkRegs),
    h₁.a0, h₁.a1, h₁.a2, h₁.a3, h₂.a0, h₂.a1, h₂.a2, h₂.a3, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

/-! ## `vg_cmac_aes_finalize` -/

/-- What a call of `vg_cmac_aes_finalize` needs: the key schedule and
subkeys `K`, the state `St`, the `L` last bytes at `P`, the working space
`S` and the rounds `R`. -/
structure FArgs (s : State) (K St P S : Addr) (L R : Nat) : Prop where
  a0 : s.gpr .a0 = K
  a1 : s.gpr .a1 = BitVec.ofNat 64 R
  a2 : s.gpr .a2 = St
  a3 : s.gpr .a3 = P
  a4 : s.gpr .a4 = BitVec.ofNat 64 L
  a5 : s.gpr .a5 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  len : L ≤ 16
  kst : (⟨K, 272⟩ : Region).Disjoint ⟨St, 16⟩
  ks : (⟨K, 272⟩ : Region).Disjoint ⟨S, 2176⟩
  pst : (⟨P, L⟩ : Region).Disjoint ⟨St, 16⟩
  ps : (⟨P, L⟩ : Region).Disjoint ⟨S, 2176⟩
  sts : (⟨St, 16⟩ : Region).Disjoint ⟨S, 2176⟩
  wrapK : K.toNat + 272 ≤ 2 ^ 64
  wrapSt : St.toNat + 16 ≤ 2 ^ 64
  wrapP : P.toNat + L ≤ 2 ^ 64
  wrapS : S.toNat + 2176 ≤ 2 ^ 64
  reads : Covers ([⟨K, 272⟩, ⟨P, L⟩] ++ [⟨St, 16⟩, ⟨S, 2176⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨St, 16⟩, ⟨S, 2176⟩] s.wr

/-- What a call of `vg_cmac_aes_finalize` leaves. -/
structure FPost (s : State) (K St P S : Addr) (L R : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  frame : Frame [⟨St, 16⟩, ⟨S, 2176⟩] s.mem s'.mem
  out : let ciph := Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem K (16 * (R + 1)))
    let ks := Spec.Cmac.subkeys ciph 16
    Spec.Aes.bytesAt s.mem (K + 240) 32 = ks.1 ++ ks.2 →
    ∀ msg : List Byte, msg.length % 16 = 0 → (msg = [] ∨ 0 < L) →
      Spec.Aes.bytesAt s.mem St 16 = Spec.Cmac.chain ciph (Spec.Cmac.zeros 16) (Spec.Cmac.blocks 16 msg) →
      Spec.Aes.bytesAt s'.mem St 16 = Spec.Cmac.macFull ciph 16 (msg ++ Spec.Aes.bytesAt s.mem P L)

theorem FArgs.pre {s : State} {K St P S : Addr} {L R : Nat} (h : FArgs s K St P S L R) :
    finalizeRISCV64.pre (s.callEntry.withRegions [⟨K, 272⟩, ⟨P, L⟩] [⟨St, 16⟩, ⟨S, 2176⟩]) := by
  have hR := toNat_rounds h.rounds
  have hL := toNat_ofNat (n := L) (by have := h.len; omega_using [this])
  simp only [finalizeRISCV64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a3 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a4 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a5 ∉ linkRegs),
    h.a0, h.a1, h.a2, h.a3, h.a4, h.a5, hR, hL]
  exact ⟨trivial, trivial, h.kst, h.ks, h.pst, h.ps, h.sts, h.wrapK, h.wrapSt, h.wrapP, h.wrapS,
    h.rounds, h.len⟩

theorem fin_call {s : State} {K St P S : Addr} {L R : Nat} (h : FArgs s K St P S L R) :
    WP isa Impl.CmacAes.Stream.RISCV64.finCall s (FPost s K St P S L R) := by
  have hR := toNat_rounds h.rounds
  have hL := toNat_ofNat (n := L) (by have := h.len; omega_using [this])
  refine WP.call (k := finalizeRISCV64) Proof.CmacAes.RISCV64.finalize_correct h.pre h.reads h.writes ?_
    finalize_noFrames
  intro s' hrd hwr hsp hf hsaved _ hpost
  refine ⟨hrd, hwr, hsp, hsaved, hf, ?_⟩
  simp only [finalizeRISCV64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a3 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a4 ∉ linkRegs), h.a0, h.a1, h.a2, h.a3, h.a4, hR, hL] at hpost
  exact hpost

theorem fin_rel {K St Q S : Addr} {L R : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → FArgs s₁ K St Q S L R ∧ FArgs s₂ K St Q S L R ∧ s₁.sp = s₂.sp) :
    RelCT isa P Impl.CmacAes.Stream.RISCV64.finCall fun _ _ => True := by
  refine RelCT.call Proof.CmacAes.RISCV64.finalize_correct Proof.CmacAes.RISCV64.finalize_ct
    [⟨K, 272⟩, ⟨Q, L⟩] [⟨St, 16⟩, ⟨S, 2176⟩] fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes⟩
  simp only [finalizeRISCV64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    State.callEntry_gpr _ (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.a2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.a3 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.a4 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.a5 ∉ linkRegs),
    h₁.a0, h₁.a1, h₁.a2, h₁.a3, h₁.a4, h₁.a5, h₂.a0, h₂.a1, h₂.a2, h₂.a3, h₂.a4, h₂.a5, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## `vg_aes_expand_key_scratch` -/

/-- What a call of `vg_aes_expand_key_scratch` needs: the key `Kp` of `KL`
bytes, the schedule `W` and the working space `S`. -/
structure EArgs (s : State) (Kp W S : Addr) (KL : Nat) : Prop where
  a0 : s.gpr .a0 = Kp
  a1 : s.gpr .a1 = BitVec.ofNat 64 KL
  a2 : s.gpr .a2 = W
  a3 : s.gpr .a3 = S
  klen : KL = 16 ∨ KL = 24 ∨ KL = 32
  kw : (⟨Kp, KL⟩ : Region).Disjoint ⟨W, 240⟩
  ks : (⟨Kp, KL⟩ : Region).Disjoint ⟨S, 512⟩
  ws : (⟨W, 240⟩ : Region).Disjoint ⟨S, 512⟩
  reads : Covers ([⟨Kp, KL⟩] ++ [⟨W, 240⟩, ⟨S, 512⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨W, 240⟩, ⟨S, 512⟩] s.wr

/-- What a call of `vg_aes_expand_key_scratch` leaves. -/
structure EPost (s : State) (Kp W S : Addr) (KL : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  frame : Frame [⟨W, 240⟩, ⟨S, 512⟩] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem W (16 * (Spec.Aes.rounds (KL / 4) + 1)) =
    Spec.Aes.expandKey (Spec.Aes.bytesAt s.mem Kp KL)

theorem EArgs.pre {s : State} {Kp W S : Addr} {KL : Nat} (h : EArgs s Kp W S KL) :
    Proof.Aes.expandKeyRISCV64.pre (s.callEntry.withRegions [⟨Kp, KL⟩] [⟨W, 240⟩, ⟨S, 512⟩]) := by
  have hK := toNat_ofNat (n := KL) (by rcases h.klen with h | h | h <;> omega_using [h])
  simp only [Proof.Aes.expandKeyRISCV64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a3 ∉ linkRegs),
    h.a0, h.a1, h.a2, h.a3, hK]
  exact ⟨trivial, trivial, h.kw, h.ks, h.ws, h.klen⟩

theorem ek_call {s : State} {Kp W S : Addr} {KL : Nat} (h : EArgs s Kp W S KL) :
    WP isa Impl.CmacAes.Stream.RISCV64.ekCall s (EPost s Kp W S KL) := by
  have hK := toNat_ofNat (n := KL) (by rcases h.klen with h | h | h <;> omega_using [h])
  refine WP.call (k := Proof.Aes.expandKeyRISCV64) Proof.Aes.RISCV64.expandKey_correct h.pre h.reads
    h.writes ?_ expandKey_noFrames
  intro s' hrd hwr hsp hf hsaved _ hpost
  refine ⟨hrd, hwr, hsp, hsaved, hf, ?_⟩
  simp only [Proof.Aes.expandKeyRISCV64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs), h.a0, h.a1, h.a2, hK] at hpost
  exact hpost

theorem ek_rel {Kp W S : Addr} {KL : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → EArgs s₁ Kp W S KL ∧ EArgs s₂ Kp W S KL ∧ s₁.sp = s₂.sp) :
    RelCT isa P Impl.CmacAes.Stream.RISCV64.ekCall fun _ _ => True := by
  refine RelCT.call Proof.Aes.RISCV64.expandKey_correct Proof.Aes.RISCV64.expandKey_ct
    [⟨Kp, KL⟩] [⟨W, 240⟩, ⟨S, 512⟩] fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes⟩
  simp only [Proof.Aes.expandKeyRISCV64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    State.callEntry_gpr _ (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.a2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.a3 ∉ linkRegs),
    h₁.a0, h₁.a1, h₁.a2, h₁.a3, h₂.a0, h₂.a1, h₂.a2, h₂.a3, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

/-! ## Bytes written -/

open VG.WriteBytes

theorem writeBytes_at (m : Mem) (q : Addr) (xs : List Byte) {i : Nat} (hi : i < 2 ^ 64) :
    writeBytes m q xs (q + BitVec.ofNat 64 i) =
      if i < xs.length then xs.getD i 0 else m (q + BitVec.ofNat 64 i) := by
  simp only [writeBytes, Mem.sub_ofNat_toNat q hi]

theorem bytesAt_writeBytes_self (m : Mem) (q : Addr) {xs : List Byte} (h : xs.length < 2 ^ 64) :
    Spec.Aes.bytesAt (writeBytes m q xs) q xs.length = xs := by
  apply List.ext_getElem (by simp [Spec.Aes.bytesAt])
  intro i h1 _
  simp only [Spec.Aes.bytesAt, List.length_map, List.length_range] at h1
  simp only [Spec.Aes.bytesAt, List.getElem_map, List.getElem_range, writeBytes_at m q xs (by omega_arith : i < 2 ^ 64),
    h1, ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some]

/-- Bytes `[0, r)` from `p` stay, and the bytes `xs` follow them. -/
theorem bytesAt_writeBytes (m : Mem) (p : Addr) (r : Nat) (xs : List Byte) (h : r + xs.length < 2 ^ 64) :
    Spec.Aes.bytesAt (writeBytes m (p + BitVec.ofNat 64 r) xs) p (r + xs.length) =
      Spec.Aes.bytesAt m p r ++ xs := by
  rw [Proof.Cmac.Stream.bytesAt_append, bytesAt_writeBytes_self _ _ (by omega_using [h])]
  refine congrArg (· ++ xs) ?_
  simp only [Spec.Aes.bytesAt]
  apply List.map_congr_left
  intro i hi
  exact writeBytes_before m p xs (List.mem_range.mp hi) (by omega_using [h])

/-! ## Copying bytes -/

/-- Memory after writing the bytes copied, pointwise, as `writeBytes`. -/
theorem writeBytes_of {m m' : Mem} {C : Addr} {xs : List Byte}
    (hc : ∀ i < xs.length, m' (C + BitVec.ofNat 64 i) = xs.getD i 0) (hf : Frame [⟨C, xs.length⟩] m m') :
    m' = writeBytes m C xs := by
  funext a
  simp only [writeBytes]
  split
  · rename_i h
    have := hc _ h
    rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel] at this
  · rename_i h
    exact hf a fun r hr hc' => by
      simp only [List.mem_singleton] at hr; subst hr
      simp only [Region.Contains] at hc'; omega_using [h, hc']

/-- What `copy` leaves. -/
structure Copied (s : State) (C : Addr) (xs : List Byte) (s' : State) : Prop where
  mem : s'.mem = writeBytes s.mem C xs
  other : ∀ r, r ≠ .t2 → r ≠ .t3 → r ≠ .t5 → r ≠ .t6 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem copy_ok (s : State) {P C : Addr} {L : Nat} (hL : L < 2 ^ 64) (h6 : s.gpr .t6 = P)
    (h5 : s.gpr .t5 = C) (h2 : s.gpr .t2 = BitVec.ofNat 64 L)
    (hr : ∀ i < L, InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < L, InRegions s.wr (C + BitVec.ofNat 64 i) 1)
    (hdis : (⟨P, L⟩ : Region).Disjoint ⟨C, L⟩) :
    WP isa Impl.CmacAes.Stream.RISCV64.copy s (Copied s C (Spec.Aes.bytesAt s.mem P L)) := by
  have ev := Steps.eval_zero_ofNat s .t2 hL h2
  by_cases hL0 : L = 0
  · subst hL0
    refine WP.ite true (by rw [ev]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    exact ⟨by simp [Spec.Aes.bytesAt, writeBytes_nil], fun _ _ _ _ _ => rfl, rfl, rfl⟩
  refine WP.ite false (by rw [ev]; simp [hL0]) (fun h => by cases h) fun _ => ?_
  refine WP.mono (copyLoop_ok (tmp := .t3) (src := .t6) (dst := .t5) (cnt := .t2) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) s (N := L) (by omega_using [hL0]) hL h2 (by rw [h6]; exact hr)
    (by rw [h5]; exact hw) (fun x h₁ h₂ => ?_)) ?_
  · rw [h5] at h₁; rw [h6] at h₂
    exact hdis x (by simp only [Region.Contains]; omega_using [h₂]) (by simp only [Region.Contains]; omega_using [h₁])
  rintro t ⟨hc, hf, hk⟩
  rw [h5, h6] at hc
  rw [h5] at hf
  refine ⟨writeBytes_of (fun i hi => ?_)
    (by rw [Proof.Cmac.bytesAt_length]; exact hf), fun r a b c d => hk.gpr (by simp [a, b, c, d]), hk.2.1, hk.2.2⟩
  rw [Proof.Cmac.bytesAt_length] at hi
  rw [hc i hi, Proof.Cmac.getD_bytesAt _ _ hi]

end VG.Proof.CmacAes.Stream.RISCV64
