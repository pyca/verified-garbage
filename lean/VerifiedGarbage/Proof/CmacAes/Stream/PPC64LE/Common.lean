module

public import VerifiedGarbage.Impl.CmacAes.Stream.PPC64LE
public import VerifiedGarbage.Proof.CmacAes.PPC64LE.Contract
public import VerifiedGarbage.Proof.Aes.PPC64LE.ExpandKey
public import VerifiedGarbage.Proof.Cmac.Stream
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
import VerifiedGarbage.Proof.CmacAes.PPC64LE.Verified
import VerifiedGarbage.Proof.CmacAes.PPC64LE.CT
import VerifiedGarbage.Proof.CmacAes.PPC64LE.FinSteps
import VerifiedGarbage.Proof.AesCbc.PPC64LE.Body
import VerifiedGarbage.Proof.AesCbc.PPC64LE.Call
import VerifiedGarbage.Proof.Aes.PPC64LE.CodeLit
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# Streaming AES-CMAC on PPC64LE: the contracts, the calls and the copies

The artifacts' contracts are the shared ones of `Spec/Cmac/Contract.lean`,
with the working space appended (`Proof/CmacAes/Stream/Scratch.lean`), which
imply these (`Verified.lean`). A call (`bl`) stores nothing in memory, so no
stack is used.

A call of each function the streaming functions call
(`vg_aes_expand_key_scratch`, `vg_cmac_aes_subkeys`, `vg_cmac_aes_update` and
`vg_cmac_aes_finalize`), from its contract (with `WP.call`): what it needs
(`…Args`), what it leaves (`…Post`, in terms of the memory before the call),
and that two calls with the same arguments leak the same (`…_rel`). The
callees change only the buffers they are given, and keep every nonvolatile
register. Then the number of bytes held back, as the code computes it from
`count` (`held_bv`), and `copy`, which copies the `r12` bytes at `r11` to
`r10`, a byte at a time (none if `r12` is 0), changing only `r9` to `r12`.
-/

@[expose] public section

namespace VG.Proof.CmacAes.Stream.PPC64LE

open VG VG.PPC64LE
open VG.Proof.CmacAes.PPC64LE (subkeysPPC64LE updatePPC64LE finalizePPC64LE)
open VG.Proof.AesCbc.PPC64LE (callEntry_gpr' toNat_rounds)

/-! ## The contracts -/

/-- `vg_cmac_aes_init(state = r3, key = r4, key_len = r5, scratch = r6)`. -/
def initPPC64LE : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .r3, 304⟩
    let key : Region := ⟨s.gpr .r4, (s.gpr .r5).toNat⟩
    let scr : Region := ⟨s.gpr .r6, 2304⟩
    s.rd = [key] ∧ s.wr = [state, scr] ∧
      state.Disjoint key ∧ state.Disjoint scr ∧ key.Disjoint scr ∧
      (s.gpr .r3).toNat + 304 ≤ 2 ^ 64 ∧ (s.gpr .r4).toNat + (s.gpr .r5).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r6).toNat + 2304 ≤ 2 ^ 64 ∧
      ((s.gpr .r5).toNat = 16 ∨ (s.gpr .r5).toNat = 24 ∨ (s.gpr .r5).toNat = 32)
  post s s' :=
    Spec.Cmac.Repr s'.mem (s.gpr .r3) (Spec.Aes.bytesAt s.mem (s.gpr .r4) (s.gpr .r5).toNat) []
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.sp = s₂.sp

/-- `vg_cmac_aes_absorb(state = r3, rounds = r4, count = r5, data = r6, len = r7, scratch = r8)`. -/
def absorbPPC64LE : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .r3, 304⟩
    let data : Region := ⟨s.gpr .r6, (s.gpr .r7).toNat⟩
    let scr : Region := ⟨s.gpr .r8, 2304⟩
    s.rd = [data] ∧ s.wr = [state, scr] ∧
      state.Disjoint data ∧ state.Disjoint scr ∧ data.Disjoint scr ∧
      (s.gpr .r3).toNat + 304 ≤ 2 ^ 64 ∧ (s.gpr .r6).toNat + (s.gpr .r7).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + 2304 ≤ 2 ^ 64 ∧
      ((s.gpr .r4).toNat = 10 ∨ (s.gpr .r4).toNat = 12 ∨ (s.gpr .r4).toNat = 14)
  post s s' :=
    ∀ key msg, Spec.Cmac.Repr s.mem (s.gpr .r3) key msg →
      (s.gpr .r4).toNat = Spec.Aes.rounds (key.length / 4) →
      s.gpr .r5 = BitVec.ofNat 64 msg.length → msg.length + (s.gpr .r7).toNat < 2 ^ 64 →
      Spec.Cmac.Repr s'.mem (s.gpr .r3) key
        (msg ++ Spec.Aes.bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat)
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.sp = s₂.sp

/-- `vg_cmac_aes_finish(state = r3, rounds = r4, count = r5, out = r6, scratch = r7)`. -/
def finishPPC64LE : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .r3, 304⟩
    let out : Region := ⟨s.gpr .r6, 16⟩
    let scr : Region := ⟨s.gpr .r7, 2304⟩
    s.rd = [] ∧ s.wr = [state, out, scr] ∧
      state.Disjoint out ∧ state.Disjoint scr ∧ out.Disjoint scr ∧
      (s.gpr .r3).toNat + 304 ≤ 2 ^ 64 ∧ (s.gpr .r6).toNat + 16 ≤ 2 ^ 64 ∧
      (s.gpr .r7).toNat + 2304 ≤ 2 ^ 64 ∧
      ((s.gpr .r4).toNat = 10 ∨ (s.gpr .r4).toNat = 12 ∨ (s.gpr .r4).toNat = 14)
  post s s' :=
    ∀ key msg, Spec.Cmac.Repr s.mem (s.gpr .r3) key msg →
      (s.gpr .r4).toNat = Spec.Aes.rounds (key.length / 4) →
      s.gpr .r5 = BitVec.ofNat 64 msg.length → msg.length < 2 ^ 64 →
      Spec.Aes.bytesAt s'.mem (s.gpr .r6) 16 = Spec.Cmac.aesCmac key 16 msg
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.sp = s₂.sp

/-! ## Arithmetic -/

theorem toNat_ofNat {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem ofNat_toNat_eq {x : BitVec 64} {n : Nat} (h : x.toNat = n) : x = BitVec.ofNat 64 n :=
  BitVec.eq_of_toNat_eq (by rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (h ▸ x.isLt)])

theorem toNat_add_lt (p : Addr) {d k : Nat} (h : p.toNat + k ≤ 2 ^ 64) (hd : d < k) :
    (p + BitVec.ofNat 64 d).toNat = p.toNat + d := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : d < 2 ^ 64)]
  exact Nat.mod_eq_of_lt (by omega)

theorem and15 (x : BitVec 64) : (x &&& BitVec.ofNat 64 15).toNat = x.toNat % 16 := by
  rw [BitVec.toNat_and, show (BitVec.ofNat 64 15).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

open VG.Proof.Cmac.Stream (held held_pos) in
/-- The number of bytes held back for a nonzero `count`, as `subi 1; and 15; addi 1` computes it. -/
theorem held_bv (c : BitVec 64) (h : c ≠ 0) :
    ((c - BitVec.ofNat 64 1) &&& BitVec.ofNat 64 15) + BitVec.ofNat 64 1 = BitVec.ofNat 64 (held c.toNat) := by
  have hc : c.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
  rw [held_pos (by omega)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, and15, BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat]
  have := c.isLt
  omega

/-- The rounds, as `srdi 2; addi 6` computes them from the key length. -/
theorem rounds_bv {KL : Nat} (h : KL = 16 ∨ KL = 24 ∨ KL = 32) :
    BitVec.ofNat 64 KL >>> 2 + BitVec.ofNat 64 6 = BitVec.ofNat 64 (KL / 4 + 6) := by
  rcases h with rfl | rfl | rfl <;> decide

theorem shr_ofNat {n k : Nat} (hn : n < 2 ^ 64) : BitVec.ofNat 64 n >>> k = BitVec.ofNat 64 (n / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (by have := Nat.div_le_self n (2 ^ k); omega)]

theorem preserved_ne (r : Reg) (hr : r ∈ preserved) :
    r ≠ .r0 ∧ r ≠ .r3 ∧ r ≠ .r4 ∧ r ≠ .r5 ∧ r ≠ .r6 ∧ r ≠ .r7 ∧ r ≠ .r8 ∧ r ≠ .r9 ∧ r ≠ .r10 ∧
      r ≠ .r11 ∧ r ≠ .r12 := by
  revert hr; cases r <;> decide

theorem in_wr {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n := by
  obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩

/-! ## Saving registers -/

/-- What the code saves: the registers, with the return address in `r0`. -/
abbrev saveG (s₀ : State) : Reg → BitVec 64 := (s₀.write .r0 s₀.lr).gpr

theorem saveG_ne {s₀ : State} {r : Reg} (h : r ≠ .r0) : saveG s₀ r = s₀.gpr r := by
  unfold saveG; simp [State.write, h]

theorem saveG_r0 (s₀ : State) : saveG s₀ .r0 = s₀.lr := by
  unfold saveG; simp [State.write]

/-- Slots holding registers whose values agree hold either's. -/
theorem saved_congr {B : Addr} {g g' : Reg → BitVec 64} {l : List (Reg × Nat)} {m : Mem}
    (h : Spill.Saved B g l m) (hg : ∀ p ∈ l, g p.1 = g' p.1) : Spill.Saved B g' l m :=
  fun p hp => (h p hp).trans (hg p hp)

/-! ## No frames -/

theorem expandKey_noFrames : Impl.Aes.PPC64LE.expandKey.noFrames = true := by lit_decide

theorem subkeys_noFrames : Impl.CmacAes.PPC64LE.subkeys.noFrames = true := by
  simp [Impl.CmacAes.PPC64LE.subkeys, Impl.AesCbc.PPC64LE.encCall, Code.noFrames]
  exact Proof.AesCbc.PPC64LE.encryptBlocks_noFrames

theorem update_noFrames : Impl.CmacAes.PPC64LE.update.noFrames = true := by
  simp [Impl.CmacAes.PPC64LE.update, Impl.CmacAes.PPC64LE.body, Impl.AesCbc.PPC64LE.whole,
    Impl.AesCbc.PPC64LE.encCall, Code.noFrames]
  exact Proof.AesCbc.PPC64LE.encryptBlocks_noFrames

theorem finalize_noFrames : Impl.CmacAes.PPC64LE.finalize.noFrames = true := by
  simp [Impl.CmacAes.PPC64LE.finalize, Impl.CmacAes.PPC64LE.finPre, Impl.CmacAes.PPC64LE.partialBlock,
    Impl.CmacAes.PPC64LE.copy, Impl.AesCbc.PPC64LE.encCall, Code.noFrames]
  exact Proof.AesCbc.PPC64LE.encryptBlocks_noFrames

/-! ## `vg_cmac_aes_update` -/

/-- What a call of `vg_cmac_aes_update` needs: the key schedule `W`, the
chaining value `C`, `n` blocks at `D`, the working space `S` and the rounds
`R`. -/
structure UArgs (s : State) (W C D S : Addr) (R n : Nat) : Prop where
  r3 : s.gpr .r3 = W
  r4 : s.gpr .r4 = BitVec.ofNat 64 R
  r5 : s.gpr .r5 = C
  r6 : s.gpr .r6 = D
  r7 : s.gpr .r7 = BitVec.ofNat 64 n
  r8 : s.gpr .r8 = S
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
    updatePPC64LE.pre (s.callEntry.withRegions [⟨W, 240⟩, ⟨D, 16 * n⟩] [⟨C, 16⟩, ⟨S, 2176⟩]) := by
  have hR := toNat_rounds h.rounds
  have hN := toNat_ofNat (n := n) (by have := h.hn; omega)
  simp only [updatePPC64LE, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    callEntry_gpr' s (by decide : Reg.r3 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r4 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.r5 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r6 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.r7 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r8 ∉ linkRegs),
    h.r3, h.r4, h.r5, h.r6, h.r7, h.r8, hR, hN]
  exact ⟨trivial, trivial, h.wc, h.ws, h.dc, h.ds, h.cs, h.wrapC, h.wrapD, h.wrapS, h.rounds⟩

theorem upd_call {s : State} {W C D S : Addr} {R n : Nat} (h : UArgs s W C D S R n) :
    WP isa Impl.CmacAes.Stream.PPC64LE.updCall s (UPost s W C D S R n) := by
  have hR := toNat_rounds h.rounds
  have hN := toNat_ofNat (n := n) (by have := h.hn; omega)
  refine WP.call (k := updatePPC64LE) Proof.CmacAes.PPC64LE.update_correct h.pre h.reads h.writes ?_
    update_noFrames
  intro s' hrd hwr hsp hf hsaved _ hpost
  refine ⟨hrd, hwr, hsp, hsaved, hf, ?_⟩
  simp only [updatePPC64LE, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    callEntry_gpr' s (by decide : Reg.r3 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r4 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.r5 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r6 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.r7 ∉ linkRegs), h.r3, h.r4, h.r5, h.r6, h.r7, hR, hN] at hpost
  exact hpost

theorem upd_rel {W C D S : Addr} {R n : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → UArgs s₁ W C D S R n ∧ UArgs s₂ W C D S R n ∧ s₁.sp = s₂.sp) :
    RelCT isa P Impl.CmacAes.Stream.PPC64LE.updCall fun _ _ => True := by
  refine RelCT.call Proof.CmacAes.PPC64LE.update_correct Proof.CmacAes.PPC64LE.update_ct
    [⟨W, 240⟩, ⟨D, 16 * n⟩] [⟨C, 16⟩, ⟨S, 2176⟩] fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes⟩
  simp only [updatePPC64LE, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    callEntry_gpr' _ (by decide : Reg.r3 ∉ linkRegs), callEntry_gpr' _ (by decide : Reg.r4 ∉ linkRegs),
    callEntry_gpr' _ (by decide : Reg.r5 ∉ linkRegs), callEntry_gpr' _ (by decide : Reg.r6 ∉ linkRegs),
    callEntry_gpr' _ (by decide : Reg.r7 ∉ linkRegs), callEntry_gpr' _ (by decide : Reg.r8 ∉ linkRegs),
    h₁.r3, h₁.r4, h₁.r5, h₁.r6, h₁.r7, h₁.r8, h₂.r3, h₂.r4, h₂.r5, h₂.r6, h₂.r7, h₂.r8, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## `vg_cmac_aes_subkeys` -/

/-- What a call of `vg_cmac_aes_subkeys` needs: the key schedule `W`, the
subkeys `K`, the working space `S` and the rounds `R`. -/
structure SArgs (s : State) (W K S : Addr) (R : Nat) : Prop where
  r3 : s.gpr .r3 = W
  r4 : s.gpr .r4 = BitVec.ofNat 64 R
  r5 : s.gpr .r5 = K
  r6 : s.gpr .r6 = S
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
    subkeysPPC64LE.pre (s.callEntry.withRegions [⟨W, 240⟩] [⟨K, 32⟩, ⟨S, 2176⟩]) := by
  have hR := toNat_rounds h.rounds
  simp only [subkeysPPC64LE, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    callEntry_gpr' s (by decide : Reg.r3 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r4 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.r5 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r6 ∉ linkRegs),
    h.r3, h.r4, h.r5, h.r6, hR]
  exact ⟨trivial, trivial, h.wk, h.ws, h.ks, h.wrapK, h.wrapS, h.rounds⟩

theorem sub_call {s : State} {W K S : Addr} {R : Nat} (h : SArgs s W K S R) :
    WP isa Impl.CmacAes.Stream.PPC64LE.skCall s (SPost s W K S R) := by
  have hR := toNat_rounds h.rounds
  refine WP.call (k := subkeysPPC64LE) Proof.CmacAes.PPC64LE.subkeys_correct h.pre h.reads h.writes ?_
    subkeys_noFrames
  intro s' hrd hwr hsp hf hsaved _ hpost
  refine ⟨hrd, hwr, hsp, hsaved, hf, ?_⟩
  simp only [subkeysPPC64LE, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    callEntry_gpr' s (by decide : Reg.r3 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r4 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.r5 ∉ linkRegs), h.r3, h.r4, h.r5, hR] at hpost
  exact hpost

theorem sub_rel {W K S : Addr} {R : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → SArgs s₁ W K S R ∧ SArgs s₂ W K S R ∧ s₁.sp = s₂.sp) :
    RelCT isa P Impl.CmacAes.Stream.PPC64LE.skCall fun _ _ => True := by
  refine RelCT.call Proof.CmacAes.PPC64LE.subkeys_correct Proof.CmacAes.PPC64LE.subkeys_ct
    [⟨W, 240⟩] [⟨K, 32⟩, ⟨S, 2176⟩] fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes⟩
  simp only [subkeysPPC64LE, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    callEntry_gpr' _ (by decide : Reg.r3 ∉ linkRegs), callEntry_gpr' _ (by decide : Reg.r4 ∉ linkRegs),
    callEntry_gpr' _ (by decide : Reg.r5 ∉ linkRegs), callEntry_gpr' _ (by decide : Reg.r6 ∉ linkRegs),
    h₁.r3, h₁.r4, h₁.r5, h₁.r6, h₂.r3, h₂.r4, h₂.r5, h₂.r6, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

/-! ## `vg_cmac_aes_finalize` -/

/-- What a call of `vg_cmac_aes_finalize` needs: the key schedule and
subkeys `K`, the state `St`, the `L` last bytes at `P`, the working space
`S` and the rounds `R`. -/
structure FArgs (s : State) (K St P S : Addr) (L R : Nat) : Prop where
  r3 : s.gpr .r3 = K
  r4 : s.gpr .r4 = BitVec.ofNat 64 R
  r5 : s.gpr .r5 = St
  r6 : s.gpr .r6 = P
  r7 : s.gpr .r7 = BitVec.ofNat 64 L
  r8 : s.gpr .r8 = S
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
    finalizePPC64LE.pre (s.callEntry.withRegions [⟨K, 272⟩, ⟨P, L⟩] [⟨St, 16⟩, ⟨S, 2176⟩]) := by
  have hR := toNat_rounds h.rounds
  have hL := toNat_ofNat (n := L) (by have := h.len; omega)
  simp only [finalizePPC64LE, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    callEntry_gpr' s (by decide : Reg.r3 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r4 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.r5 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r6 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.r7 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r8 ∉ linkRegs),
    h.r3, h.r4, h.r5, h.r6, h.r7, h.r8, hR, hL]
  exact ⟨trivial, trivial, h.kst, h.ks, h.pst, h.ps, h.sts, h.wrapK, h.wrapSt, h.wrapP, h.wrapS,
    h.rounds, h.len⟩

theorem fin_call {s : State} {K St P S : Addr} {L R : Nat} (h : FArgs s K St P S L R) :
    WP isa Impl.CmacAes.Stream.PPC64LE.finCall s (FPost s K St P S L R) := by
  have hR := toNat_rounds h.rounds
  have hL := toNat_ofNat (n := L) (by have := h.len; omega)
  refine WP.call (k := finalizePPC64LE) Proof.CmacAes.PPC64LE.finalize_correct h.pre h.reads h.writes ?_
    finalize_noFrames
  intro s' hrd hwr hsp hf hsaved _ hpost
  refine ⟨hrd, hwr, hsp, hsaved, hf, ?_⟩
  simp only [finalizePPC64LE, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    callEntry_gpr' s (by decide : Reg.r3 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r4 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.r5 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r6 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.r7 ∉ linkRegs), h.r3, h.r4, h.r5, h.r6, h.r7, hR, hL] at hpost
  exact hpost

theorem fin_rel {K St Q S : Addr} {L R : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → FArgs s₁ K St Q S L R ∧ FArgs s₂ K St Q S L R ∧ s₁.sp = s₂.sp) :
    RelCT isa P Impl.CmacAes.Stream.PPC64LE.finCall fun _ _ => True := by
  refine RelCT.call Proof.CmacAes.PPC64LE.finalize_correct Proof.CmacAes.PPC64LE.finalize_ct
    [⟨K, 272⟩, ⟨Q, L⟩] [⟨St, 16⟩, ⟨S, 2176⟩] fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes⟩
  simp only [finalizePPC64LE, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    callEntry_gpr' _ (by decide : Reg.r3 ∉ linkRegs), callEntry_gpr' _ (by decide : Reg.r4 ∉ linkRegs),
    callEntry_gpr' _ (by decide : Reg.r5 ∉ linkRegs), callEntry_gpr' _ (by decide : Reg.r6 ∉ linkRegs),
    callEntry_gpr' _ (by decide : Reg.r7 ∉ linkRegs), callEntry_gpr' _ (by decide : Reg.r8 ∉ linkRegs),
    h₁.r3, h₁.r4, h₁.r5, h₁.r6, h₁.r7, h₁.r8, h₂.r3, h₂.r4, h₂.r5, h₂.r6, h₂.r7, h₂.r8, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## `vg_aes_expand_key_scratch` -/

/-- What a call of `vg_aes_expand_key_scratch` needs: the key `Kp` of `KL`
bytes, the schedule `W` and the working space `S`. -/
structure EArgs (s : State) (Kp W S : Addr) (KL : Nat) : Prop where
  r3 : s.gpr .r3 = Kp
  r4 : s.gpr .r4 = BitVec.ofNat 64 KL
  r5 : s.gpr .r5 = W
  r6 : s.gpr .r6 = S
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
    Proof.Aes.expandKeyPPC64LE.pre (s.callEntry.withRegions [⟨Kp, KL⟩] [⟨W, 240⟩, ⟨S, 512⟩]) := by
  have hK := toNat_ofNat (n := KL) (by rcases h.klen with h | h | h <;> omega)
  simp only [Proof.Aes.expandKeyPPC64LE, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    callEntry_gpr' s (by decide : Reg.r3 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r4 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.r5 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r6 ∉ linkRegs),
    h.r3, h.r4, h.r5, h.r6, hK]
  exact ⟨trivial, trivial, h.kw, h.ks, h.ws, h.klen⟩

theorem ek_call {s : State} {Kp W S : Addr} {KL : Nat} (h : EArgs s Kp W S KL) :
    WP isa Impl.CmacAes.Stream.PPC64LE.ekCall s (EPost s Kp W S KL) := by
  have hK := toNat_ofNat (n := KL) (by rcases h.klen with h | h | h <;> omega)
  refine WP.call (k := Proof.Aes.expandKeyPPC64LE) Proof.Aes.PPC64LE.expandKey_correct h.pre h.reads
    h.writes ?_ expandKey_noFrames
  intro s' hrd hwr hsp hf hsaved _ hpost
  refine ⟨hrd, hwr, hsp, hsaved, hf, ?_⟩
  simp only [Proof.Aes.expandKeyPPC64LE, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    callEntry_gpr' s (by decide : Reg.r3 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r4 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.r5 ∉ linkRegs), h.r3, h.r4, h.r5, hK] at hpost
  exact hpost

theorem ek_rel {Kp W S : Addr} {KL : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → EArgs s₁ Kp W S KL ∧ EArgs s₂ Kp W S KL ∧ s₁.sp = s₂.sp) :
    RelCT isa P Impl.CmacAes.Stream.PPC64LE.ekCall fun _ _ => True := by
  refine RelCT.call Proof.Aes.PPC64LE.expandKey_correct Proof.Aes.PPC64LE.expandKey_ct
    [⟨Kp, KL⟩] [⟨W, 240⟩, ⟨S, 512⟩] fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes⟩
  simp only [Proof.Aes.expandKeyPPC64LE, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    callEntry_gpr' _ (by decide : Reg.r3 ∉ linkRegs), callEntry_gpr' _ (by decide : Reg.r4 ∉ linkRegs),
    callEntry_gpr' _ (by decide : Reg.r5 ∉ linkRegs), callEntry_gpr' _ (by decide : Reg.r6 ∉ linkRegs),
    h₁.r3, h₁.r4, h₁.r5, h₁.r6, h₂.r3, h₂.r4, h₂.r5, h₂.r6, hsp]
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
  simp only [Spec.Aes.bytesAt, List.getElem_map, List.getElem_range, writeBytes_at m q xs (by omega : i < 2 ^ 64),
    h1, ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some]

/-- Bytes `[0, r)` from `p` stay, and the bytes `xs` follow them. -/
theorem bytesAt_writeBytes (m : Mem) (p : Addr) (r : Nat) (xs : List Byte) (h : r + xs.length < 2 ^ 64) :
    Spec.Aes.bytesAt (writeBytes m (p + BitVec.ofNat 64 r) xs) p (r + xs.length) =
      Spec.Aes.bytesAt m p r ++ xs := by
  rw [Proof.Cmac.Stream.bytesAt_append, bytesAt_writeBytes_self _ _ (by omega)]
  refine congrArg (· ++ xs) ?_
  simp only [Spec.Aes.bytesAt]
  apply List.map_congr_left
  intro i hi
  exact writeBytes_before m p xs (List.mem_range.mp hi) (by omega)

/-! ## Copying bytes -/

/-- What `copy` leaves. -/
structure Copied (s : State) (C : Addr) (xs : List Byte) (s' : State) : Prop where
  mem : s'.mem = writeBytes s.mem C xs
  other : ∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem copy_ok (s : State) {P C : Addr} {L : Nat} (hL : L < 2 ^ 64) (h11 : s.gpr .r11 = P)
    (h10 : s.gpr .r10 = C) (h12 : s.gpr .r12 = BitVec.ofNat 64 L)
    (hr : ∀ i < L, InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < L, InRegions s.wr (C + BitVec.ofNat 64 i) 1)
    (hdis : (⟨P, L⟩ : Region).Disjoint ⟨C, L⟩) :
    WP isa Impl.CmacAes.Stream.PPC64LE.copy s (Copied s C (Spec.Aes.bytesAt s.mem P L)) := by
  have ev := eval_zero_ofNat s .r12 hL h12
  by_cases hL0 : L = 0
  · subst hL0
    refine WP.ite true (by rw [ev]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    exact ⟨by simp [Spec.Aes.bytesAt, writeBytes_nil], fun _ _ _ _ _ => rfl, rfl, rfl⟩
  refine WP.ite false (by rw [ev]; simp [hL0]) (fun h => by cases h) fun _ => ?_
  refine WP.mono (Proof.CmacAes.PPC64LE.copy_wp s (by omega) hL h11 h10 h12 hr hw hdis) ?_
  rintro s' ⟨m, -, g, rd, wr⟩
  exact ⟨m, g, rd, wr⟩

end VG.Proof.CmacAes.Stream.PPC64LE
