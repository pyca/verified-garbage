import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Proof.Gcm.X86_64.Bits
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.Spill
import VerifiedGarbage.Impl.CmacAes.X86_64
import VerifiedGarbage.Proof.Aes.X86_64.Variant
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Cmac.Contract
import VerifiedGarbage.Proof.Framework.X86_64.Taint

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.X86_64.Dbl`. -/
section

/-!
# AES-CMAC on x86-64: doubling a block in two 64-bit words

`subkeys` loads a block as two byte-reversed words, the high and low halves of
the block as a big-endian integer (`Proof.Gcm.X86_64.blockAt_bswap`), doubles
the integer a word at a time (`dbl_words`), and stores the halves
byte-reversed again (`le8_bswap`).
-/

namespace VG.Proof.CmacAes.X86_64

open VG VG.X86_64 Proof.Cmac

theorem getD_le8_append (a b : BitVec 64) {k : Nat} (hk : k < 16) :
    (le8 a ++ le8 b).getD k 0 = if k < 8 then a.extractLsb' (8 * k) 8 else b.extractLsb' (8 * (k - 8)) 8 := by
  rw [List.getD_eq_getElem?_getD]
  split
  · rw [List.getElem?_append_left (by rw [length_le8]; omega), ← List.getD_eq_getElem?_getD, getD_le8 _ ‹_›]
  · rw [List.getElem?_append_right (by rw [length_le8]; omega), length_le8, ← List.getD_eq_getElem?_getD,
      getD_le8 _ (by omega)]

theorem getLsbD_bswap64 (x : BitVec 64) {p : Nat} (hp : p < 64) :
    (bswap64 x).getLsbD p = x.getLsbD (8 * (7 - p / 8) + p % 8) :=
  Proof.Gcm.getLsbD_byteRev64 x p hp

/-- Storing the byte-reversed halves of `h ++ l` stores its bytes, big-endian. -/
theorem le8_bswap (h l : BitVec 64) :
    le8 (bswap64 h) ++ le8 (bswap64 l) = Spec.Gcm.toBytes (h ++ l) := by
  refine ext16 (by simp [length_le8]) (toBytes_length _) fun k hk => ?_
  rw [Proof.Aes.toBytes_getD _ hk]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  simp only [hj, decide_true, Bool.true_and]
  rcases Nat.lt_or_ge k 8 with h8 | h8
  · rw [VG.Proof.CmacAes.X86_64.getD_le8_append _ _ hk]
    simp only [h8, ↓reduceIte]
    rw [BitVec.getLsbD_extractLsb', VG.Proof.CmacAes.X86_64.getLsbD_bswap64 _ (by omega)]
    simp only [hj, decide_true, Bool.true_and, show ¬ 8 * (15 - k) + j < 64 by omega, ite_false]
    congr 1; omega
  · rw [VG.Proof.CmacAes.X86_64.getD_le8_append _ _ hk]
    simp only [show ¬ k < 8 by omega, ↓reduceIte]
    rw [BitVec.getLsbD_extractLsb', VG.Proof.CmacAes.X86_64.getLsbD_bswap64 _ (by omega)]
    simp only [hj, decide_true, Bool.true_and, show 8 * (15 - k) + j < 64 by omega, ite_true]
    congr 1; omega

theorem add_self (x : BitVec 64) : x + x = x <<< 1 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

theorem mask_eq (hi : BitVec 64) :
    ((0 : BitVec 64) - (hi >>> 63)) &&& BitVec.signExtend 64 (0x87 : BitVec 32) = if hi.msb then 0x87 else 0 := by
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

/-- `subkeys`' doubling of `hi ++ lo`. -/
theorem dbl_words (hi lo : BitVec 64) :
    ((hi + hi) ||| (lo >>> 63)) ++
        ((lo + lo) ^^^ (((0 : BitVec 64) - (hi >>> 63)) &&& BitVec.signExtend 64 (0x87 : BitVec 32))) =
      dbl128 (hi ++ lo) := by
  rw [VG.Proof.CmacAes.X86_64.mask_eq, VG.Proof.CmacAes.X86_64.add_self, VG.Proof.CmacAes.X86_64.add_self, dbl128, BitVec.msb_append]
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
    · exact VG.Proof.CmacAes.X86_64.bit135 p h64
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

end VG.Proof.CmacAes.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.X86_64.UpdateLoop`. -/
section

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
theorem CallPre.ctr_pre {s : State} {W C D S : Addr} {R : Nat} (h : VG.Proof.CmacAes.X86_64.CallPre s W C D S R) :
    Proof.Aes.ctr32X86_64.pre
      (s.callEntry.withRegions [⟨W, 240⟩] [⟨C, 16⟩, ⟨D, 16⟩, ⟨S, 2048⟩]) := by
  have hR := VG.Proof.CmacAes.X86_64.toNat_rounds h.rounds
  simp only [Proof.Aes.ctr32X86_64, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.callEntry_rsp, State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.r9 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, hR,
    VG.Proof.CmacAes.X86_64.one_toNat, Nat.mul_one]
  exact ⟨trivial, trivial, h.wc, by simpa using h.wd, h.ws, by simpa using h.cd, h.cs,
    by simpa using h.ds, h.stkC, by simpa using h.stkD, h.stkS, by simpa using h.wrap, h.rounds⟩

theorem ctr_call (v : Ctr32Impl) {s : State} {W C D S : Addr} {R : Nat} (h : VG.Proof.CmacAes.X86_64.CallPre s W C D S R) :
    WP isa (.call v.callee.name v.callee.code) s (VG.Proof.CmacAes.X86_64.CallPost s W C D S R) := by
  have hR := VG.Proof.CmacAes.X86_64.toNat_rounds h.rounds
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
      VG.Proof.CmacAes.X86_64.one_toNat] at hdata
    have fE := VG.Proof.CmacAes.X86_64.callEntry_frame s
    have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with rfl | rfl | rfl <;> decide
    have eW := VG.Proof.CmacAes.X86_64.bytesAt_frame fE (p := W) (n := 16 * (R + 1))
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (h.stkW.sub_right (Region.sub_prefix hRb)).symm)
      (by omega)
    have eC := VG.Proof.CmacAes.X86_64.bytesAt_frame fE (p := C) (n := 16)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.stkC.symm) (by decide)
    have eD := VG.Proof.CmacAes.X86_64.bytesAt_frame fE (p := D) (n := 16)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.stkD.symm) (by decide)
    have one : ∀ m : Mem, Spec.Gcm.blocksAt m D 1 = [Spec.Gcm.blockAt m D] := fun m => by
      simp [Spec.Gcm.blocksAt]
    have bD : Spec.Gcm.blockAt s.callEntry.mem D = 0 := by
      rw [Spec.Gcm.blockAt, eD, h.zero, VG.Proof.CmacAes.X86_64.ofBytes_zeros]
    have bC : Spec.Gcm.blockAt s.callEntry.mem C = Spec.Gcm.ofBytes (Spec.Aes.bytesAt s.mem C 16) := by
      rw [Spec.Gcm.blockAt, eC]
    rw [one, one, bD, bC, eW, Proof.Cmac.ctr32_one, List.cons.injEq] at hdata
    rw [← hm₂, Proof.Cmac.bytesAt_blockAt, hdata.1,
      Proof.Cmac.aesWith_bytes _ _ (Proof.Cmac.bytesAt_length _ _ _)]

/-- Calls of `vg_aes_ctr32` on one block, with the same arguments in both
runs, are constant time. -/
theorem ctr_rel (v : Ctr32Impl) {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ W C D S : Addr, ∃ R : Nat,
      VG.Proof.CmacAes.X86_64.CallPre s₁ W C D S R ∧ VG.Proof.CmacAes.X86_64.CallPre s₂ W C D S R ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
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
      Spec.Cmac.chain (VG.Proof.CmacAes.X86_64.ciphAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (Spec.Aes.bytesAt s.mem (s.gpr .rdx) 16)
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
    let ks := Spec.Cmac.subkeys (VG.Proof.CmacAes.X86_64.ciphAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) 16
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
    let ciph := VG.Proof.CmacAes.X86_64.ciphAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat
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
abbrev savedMem (s : State) : Mem := Spill.saveMem s.mem (s.gpr .r9) s.gpr VG.Impl.CmacAes.X86_64.saved

theorem saved_bound : ∀ p ∈ VG.Impl.CmacAes.X86_64.saved, 2064 ≤ p.2 ∧ p.2 + 8 ≤ 2112 := by decide

theorem prologue_ok (s : State)
    (hw : ∀ d, 2064 ≤ d → d + 8 ≤ 2112 → InRegions s.wr (s.gpr .r9 + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa (VG.Impl.CmacAes.X86_64.save ++ VG.Impl.CmacAes.X86_64.setup) s = some s' ∧
      s'.gpr .rbx = s.gpr .rdi ∧ s'.gpr .rbp = s.gpr .rsi ∧ s'.gpr .r12 = s.gpr .rdx ∧
      s'.gpr .r13 = s.gpr .rcx ∧ s'.gpr .r14 = s.gpr .r8 ∧ s'.gpr .r15 = s.gpr .r9 ∧
      s'.gpr .rsp = s.gpr .rsp ∧ s'.zf = some (s.gpr .r8 == 0) ∧
      s'.mem = VG.Proof.CmacAes.X86_64.savedMem s ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [VG.Impl.CmacAes.X86_64.save, VG.Impl.CmacAes.X86_64.setup, VG.Impl.CmacAes.X86_64.saved, List.map, List.cons_append, List.nil_append, runBlock_cons,
      runStep_some, runBlock_nil, VG.Impl.CmacAes.X86_64.at_, exec, readSrc, State.store64, State.ea, VG.Proof.CmacAes.X86_64.offset_nat,
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
      s'.mem = VG.Proof.CmacAes.X86_64.chainMem s.mem C P Q ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hc' : s.gpr .r15 + BitVec.ofNat 64 2056 = C + BitVec.ofNat 64 8 := by
    rw [← hc, BitVec.add_assoc]; rfl
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceAdd, Nat.reducePow, BitVec.reduceSignExtend, chainIn, updArgs, ctrArgs, cOff, List.cons_append,
      List.nil_append, runBlock_cons, runStep_some, runBlock_nil, VG.Impl.CmacAes.X86_64.at_, exec, readSrc, readSrc32,
      State.load64, State.store64, State.ea, VG.Proof.CmacAes.X86_64.offset_nat, execAlu, Option.bind_some, Option.map_some,
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

theorem chainMem_frame (m : Mem) (C P Q : Addr) : Frame [⟨C, 16⟩, ⟨P, 16⟩] m (VG.Proof.CmacAes.X86_64.chainMem m C P Q) := by
  have f₁ : Frame [⟨C, 16⟩, ⟨P, 16⟩] m _ :=
    (VG.Proof.CmacAes.X86_64.frame_store2 (m := m) C (m.readW P 64 ^^^ m.readW Q 64)
      ((m.writeW C (m.readW P 64 ^^^ m.readW Q 64)).readW (P + BitVec.ofNat 64 8) 64 ^^^
        (m.writeW C (m.readW P 64 ^^^ m.readW Q 64)).readW (Q + BitVec.ofNat 64 8) 64)).mono
      (fun r hr => by simp only [List.mem_singleton] at hr; simp [hr])
  exact f₁.trans ((VG.Proof.CmacAes.X86_64.frame_store2 P 0 0).mono (fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]))

theorem chainMem_state (m : Mem) (C P Q : Addr) :
    Spec.Aes.bytesAt (VG.Proof.CmacAes.X86_64.chainMem m C P Q) P 16 = Spec.Cmac.zeros 16 := by
  rw [VG.Proof.CmacAes.X86_64.chainMem, Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_zero]; rfl

theorem bytesAt_frame' {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 16⟩ : Region).Disjoint r) : Spec.Aes.bytesAt m' p 16 = Spec.Aes.bytesAt m p 16 :=
  VG.Proof.CmacAes.X86_64.bytesAt_frame hf hd (by decide)

theorem readW_frame16 {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {d : Nat} (hd8 : d + 8 ≤ 16)
    (hd : ∀ r ∈ rs, (⟨p, 16⟩ : Region).Disjoint r) :
    m'.readW (p + BitVec.ofNat 64 d) 64 = m.readW (p + BitVec.ofNat 64 d) 64 :=
  hf.readW (r := ⟨p + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
    (fun r hr => (hd r hr).sub_left (Offset.sub_base p hd8)) (by decide)

theorem chainMem_counter (m : Mem) {C P Q : Addr} (hcp : (⟨C, 16⟩ : Region).Disjoint ⟨P, 16⟩)
    (hcq : (⟨C, 16⟩ : Region).Disjoint ⟨Q, 16⟩) :
    Spec.Aes.bytesAt (VG.Proof.CmacAes.X86_64.chainMem m C P Q) C 16 =
      Spec.Cmac.xor (Spec.Aes.bytesAt m P 16) (Spec.Aes.bytesAt m Q 16) := by
  rw [VG.Proof.CmacAes.X86_64.chainMem, VG.Proof.CmacAes.X86_64.bytesAt_frame' (VG.Proof.CmacAes.X86_64.frame_store2 P 0 0) (by simpa using hcp), Proof.Cmac.bytesAt_store2]
  have g : Frame [⟨C, 16⟩] m (m.writeW C (m.readW P 64 ^^^ m.readW Q 64)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (by simpa using Offset.contains_base C (d := 0) (n := 8) (k := 16) (by decide) (by decide))
  rw [VG.Proof.CmacAes.X86_64.readW_frame16 g (d := 8) (by decide) (by simpa using hcp.symm),
    VG.Proof.CmacAes.X86_64.readW_frame16 g (d := 8) (by decide) (by simpa using hcq.symm)]
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

abbrev schR : Region := ⟨VG.Proof.CmacAes.X86_64.W s₀, 240⟩
abbrev stR : Region := ⟨VG.Proof.CmacAes.X86_64.St s₀, 16⟩
abbrev dataR : Region := ⟨VG.Proof.CmacAes.X86_64.Dp s₀, 16 * VG.Proof.CmacAes.X86_64.N s₀⟩
abbrev scrR : Region := ⟨VG.Proof.CmacAes.X86_64.S s₀, 2176⟩
abbrev stkR : Region := below (s₀.gpr .rsp) 8

/-- The cipher. -/
abbrev ciph : Spec.Cmac.Cipher := VG.Proof.CmacAes.X86_64.ciphAt s₀.mem (VG.Proof.CmacAes.X86_64.W s₀) (VG.Proof.CmacAes.X86_64.R s₀)

/-- The message blocks. -/
abbrev blks : List (List Byte) := Spec.Cmac.blocksAt s₀.mem (VG.Proof.CmacAes.X86_64.Dp s₀) 16 (VG.Proof.CmacAes.X86_64.N s₀)

end

/-- The precondition, by name. -/
structure UPre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.CmacAes.X86_64.schR s₀, VG.Proof.CmacAes.X86_64.dataR s₀]
  wr : s₀.wr = [VG.Proof.CmacAes.X86_64.stR s₀, VG.Proof.CmacAes.X86_64.scrR s₀]
  sch_st : (VG.Proof.CmacAes.X86_64.schR s₀).Disjoint (VG.Proof.CmacAes.X86_64.stR s₀)
  sch_scr : (VG.Proof.CmacAes.X86_64.schR s₀).Disjoint (VG.Proof.CmacAes.X86_64.scrR s₀)
  data_st : (VG.Proof.CmacAes.X86_64.dataR s₀).Disjoint (VG.Proof.CmacAes.X86_64.stR s₀)
  data_scr : (VG.Proof.CmacAes.X86_64.dataR s₀).Disjoint (VG.Proof.CmacAes.X86_64.scrR s₀)
  st_scr : (VG.Proof.CmacAes.X86_64.stR s₀).Disjoint (VG.Proof.CmacAes.X86_64.scrR s₀)
  ret_st : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint (VG.Proof.CmacAes.X86_64.stR s₀)
  ret_scr : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint (VG.Proof.CmacAes.X86_64.scrR s₀)
  stk_sch : (VG.Proof.CmacAes.X86_64.stkR s₀).Disjoint (VG.Proof.CmacAes.X86_64.schR s₀)
  stk_data : (VG.Proof.CmacAes.X86_64.stkR s₀).Disjoint (VG.Proof.CmacAes.X86_64.dataR s₀)
  stk_st : (VG.Proof.CmacAes.X86_64.stkR s₀).Disjoint (VG.Proof.CmacAes.X86_64.stR s₀)
  stk_scr : (VG.Proof.CmacAes.X86_64.stkR s₀).Disjoint (VG.Proof.CmacAes.X86_64.scrR s₀)
  st_wrap : (VG.Proof.CmacAes.X86_64.St s₀).toNat + 16 ≤ 2 ^ 64
  data_wrap : (VG.Proof.CmacAes.X86_64.Dp s₀).toNat + 16 * VG.Proof.CmacAes.X86_64.N s₀ ≤ 2 ^ 64
  scr_wrap : (VG.Proof.CmacAes.X86_64.S s₀).toNat + 2176 ≤ 2 ^ 64
  rounds : VG.Proof.CmacAes.X86_64.R s₀ = 10 ∨ VG.Proof.CmacAes.X86_64.R s₀ = 12 ∨ VG.Proof.CmacAes.X86_64.R s₀ = 14

theorem UPre.of {s₀ : State} (h : updateX86_64.pre s₀) : VG.Proof.CmacAes.X86_64.UPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q⟩

/-- The loop invariant, after `k` blocks. -/
structure LInv (s₀ : State) (k : Nat) (s : State) : Prop where
  rbx : s.gpr .rbx = VG.Proof.CmacAes.X86_64.W s₀
  rbp : s.gpr .rbp = s₀.gpr .rsi
  r12 : s.gpr .r12 = VG.Proof.CmacAes.X86_64.St s₀
  r13 : s.gpr .r13 = VG.Proof.CmacAes.X86_64.Dp s₀ + BitVec.ofNat 64 (16 * k)
  r14 : s.gpr .r14 = BitVec.ofNat 64 (VG.Proof.CmacAes.X86_64.N s₀ - k)
  r15 : s.gpr .r15 = VG.Proof.CmacAes.X86_64.S s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [VG.Proof.CmacAes.X86_64.stR s₀, ⟨VG.Proof.CmacAes.X86_64.S s₀, 2064⟩, VG.Proof.CmacAes.X86_64.stkR s₀] (VG.Proof.CmacAes.X86_64.savedMem s₀) s.mem
  state : Spec.Aes.bytesAt s.mem (VG.Proof.CmacAes.X86_64.St s₀) 16 =
    Spec.Cmac.chain (VG.Proof.CmacAes.X86_64.ciph s₀) (Spec.Aes.bytesAt s₀.mem (VG.Proof.CmacAes.X86_64.St s₀) 16) ((VG.Proof.CmacAes.X86_64.blks s₀).take k)

/-! ## Regions -/

section
variable {s₀ : State}

theorem UPre.scr_sub {d n : Nat} (h : d + n ≤ 2176) : Region.Sub ⟨VG.Proof.CmacAes.X86_64.S s₀ + BitVec.ofNat 64 d, n⟩ (VG.Proof.CmacAes.X86_64.scrR s₀) :=
  Offset.sub_base _ h

theorem UPre.data_sub {k : Nat} (hk : k < VG.Proof.CmacAes.X86_64.N s₀) :
    Region.Sub ⟨VG.Proof.CmacAes.X86_64.Dp s₀ + BitVec.ofNat 64 (16 * k), 16⟩ (VG.Proof.CmacAes.X86_64.dataR s₀) :=
  Offset.sub_base _ (by omega)

theorem UPre.sch_sub {R' : Nat} (h : R' ≤ 240) : Region.Sub ⟨VG.Proof.CmacAes.X86_64.W s₀, R'⟩ (VG.Proof.CmacAes.X86_64.schR s₀) :=
  Region.sub_prefix h

end

theorem slot_contains (b : Addr) {d : Nat} (h₁ : 2064 ≤ d) (h₂ : d + 8 ≤ 2112) :
    (⟨b + BitVec.ofNat 64 2064, 48⟩ : Region).Contains (b + BitVec.ofNat 64 d) 8 := by
  rw [show b + BitVec.ofNat 64 d = (b + BitVec.ofNat 64 2064) + BitVec.ofNat 64 (d - 2064) from
    (Offset.add_add_eq b (by omega)).symm]
  exact Offset.contains_base _ (by omega) (by omega)

/-- Saving the registers changes only their slots. -/
theorem savedMem_frame (s : State) : Frame [⟨s.gpr .r9 + BitVec.ofNat 64 2064, 48⟩] s.mem (VG.Proof.CmacAes.X86_64.savedMem s) :=
  Spill.saveMem_frame _ _ _ _ fun p hp => VG.Proof.CmacAes.X86_64.slot_contains _ (VG.Proof.CmacAes.X86_64.saved_bound p hp).1 (VG.Proof.CmacAes.X86_64.saved_bound p hp).2

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

theorem rsi_ofNat (s₀ : State) : s₀.gpr .rsi = BitVec.ofNat 64 (VG.Proof.CmacAes.X86_64.R s₀) := by
  apply BitVec.eq_of_toNat_eq; simp [VG.Proof.CmacAes.X86_64.R]

theorem take_succ_blks (s₀ : State) {k : Nat} (hk : k < VG.Proof.CmacAes.X86_64.N s₀) :
    (VG.Proof.CmacAes.X86_64.blks s₀).take (k + 1) =
      (VG.Proof.CmacAes.X86_64.blks s₀).take k ++ [Spec.Aes.bytesAt s₀.mem (VG.Proof.CmacAes.X86_64.Dp s₀ + BitVec.ofNat 64 (16 * k)) 16] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simp [Spec.Cmac.blocksAt]; omega)]
  simp [Spec.Cmac.blocksAt]

theorem in_rw {rs : List Region} {r : Region} (hr : r ∈ rs) {a : Addr} {n : Nat} (hc : r.Contains a n) :
    InRegions rs a n := ⟨r, hr, hc⟩

/-! ## Memory outside the writable regions -/

/-- The regions the function writes. -/
abbrev Big (s₀ : State) : List Region := [VG.Proof.CmacAes.X86_64.stR s₀, VG.Proof.CmacAes.X86_64.scrR s₀, VG.Proof.CmacAes.X86_64.stkR s₀]

section
variable {s₀ : State} (hp : VG.Proof.CmacAes.X86_64.UPre s₀)
include hp

theorem UPre.sched_bytes {m : Mem} (hf : Frame (VG.Proof.CmacAes.X86_64.Big s₀) s₀.mem m) :
    Spec.Aes.bytesAt m (VG.Proof.CmacAes.X86_64.W s₀) (16 * (VG.Proof.CmacAes.X86_64.R s₀ + 1)) = Spec.Aes.bytesAt s₀.mem (VG.Proof.CmacAes.X86_64.W s₀) (16 * (VG.Proof.CmacAes.X86_64.R s₀ + 1)) := by
  have hR : 16 * (VG.Proof.CmacAes.X86_64.R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega
  refine VG.Proof.CmacAes.X86_64.bytesAt_frame hf (fun r hr => ?_) (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.sch_st.sub_left (Region.sub_prefix hR)
  · exact hp.sch_scr.sub_left (Region.sub_prefix hR)
  · exact hp.stk_sch.symm.sub_left (Region.sub_prefix hR)

theorem UPre.block_bytes {m : Mem} (hf : Frame (VG.Proof.CmacAes.X86_64.Big s₀) s₀.mem m) {k : Nat} (hk : k < VG.Proof.CmacAes.X86_64.N s₀) :
    Spec.Aes.bytesAt m (VG.Proof.CmacAes.X86_64.Dp s₀ + BitVec.ofNat 64 (16 * k)) 16 =
      Spec.Aes.bytesAt s₀.mem (VG.Proof.CmacAes.X86_64.Dp s₀ + BitVec.ofNat 64 (16 * k)) 16 := by
  refine VG.Proof.CmacAes.X86_64.bytesAt_frame hf (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.data_st.sub_left (UPre.data_sub hk)
  · exact hp.data_scr.sub_left (UPre.data_sub hk)
  · exact hp.stk_data.symm.sub_left (UPre.data_sub hk)

omit hp in
theorem UPre.big_of {m : Mem} (hf : Frame [VG.Proof.CmacAes.X86_64.stR s₀, ⟨VG.Proof.CmacAes.X86_64.S s₀, 2064⟩, VG.Proof.CmacAes.X86_64.stkR s₀] (VG.Proof.CmacAes.X86_64.savedMem s₀) m) :
    Frame (VG.Proof.CmacAes.X86_64.Big s₀) s₀.mem m := by
  have f₀ : Frame (VG.Proof.CmacAes.X86_64.Big s₀) s₀.mem (VG.Proof.CmacAes.X86_64.savedMem s₀) :=
    (VG.Proof.CmacAes.X86_64.savedMem_frame s₀).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.CmacAes.X86_64.scrR s₀, by simp, UPre.scr_sub (by decide)⟩
  exact f₀.trans (hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨VG.Proof.CmacAes.X86_64.stR s₀, by simp, fun _ h => h⟩
    · exact ⟨VG.Proof.CmacAes.X86_64.scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨VG.Proof.CmacAes.X86_64.stkR s₀, by simp, fun _ h => h⟩)

end

/-! ## One block -/

/-- What the code before the call leaves. -/
structure BodyA (s₀ : State) (k : Nat) (s s₁ : State) : Prop where
  pre : VG.Proof.CmacAes.X86_64.CallPre s₁ (VG.Proof.CmacAes.X86_64.W s₀) (VG.Proof.CmacAes.X86_64.S s₀ + BitVec.ofNat 64 2048) (VG.Proof.CmacAes.X86_64.St s₀) (VG.Proof.CmacAes.X86_64.S s₀) (VG.Proof.CmacAes.X86_64.R s₀)
  saved : ∀ r ∈ calleeSaved, s₁.gpr r = s.gpr r
  mem : s₁.mem = VG.Proof.CmacAes.X86_64.chainMem s.mem (VG.Proof.CmacAes.X86_64.S s₀ + BitVec.ofNat 64 2048) (VG.Proof.CmacAes.X86_64.St s₀) (VG.Proof.CmacAes.X86_64.Dp s₀ + BitVec.ofNat 64 (16 * k))
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

theorem bodyA_wp {s₀ : State} (hp : VG.Proof.CmacAes.X86_64.UPre s₀) {k : Nat} (hk : k < VG.Proof.CmacAes.X86_64.N s₀) {s : State} (h : VG.Proof.CmacAes.X86_64.LInv s₀ k s) :
    WP isa (.block (chainIn ++ updArgs)) s (VG.Proof.CmacAes.X86_64.BodyA s₀ k s) := by
  have hRegs : s.rd ++ s.wr = [VG.Proof.CmacAes.X86_64.schR s₀, VG.Proof.CmacAes.X86_64.dataR s₀, VG.Proof.CmacAes.X86_64.stR s₀, VG.Proof.CmacAes.X86_64.scrR s₀] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have hW : s.wr = [VG.Proof.CmacAes.X86_64.stR s₀, VG.Proof.CmacAes.X86_64.scrR s₀] := by rw [h.wr, hp.wr]
  have h16k : 16 * k + 16 ≤ 16 * VG.Proof.CmacAes.X86_64.N s₀ := by omega
  have hdw := hp.data_wrap
  have cSt0 : (VG.Proof.CmacAes.X86_64.stR s₀).Contains (VG.Proof.CmacAes.X86_64.St s₀) 8 := by
    simpa using Offset.contains_base (VG.Proof.CmacAes.X86_64.St s₀) (d := 0) (n := 8) (k := 16) (by decide) (by decide)
  have cSt8 : (VG.Proof.CmacAes.X86_64.stR s₀).Contains (VG.Proof.CmacAes.X86_64.St s₀ + BitVec.ofNat 64 8) 8 := Offset.contains_base _ (by decide) (by decide)
  have cQ0 : (VG.Proof.CmacAes.X86_64.dataR s₀).Contains (VG.Proof.CmacAes.X86_64.Dp s₀ + BitVec.ofNat 64 (16 * k)) 8 :=
    Offset.contains_base _ (by omega) (by omega)
  have cQ8 : (VG.Proof.CmacAes.X86_64.dataR s₀).Contains (VG.Proof.CmacAes.X86_64.Dp s₀ + BitVec.ofNat 64 (16 * k) + BitVec.ofNat 64 8) 8 := by
    rw [Offset.add_add]; exact Offset.contains_base _ (by omega) (by omega)
  have cC0 : (VG.Proof.CmacAes.X86_64.scrR s₀).Contains (VG.Proof.CmacAes.X86_64.S s₀ + BitVec.ofNat 64 2048) 8 := Offset.contains_base _ (by decide) (by decide)
  have cC8 : (VG.Proof.CmacAes.X86_64.scrR s₀).Contains (VG.Proof.CmacAes.X86_64.S s₀ + BitVec.ofNat 64 2048 + BitVec.ofNat 64 8) 8 := by
    rw [Offset.add_add]; exact Offset.contains_base _ (by decide) (by decide)
  obtain ⟨s₁, run₁, rdi₁, rsi₁, rdx₁, rcx₁, r8₁, r9₁, cs₁, mem₁, rd₁, wr₁⟩ :=
    VG.Proof.CmacAes.X86_64.chainIn_ok s (C := VG.Proof.CmacAes.X86_64.S s₀ + BitVec.ofNat 64 2048) (P := VG.Proof.CmacAes.X86_64.St s₀) (Q := VG.Proof.CmacAes.X86_64.Dp s₀ + BitVec.ofNat 64 (16 * k))
      (by rw [h.r15]) h.r12 h.r13
      (by rw [hRegs]; exact VG.Proof.CmacAes.X86_64.in_rw (by simp) cSt0) (by rw [hRegs]; exact VG.Proof.CmacAes.X86_64.in_rw (by simp) cSt8)
      (by rw [hRegs]; exact VG.Proof.CmacAes.X86_64.in_rw (by simp) cQ0) (by rw [hRegs]; exact VG.Proof.CmacAes.X86_64.in_rw (by simp) cQ8)
      (by rw [hW]; exact VG.Proof.CmacAes.X86_64.in_rw (by simp) cC0) (by rw [hW]; exact VG.Proof.CmacAes.X86_64.in_rw (by simp) cC8)
      (by rw [hW]; exact VG.Proof.CmacAes.X86_64.in_rw (by simp) cSt0) (by rw [hW]; exact VG.Proof.CmacAes.X86_64.in_rw (by simp) cSt8)
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := by rw [cs₁ .rsp (by simp [calleeSaved]), h.rsp]
  have hR : 16 * (VG.Proof.CmacAes.X86_64.R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega
  have cDis : (⟨VG.Proof.CmacAes.X86_64.S s₀ + BitVec.ofNat 64 2048, 16⟩ : Region).Disjoint ⟨VG.Proof.CmacAes.X86_64.S s₀, 2048⟩ :=
    Offset.disjoint_base _ (by decide) (by have := hp.scr_wrap; omega)
  have pre : VG.Proof.CmacAes.X86_64.CallPre s₁ (VG.Proof.CmacAes.X86_64.W s₀) (VG.Proof.CmacAes.X86_64.S s₀ + BitVec.ofNat 64 2048) (VG.Proof.CmacAes.X86_64.St s₀) (VG.Proof.CmacAes.X86_64.S s₀) (VG.Proof.CmacAes.X86_64.R s₀) :=
    { rdi := by rw [rdi₁, h.rbx]
      rsi := by rw [rsi₁, h.rbp, VG.Proof.CmacAes.X86_64.rsi_ofNat]
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
        · exact ⟨VG.Proof.CmacAes.X86_64.schR s₀, by simp, 0, by simp, by simp⟩
        · exact ⟨VG.Proof.CmacAes.X86_64.scrR s₀, by simp, 2048, rfl, by simp⟩
        · exact ⟨VG.Proof.CmacAes.X86_64.stR s₀, by simp, 0, by simp, by simp⟩
        · exact ⟨VG.Proof.CmacAes.X86_64.scrR s₀, by simp, 0, by simp, by simp⟩
      writes := by
        rw [wr₁, hW]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨VG.Proof.CmacAes.X86_64.scrR s₀, by simp, 2048, rfl, by simp⟩
        · exact ⟨VG.Proof.CmacAes.X86_64.stR s₀, by simp, 0, by simp, by simp⟩
        · exact ⟨VG.Proof.CmacAes.X86_64.scrR s₀, by simp, 0, by simp, by simp⟩
      zero := by rw [mem₁]; exact VG.Proof.CmacAes.X86_64.chainMem_state _ _ _ _ }
  exact ⟨pre, cs₁, mem₁, rd₁, wr₁⟩

theorem body_ok (v : Ctr32Impl) {s₀ : State} (hp : VG.Proof.CmacAes.X86_64.UPre s₀) {k : Nat} (hk : k < VG.Proof.CmacAes.X86_64.N s₀) {s : State}
    (h : VG.Proof.CmacAes.X86_64.LInv s₀ k s) :
    WP isa (VG.Impl.CmacAes.X86_64.body v.callee) s fun s' => VG.Proof.CmacAes.X86_64.LInv s₀ (k + 1) s' ∧ s'.zf = some (decide (VG.Proof.CmacAes.X86_64.N s₀ - (k + 1) = 0)) := by
  have h16k : 16 * k + 16 ≤ 16 * VG.Proof.CmacAes.X86_64.N s₀ := by omega
  have hdw := hp.data_wrap
  refine WP.seq (WP.mono (VG.Proof.CmacAes.X86_64.bodyA_wp hp hk h) fun s₁ ⟨pre, cs₁, mem₁, rd₁, wr₁⟩ => ?_)
  have rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := by rw [cs₁ .rsp (by simp [calleeSaved]), h.rsp]
  refine WP.seq (WP.mono (VG.Proof.CmacAes.X86_64.ctr_call v pre) fun s₂ h₂ => ?_)
  obtain ⟨s₃, run₃, r13₃, r14₃, zf₃, keep₃, mem₃, rd₃, wr₃⟩ := VG.Proof.CmacAes.X86_64.advance_ok s₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have g (r : Reg) (hr : r ∈ calleeSaved) (h13 : r ≠ .r13) (h14 : r ≠ .r14) : s₃.gpr r = s.gpr r := by
    rw [keep₃ r h13 h14, h₂.saved r hr, cs₁ r hr]
  have r13₂ : s₂.gpr .r13 = VG.Proof.CmacAes.X86_64.Dp s₀ + BitVec.ofNat 64 (16 * k) := by
    rw [h₂.saved .r13 (by simp [calleeSaved]), cs₁ .r13 (by simp [calleeSaved]), h.r13]
  have r14₂ : s₂.gpr .r14 = BitVec.ofNat 64 (VG.Proof.CmacAes.X86_64.N s₀ - k) := by
    rw [h₂.saved .r14 (by simp [calleeSaved]), cs₁ .r14 (by simp [calleeSaved]), h.r14]
  have hN := (s₀.gpr .r8).isLt
  have dec : BitVec.ofNat 64 (VG.Proof.CmacAes.X86_64.N s₀ - k) - 1 = BitVec.ofNat 64 (VG.Proof.CmacAes.X86_64.N s₀ - (k + 1)) := by
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega)]; rfl
  -- Memory.
  have bigS := UPre.big_of h.frame
  have f₁ : Frame [⟨VG.Proof.CmacAes.X86_64.S s₀ + BitVec.ofNat 64 2048, 16⟩, ⟨VG.Proof.CmacAes.X86_64.St s₀, 16⟩] s.mem s₁.mem := by
    rw [mem₁]; exact VG.Proof.CmacAes.X86_64.chainMem_frame _ _ _ _
  have big₁ : Frame (VG.Proof.CmacAes.X86_64.Big s₀) s₀.mem s₁.mem := bigS.trans (f₁.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨VG.Proof.CmacAes.X86_64.scrR s₀, by simp, UPre.scr_sub (by decide)⟩
    · exact ⟨VG.Proof.CmacAes.X86_64.stR s₀, by simp, fun _ h => h⟩)
  have cst : (⟨VG.Proof.CmacAes.X86_64.S s₀ + BitVec.ofNat 64 2048, 16⟩ : Region).Disjoint (VG.Proof.CmacAes.X86_64.stR s₀) :=
    hp.st_scr.symm.sub_left (UPre.scr_sub (by decide))
  have cq : (⟨VG.Proof.CmacAes.X86_64.S s₀ + BitVec.ofNat 64 2048, 16⟩ : Region).Disjoint ⟨VG.Proof.CmacAes.X86_64.Dp s₀ + BitVec.ofNat 64 (16 * k), 16⟩ :=
    (hp.data_scr.symm.sub_left (UPre.scr_sub (by decide))).sub_right (UPre.data_sub hk)
  have out := h₂.out
  rw [UPre.sched_bytes hp big₁, mem₁, VG.Proof.CmacAes.X86_64.chainMem_counter _ cst cq, h.state,
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
      · exact ⟨⟨VG.Proof.CmacAes.X86_64.S s₀, 2064⟩, by simp, Offset.sub_base _ (by decide)⟩
      · exact ⟨VG.Proof.CmacAes.X86_64.stR s₀, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨VG.Proof.CmacAes.X86_64.S s₀, 2064⟩, by simp, Offset.sub_base _ (by decide)⟩
      · exact ⟨VG.Proof.CmacAes.X86_64.stR s₀, by simp, fun _ h => h⟩
      · exact ⟨⟨VG.Proof.CmacAes.X86_64.S s₀, 2064⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨VG.Proof.CmacAes.X86_64.stkR s₀, by simp, by rw [rsp₁]; exact fun _ h => h⟩
  · rw [mem₃, out, VG.Proof.CmacAes.X86_64.take_succ_blks s₀ hk, Proof.Cmac.chain_append, Proof.Cmac.chain_single]
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

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.X86_64.UpdateCorrect`. -/
section

/-!
# AES-CMAC on x86-64: `vg_cmac_aes_update` is correct
-/

namespace VG.Proof.CmacAes.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.CmacAes.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)

theorem beq_zero {x : Nat} (hx : x < 2 ^ 64) : (BitVec.ofNat 64 x == 0) = decide (x = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro he
    have := congrArg BitVec.toNat he
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx] at this
    simpa using this
  · intro he; rw [he]; rfl

theorem loop_ok (v : Ctr32Impl) {s₀ : State} (hp : VG.Proof.CmacAes.X86_64.UPre s₀) {k : Nat} (hk : k < VG.Proof.CmacAes.X86_64.N s₀) {s : State}
    (h : VG.Proof.CmacAes.X86_64.LInv s₀ k s) : WP isa (.loop (VG.Impl.CmacAes.X86_64.body v.callee) .ne) s (VG.Proof.CmacAes.X86_64.LInv s₀ (VG.Proof.CmacAes.X86_64.N s₀)) := by
  refine WP.loop (M := isa) (body := VG.Impl.CmacAes.X86_64.body v.callee) (c := .ne) (Q := VG.Proof.CmacAes.X86_64.LInv s₀ (VG.Proof.CmacAes.X86_64.N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = VG.Proof.CmacAes.X86_64.N s₀ - j ∧ j < VG.Proof.CmacAes.X86_64.N s₀ ∧ VG.Proof.CmacAes.X86_64.LInv s₀ j t) ?_ (VG.Proof.CmacAes.X86_64.N s₀ - k) s
    ⟨k, rfl, hk, h⟩
  rintro n s ⟨k, rfl, hk, h⟩
  refine WP.mono (VG.Proof.CmacAes.X86_64.body_ok v hp hk h) fun s' ⟨h', zf'⟩ => ?_
  by_cases hz : VG.Proof.CmacAes.X86_64.N s₀ - (k + 1) = 0
  · left
    refine ⟨by simp [eval, zf', hz], ?_⟩
    rwa [show VG.Proof.CmacAes.X86_64.N s₀ = k + 1 by omega]
  · right
    refine ⟨by simp [eval, zf', hz], VG.Proof.CmacAes.X86_64.N s₀ - (k + 1), by omega, k + 1, rfl, by omega, h'⟩

/-! ## Saving and restoring the registers -/

theorem readW_writeW_other (m : Mem) (b : Addr) {d e : Nat} (v : BitVec 64) (h : d + 8 ≤ e ∨ e + 8 ≤ d)
    (hd : d + 8 ≤ 2 ^ 64) (he : e + 8 ≤ 2 ^ 64) :
    (m.writeW (b + BitVec.ofNat 64 e) v).readW (b + BitVec.ofNat 64 d) 64 = m.readW (b + BitVec.ofNat 64 d) 64 :=
  Mem.readW_writeW_sep (Offset.sep b h hd he) (by decide)

/-! ## The whole function -/

theorem r8_ofNat (s₀ : State) : s₀.gpr .r8 = BitVec.ofNat 64 (VG.Proof.CmacAes.X86_64.N s₀) := by
  apply BitVec.eq_of_toNat_eq; simp [VG.Proof.CmacAes.X86_64.N]

theorem slots_disj {s₀ : State} (hp : VG.Proof.CmacAes.X86_64.UPre s₀) :
    ∀ r ∈ [VG.Proof.CmacAes.X86_64.stR s₀, ⟨VG.Proof.CmacAes.X86_64.S s₀, 2064⟩, VG.Proof.CmacAes.X86_64.stkR s₀], (⟨VG.Proof.CmacAes.X86_64.S s₀ + BitVec.ofNat 64 2064, 48⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.st_scr.symm.sub_left (UPre.scr_sub (by decide))
  · exact Offset.disjoint_base _ (by decide) (by have := hp.scr_wrap; omega)
  · exact hp.stk_scr.symm.sub_left (UPre.scr_sub (by decide))

theorem slot_read {s₀ : State} (hp : VG.Proof.CmacAes.X86_64.UPre s₀) {m : Mem}
    (hf : Frame [VG.Proof.CmacAes.X86_64.stR s₀, ⟨VG.Proof.CmacAes.X86_64.S s₀, 2064⟩, VG.Proof.CmacAes.X86_64.stkR s₀] (VG.Proof.CmacAes.X86_64.savedMem s₀) m) {d : Nat} (h₁ : 2064 ≤ d) (h₂ : d + 8 ≤ 2112) :
    m.readW (VG.Proof.CmacAes.X86_64.S s₀ + BitVec.ofNat 64 d) 64 = (VG.Proof.CmacAes.X86_64.savedMem s₀).readW (VG.Proof.CmacAes.X86_64.S s₀ + BitVec.ofNat 64 d) 64 :=
  hf.readW (r := ⟨VG.Proof.CmacAes.X86_64.S s₀ + BitVec.ofNat 64 2064, 48⟩) (VG.Proof.CmacAes.X86_64.slot_contains _ h₁ h₂) (VG.Proof.CmacAes.X86_64.slots_disj hp) (by decide)

theorem prologue_wp {s₀ : State} (hp : VG.Proof.CmacAes.X86_64.UPre s₀) :
    WP isa (.block (VG.Impl.CmacAes.X86_64.save ++ VG.Impl.CmacAes.X86_64.setup)) s₀ fun s₁ => VG.Proof.CmacAes.X86_64.LInv s₀ 0 s₁ ∧ s₁.zf = some (decide (VG.Proof.CmacAes.X86_64.N s₀ = 0)) := by
  have hN := (s₀.gpr .r8).isLt
  obtain ⟨s₁, run₁, rbx₁, rbp₁, r12₁, r13₁, r14₁, r15₁, rsp₁, zf₁, mem₁, rd₁, wr₁⟩ :=
    VG.Proof.CmacAes.X86_64.prologue_ok s₀ fun d _ h₂ => by
      rw [hp.wr]; exact VG.Proof.CmacAes.X86_64.in_rw (r := VG.Proof.CmacAes.X86_64.scrR s₀) (by simp) (Offset.contains_base _ (by omega) (by omega))
  refine WP.of_runBlock ⟨s₁, run₁, ?_, ?_⟩
  · have stSaved : Spec.Aes.bytesAt (VG.Proof.CmacAes.X86_64.savedMem s₀) (VG.Proof.CmacAes.X86_64.St s₀) 16 = Spec.Aes.bytesAt s₀.mem (VG.Proof.CmacAes.X86_64.St s₀) 16 :=
      VG.Proof.CmacAes.X86_64.bytesAt_frame' (VG.Proof.CmacAes.X86_64.savedMem_frame s₀) fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.st_scr.sub_right (UPre.scr_sub (by decide))
    exact { rbx := rbx₁, rbp := rbp₁, r12 := r12₁
            r13 := by rw [r13₁]; simp
            r14 := by rw [r14₁, VG.Proof.CmacAes.X86_64.r8_ofNat]; rfl
            r15 := r15₁, rsp := rsp₁, rd := rd₁, wr := wr₁
            frame := by rw [mem₁]; exact Frame.refl _ _
            state := by rw [mem₁, stSaved]; rfl }
  · rw [zf₁, VG.Proof.CmacAes.X86_64.r8_ofNat, VG.Proof.CmacAes.X86_64.beq_zero hN]

theorem mid_wp (v : Ctr32Impl) {s₀ : State} (hp : VG.Proof.CmacAes.X86_64.UPre s₀) {s₁ : State} (h : VG.Proof.CmacAes.X86_64.LInv s₀ 0 s₁)
    (hz : s₁.zf = some (decide (VG.Proof.CmacAes.X86_64.N s₀ = 0))) :
    WP isa (.ite .e (.block []) (.loop (VG.Impl.CmacAes.X86_64.body v.callee) .ne)) s₁ (VG.Proof.CmacAes.X86_64.LInv s₀ (VG.Proof.CmacAes.X86_64.N s₀)) := by
  have ev : isa.eval .e s₁ = some (decide (VG.Proof.CmacAes.X86_64.N s₀ = 0)) := hz
  by_cases hn : VG.Proof.CmacAes.X86_64.N s₀ = 0
  · refine WP.ite true (by rw [ev, hn]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    rw [hn]; exact h
  · refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
    exact VG.Proof.CmacAes.X86_64.loop_ok v hp (by omega) h

theorem epilogue_wp {s₀ : State} (hp : VG.Proof.CmacAes.X86_64.UPre s₀) {s₂ : State} (h₂ : VG.Proof.CmacAes.X86_64.LInv s₀ (VG.Proof.CmacAes.X86_64.N s₀) s₂) :
    WP isa (.block VG.Impl.CmacAes.X86_64.restore) s₂ fun s' => gprPreserved s₀ s' ∧ updateX86_64.post s₀ s' := by
  have rdwr : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [h₂.rd, h₂.wr]
  have hsv : Spill.Saved s₂.mem (s₂.gpr .r15) s₀.gpr VG.Impl.CmacAes.X86_64.saved := fun p hp' => by
    have := VG.Proof.CmacAes.X86_64.saved_bound p hp'
    rw [h₂.r15, VG.Proof.CmacAes.X86_64.slot_read hp h₂.frame this.1 this.2]
    exact Spill.saveMem_saved _ _ _ _ (by decide) p hp'
  refine WP.mono (Spill.restore_ok .r15 VG.Impl.CmacAes.X86_64.saved s₀.gpr s₂ (by decide) (fun p hp' => ?_) hsv)
    fun s₃ ⟨g₁, g₂, mem₃, _⟩ => ⟨⟨Spill.calleeSaved_ok g₁ g₂ (by decide) h₂.rsp, ?_⟩, ?_⟩
  · have := VG.Proof.CmacAes.X86_64.saved_bound p hp'
    rw [rdwr, hp.rd, hp.wr, h₂.r15]
    exact VG.Proof.CmacAes.X86_64.in_rw (r := VG.Proof.CmacAes.X86_64.scrR s₀) (by simp) (Offset.contains_base _ (by omega) (by have := hp.scr_wrap; omega))
  · rw [mem₃]
    refine (UPre.big_of h₂.frame).readW (r := ⟨s₀.gpr .rsp, 8⟩) (Region.contains_self _ _)
      (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.ret_st
    · exact hp.ret_scr
    · exact Offset.base_disjoint_below _ (by decide)
  · show Spec.Aes.bytesAt s₃.mem (VG.Proof.CmacAes.X86_64.St s₀) 16 = Spec.Cmac.chain (VG.Proof.CmacAes.X86_64.ciph s₀) _ (VG.Proof.CmacAes.X86_64.blks s₀)
    rw [mem₃, h₂.state, List.take_of_length_le (by simp [Spec.Cmac.blocksAt])]

theorem update_wp (v : Ctr32Impl) {s₀ : State} (h0 : updateX86_64.pre s₀) :
    WP isa (update v.callee) s₀ fun s' => gprPreserved s₀ s' ∧ updateX86_64.post s₀ s' := by
  have hp := UPre.of h0
  exact WP.seq (WP.mono (VG.Proof.CmacAes.X86_64.prologue_wp hp) fun s₁ ⟨h₁, z₁⟩ =>
    WP.seq (WP.mono (VG.Proof.CmacAes.X86_64.mid_wp v hp h₁ z₁) fun _ h₂ => VG.Proof.CmacAes.X86_64.epilogue_wp hp h₂))

end VG.Proof.CmacAes.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.X86_64.Subkeys`. -/
section

/-!
# AES-CMAC on x86-64: `vg_cmac_aes_subkeys`
-/

namespace VG.Proof.CmacAes.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.CmacAes.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-! ## Doubling a block -/

/-- The words `dbl` stores, from the halves `hi` and `lo` it loads. -/
def dblHi (hi lo : BitVec 64) : BitVec 64 := (hi + hi) ||| (lo >>> 63)
def dblLo (hi lo : BitVec 64) : BitVec 64 :=
  (lo + lo) ^^^ (((0 : BitVec 32).setWidth 64 - (hi >>> 63)) &&& BitVec.signExtend 64 (0x87 : BitVec 32))

/-- The memory after `dbl src dst`, from `rbx = K`. -/
def dblMem (m : Mem) (K : Addr) (src dst : Nat) : Mem :=
  let hi := bswap64 (m.readW (K + BitVec.ofNat 64 src) 64)
  let lo := bswap64 (m.readW (K + BitVec.ofNat 64 (src + 8)) 64)
  (m.writeW (K + BitVec.ofNat 64 dst) (bswap64 (VG.Proof.CmacAes.X86_64.dblHi hi lo))).writeW (K + BitVec.ofNat 64 (dst + 8))
    (bswap64 (VG.Proof.CmacAes.X86_64.dblLo hi lo))

theorem dbl_ok (s : State) {K : Addr} (hb : s.gpr .rbx = K) {src dst : Nat}
    (r₀ : InRegions (s.rd ++ s.wr) (K + BitVec.ofNat 64 src) 8)
    (r₁ : InRegions (s.rd ++ s.wr) (K + BitVec.ofNat 64 (src + 8)) 8)
    (w₀ : InRegions s.wr (K + BitVec.ofNat 64 dst) 8) (w₁ : InRegions s.wr (K + BitVec.ofNat 64 (dst + 8)) 8) :
    ∃ s', runBlock isa (dbl src dst) s = some s' ∧ s'.mem = VG.Proof.CmacAes.X86_64.dblMem s.mem K src dst ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLeDiff, Nat.reduceEqDiff, Nat.reduceSub, Nat.reducePow, and_self, BitVec.reduceSignExtend, dbl, runBlock_cons, runStep_some, runBlock_nil, at_, exec,
      readSrc, readSrc32, execAlu, execShift, State.load64, State.store64, State.ea, State.setReg32, VG.Proof.CmacAes.X86_64.offset_nat,
      Option.bind_some, Option.map_some, gpr_setReg, gpr_arithFlags, gpr_setFlags, mem_setReg, mem_arithFlags,
      mem_setFlags, rd_setReg, rd_arithFlags, rd_setFlags, wr_setReg, wr_arithFlags, wr_setFlags,
      hb, r₀, r₁, w₀, w₁]
    rfl, ?_⟩
  refine ⟨?_, ?_, rfl, rfl⟩
  · rfl
  · intro r h₁ h₂ h₃ h₄
    simp [gpr_setReg, gpr_setFlags, h₁, h₂, h₃, h₄]

theorem dbl_words' (hi lo : BitVec 64) : VG.Proof.CmacAes.X86_64.dblHi hi lo ++ VG.Proof.CmacAes.X86_64.dblLo hi lo = Proof.Cmac.dbl128 (hi ++ lo) := by
  rw [VG.Proof.CmacAes.X86_64.dblHi, VG.Proof.CmacAes.X86_64.dblLo, show (0 : BitVec 32).setWidth 64 = 0 from rfl]
  exact VG.Proof.CmacAes.X86_64.dbl_words hi lo

theorem dblMem_frame (m : Mem) (K : Addr) (src dst : Nat) :
    Frame [⟨K + BitVec.ofNat 64 dst, 16⟩] m (VG.Proof.CmacAes.X86_64.dblMem m K src dst) := by
  rw [VG.Proof.CmacAes.X86_64.dblMem, show K + BitVec.ofNat 64 (dst + 8) = K + BitVec.ofNat 64 dst + BitVec.ofNat 64 8 from
    (Offset.add_add _ _ _).symm]
  exact VG.Proof.CmacAes.X86_64.frame_store2 _ _ _

theorem dblMem_bytes (m : Mem) (K : Addr) (src dst : Nat) :
    Spec.Aes.bytesAt (VG.Proof.CmacAes.X86_64.dblMem m K src dst) (K + BitVec.ofNat 64 dst) 16 =
      Spec.Cmac.dbl 16 (Spec.Aes.bytesAt m (K + BitVec.ofNat 64 src) 16) := by
  rw [VG.Proof.CmacAes.X86_64.dblMem, show K + BitVec.ofNat 64 (dst + 8) = K + BitVec.ofNat 64 dst + BitVec.ofNat 64 8 from
      (Offset.add_add _ _ _).symm,
    show K + BitVec.ofNat 64 (src + 8) = K + BitVec.ofNat 64 src + BitVec.ofNat 64 8 from
      (Offset.add_add _ _ _).symm,
    Proof.Cmac.bytesAt_store2, VG.Proof.CmacAes.X86_64.le8_bswap, VG.Proof.CmacAes.X86_64.dbl_words', Proof.Cmac.dbl_eq (Proof.Cmac.bytesAt_length _ _ _),
    ← Spec.Gcm.blockAt, ← Proof.Gcm.X86_64.blockAt_bswap, BitVec.add_zero]

/-! ## Before the call -/

/-- The memory after `subkeysPre`. -/
def preMem (s : State) : Mem :=
  (((((s.mem.writeW (s.gpr .rcx + BitVec.ofNat 64 2064) (s.gpr .rbx)).writeW
    (s.gpr .rcx + BitVec.ofNat 64 2072) (s.gpr .rbp)).writeW
    (s.gpr .rcx + BitVec.ofNat 64 2048) (BitVec.setWidth 64 (0 : BitVec 32))).writeW
    (s.gpr .rcx + BitVec.ofNat 64 2056) (BitVec.setWidth 64 (0 : BitVec 32))).writeW
    (s.gpr .rdx + BitVec.ofNat 64 0) (BitVec.setWidth 64 (0 : BitVec 32))).writeW
    (s.gpr .rdx + BitVec.ofNat 64 8) (BitVec.setWidth 64 (0 : BitVec 32))

theorem subkeysPre_ok (s : State)
    (w₁ : InRegions s.wr (s.gpr .rcx + BitVec.ofNat 64 2064) 8)
    (w₂ : InRegions s.wr (s.gpr .rcx + BitVec.ofNat 64 2072) 8)
    (w₃ : InRegions s.wr (s.gpr .rcx + BitVec.ofNat 64 2048) 8)
    (w₄ : InRegions s.wr (s.gpr .rcx + BitVec.ofNat 64 2056) 8)
    (w₅ : InRegions s.wr (s.gpr .rdx + BitVec.ofNat 64 0) 8)
    (w₆ : InRegions s.wr (s.gpr .rdx + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa subkeysPre s = some s' ∧
      s'.gpr .rdi = s.gpr .rdi ∧ s'.gpr .rsi = s.gpr .rsi ∧
      s'.gpr .rdx = s.gpr .rcx + BitVec.ofNat 64 2048 ∧ s'.gpr .rcx = s.gpr .rdx ∧ s'.gpr .r8 = 1 ∧
      s'.gpr .r9 = s.gpr .rcx ∧ s'.gpr .rbx = s.gpr .rdx ∧ s'.gpr .rbp = s.gpr .rcx ∧
      (∀ r ∈ calleeSaved, r ≠ .rbx → r ≠ .rbp → s'.gpr r = s.gpr r) ∧
      s'.mem = VG.Proof.CmacAes.X86_64.preMem s ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceAdd, Nat.reducePow, BitVec.reduceSignExtend, subkeysPre, ctrArgs, cOff, List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc, readSrc32, execAlu, State.store64,
      State.ea, State.setReg32, VG.Proof.CmacAes.X86_64.offset_nat, Option.bind_some, Option.map_some, gpr_setReg, gpr_arithFlags,
      mem_setReg, rd_setReg, wr_setReg, w₁, w₂, w₃, w₄, w₅, w₆]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | rfl
    | (simp [gpr_setReg]; done)
    | (intro r hr h₁ h₂
       simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [gpr_setReg])

/-! ## The whole function -/

/-- The precondition, by name: the schedule `W`, the subkeys `K`, the scratch
buffer `S` and the rounds `R`. -/
structure SPre (s₀ : State) (W K S : Addr) (R : Nat) : Prop where
  rdi : s₀.gpr .rdi = W
  rdx : s₀.gpr .rdx = K
  rcx : s₀.gpr .rcx = S
  rsi : (s₀.gpr .rsi).toNat = R
  rd : s₀.rd = [⟨W, 240⟩]
  wr : s₀.wr = [⟨K, 32⟩, ⟨S, 2176⟩]
  sch_k : (⟨W, 240⟩ : Region).Disjoint ⟨K, 32⟩
  sch_scr : (⟨W, 240⟩ : Region).Disjoint ⟨S, 2176⟩
  k_scr : (⟨K, 32⟩ : Region).Disjoint ⟨S, 2176⟩
  ret_k : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨K, 32⟩
  ret_scr : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨S, 2176⟩
  stk_sch : (below (s₀.gpr .rsp) 8).Disjoint ⟨W, 240⟩
  stk_k : (below (s₀.gpr .rsp) 8).Disjoint ⟨K, 32⟩
  stk_scr : (below (s₀.gpr .rsp) 8).Disjoint ⟨S, 2176⟩
  k_wrap : K.toNat + 32 ≤ 2 ^ 64
  scr_wrap : S.toNat + 2176 ≤ 2 ^ 64
  rounds : R = 10 ∨ R = 12 ∨ R = 14

theorem SPre.of {s₀ : State} (h : subkeysX86_64.pre s₀) :
    VG.Proof.CmacAes.X86_64.SPre s₀ (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .rsi).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m⟩ := h
  ⟨rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i, j, k, l, m⟩

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

theorem zero_le8 : Proof.Cmac.le8 (BitVec.setWidth 64 (0 : BitVec 32)) = Spec.Cmac.zeros 8 := by decide

theorem scr_sub' {S : Addr} {d n : Nat} (h : d + n ≤ 2176) :
    Region.Sub ⟨S + BitVec.ofNat 64 d, n⟩ ⟨S, 2176⟩ := Offset.sub_base _ h


theorem preMem_frame (s : State) :
    Frame [⟨s.gpr .rcx + BitVec.ofNat 64 2048, 32⟩, ⟨s.gpr .rdx, 16⟩] s.mem (VG.Proof.CmacAes.X86_64.preMem s) := by
  have c (d : Nat) (h : d + 8 ≤ 32) :
      (⟨s.gpr .rcx + BitVec.ofNat 64 2048, 32⟩ : Region).Contains (s.gpr .rcx + BitVec.ofNat 64 (2048 + d)) 8 := by
    rw [← Offset.add_add]; exact Offset.contains_base _ h (by omega)
  have k (d : Nat) (h : d + 8 ≤ 16) : (⟨s.gpr .rdx, 16⟩ : Region).Contains (s.gpr .rdx + BitVec.ofNat 64 d) 8 :=
    Offset.contains_base _ h (by omega)
  exact ((((((Frame.refl _ _).writeW (by simp) _ (c 16 (by decide))).writeW (by simp) _ (c 24 (by decide))).writeW
    (by simp) _ (c 0 (by decide))).writeW (by simp) _ (c 8 (by decide))).writeW (by simp) _ (k 0 (by decide))).writeW
    (by simp) _ (k 8 (by decide))

theorem frame_store2' {m : Mem} (p : Addr) (w₀ w₁ : BitVec 64) :
    Frame [⟨p, 16⟩] m ((m.writeW (p + BitVec.ofNat 64 0) w₀).writeW (p + BitVec.ofNat 64 8) w₁) := by
  rw [VG.Proof.CmacAes.X86_64.k0]; exact VG.Proof.CmacAes.X86_64.frame_store2 _ _ _

theorem restore2_ok (s : State) {B : Addr} (hb : s.gpr .rbp = B)
    (r₁ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 2064) 8)
    (r₂ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 2072) 8) :
    ∃ s', runBlock isa [.mov .rbx (.mem (at_ .rbp 2064)), .mov .rbp (.mem (at_ .rbp 2072))] s = some s' ∧
      s'.gpr .rbx = s.mem.readW (B + BitVec.ofNat 64 2064) 64 ∧
      s'.gpr .rbp = s.mem.readW (B + BitVec.ofNat 64 2072) 64 ∧
      (∀ r, r ≠ .rbx → r ≠ .rbp → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc,
      State.load64, State.ea, VG.Proof.CmacAes.X86_64.offset_nat, gpr_setReg, mem_setReg, rd_setReg, wr_setReg,
      Option.map_some, hb, r₁, r₂]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, rfl⟩
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]

theorem preMem_slot (s : State) {d : Nat} (hd : d = 2064 ∨ d = 2072)
    (hks : (⟨s.gpr .rdx, 32⟩ : Region).Disjoint ⟨s.gpr .rcx, 2176⟩) :
    (VG.Proof.CmacAes.X86_64.preMem s).readW (s.gpr .rcx + BitVec.ofNat 64 d) 64 = if d = 2064 then s.gpr .rbx else s.gpr .rbp := by
  have kd (e : Nat) (he : e + 8 ≤ 32) : Mem.Sep (s.gpr .rcx + BitVec.ofNat 64 d) (64 / 8)
      (s.gpr .rdx + BitVec.ofNat 64 e) (64 / 8) :=
    hks.symm.sep (Offset.contains_base _ (by omega) (by omega)) (Offset.contains_base _ he (by omega))
  rw [VG.Proof.CmacAes.X86_64.preMem, Mem.readW_writeW_sep (kd 8 (by decide)) (by decide), Mem.readW_writeW_sep (kd 0 (by decide)) (by decide),
    VG.Proof.CmacAes.X86_64.readW_writeW_other _ _ _ (by omega) (by omega) (by decide),
    VG.Proof.CmacAes.X86_64.readW_writeW_other _ _ _ (by omega) (by omega) (by decide)]
  rcases hd with rfl | rfl
  · rw [VG.Proof.CmacAes.X86_64.readW_writeW_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]; rfl
  · rw [Mem.readW_writeW_self64]; rfl

theorem callPre_of {s₀ : State} {W K S : Addr} {R : Nat} (hp : VG.Proof.CmacAes.X86_64.SPre s₀ W K S R) {s₁ : State}
    (rdi₁ : s₁.gpr .rdi = s₀.gpr .rdi) (rsi₁ : s₁.gpr .rsi = s₀.gpr .rsi)
    (rdx₁ : s₁.gpr .rdx = s₀.gpr .rcx + BitVec.ofNat 64 2048) (rcx₁ : s₁.gpr .rcx = s₀.gpr .rdx)
    (r8₁ : s₁.gpr .r8 = 1) (r9₁ : s₁.gpr .r9 = s₀.gpr .rcx) (rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp)
    (mem₁ : s₁.mem = VG.Proof.CmacAes.X86_64.preMem s₀) (rd₁ : s₁.rd = s₀.rd) (wr₁ : s₁.wr = s₀.wr) :
    VG.Proof.CmacAes.X86_64.CallPre s₁ W (S + BitVec.ofNat 64 2048) K S R := by
  have hR := hp.rounds
  have kw := hp.k_wrap
  have sw := hp.scr_wrap
  have cK : (⟨K, 16⟩ : Region).Disjoint ⟨S + BitVec.ofNat 64 2048, 16⟩ :=
    (hp.k_scr.sub_left (Region.sub_prefix (by decide))).sub_right (VG.Proof.CmacAes.X86_64.scr_sub' (by decide))
  have zK : Spec.Aes.bytesAt s₁.mem K 16 = Spec.Cmac.zeros 16 := by
    rw [mem₁, VG.Proof.CmacAes.X86_64.preMem, hp.rdx, VG.Proof.CmacAes.X86_64.k0, Proof.Cmac.bytesAt_store2, VG.Proof.CmacAes.X86_64.zero_le8, VG.Proof.CmacAes.X86_64.zeros_8_8]
  exact
      { rdi := by rw [rdi₁, hp.rdi]
        rsi := by rw [rsi₁]; apply BitVec.eq_of_toNat_eq; simp [hp.rsi]; omega
        rdx := by rw [rdx₁, hp.rcx]
        rcx := by rw [rcx₁, hp.rdx]
        r8 := r8₁
        r9 := by rw [r9₁, hp.rcx]
        rounds := hR
        wc := hp.sch_scr.sub_right (VG.Proof.CmacAes.X86_64.scr_sub' (by decide))
        wd := hp.sch_k.sub_right (Region.sub_prefix (by decide))
        ws := hp.sch_scr.sub_right (Region.sub_prefix (by decide))
        cd := cK.symm
        cs := Offset.disjoint_base _ (by decide) (by omega)
        ds := (hp.k_scr.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
        stkW := by rw [rsp₁]; exact hp.stk_sch
        stkC := by rw [rsp₁]; exact hp.stk_scr.sub_right (VG.Proof.CmacAes.X86_64.scr_sub' (by decide))
        stkD := by rw [rsp₁]; exact hp.stk_k.sub_right (Region.sub_prefix (by decide))
        stkS := by rw [rsp₁]; exact hp.stk_scr.sub_right (Region.sub_prefix (by decide))
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

theorem subkeys_wp (v : Ctr32Impl) {s₀ : State} (h0 : subkeysX86_64.pre s₀) :
    WP isa (subkeys v.callee) s₀ fun s' => gprPreserved s₀ s' ∧ subkeysX86_64.post s₀ s' := by
  have hp := SPre.of h0
  generalize s₀.gpr .rdi = W at hp
  generalize s₀.gpr .rdx = K at hp
  generalize s₀.gpr .rcx = S at hp
  generalize (s₀.gpr .rsi).toNat = R at hp
  have hR := hp.rounds
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with h | h | h <;> omega
  have kw := hp.k_wrap
  have sw := hp.scr_wrap
  have inS (d : Nat) (h : d + 8 ≤ 2176) : InRegions s₀.wr (S + BitVec.ofNat 64 d) 8 := by
    rw [hp.wr]; exact VG.Proof.CmacAes.X86_64.in_rw (r := ⟨S, 2176⟩) (by simp) (Offset.contains_base _ h (by omega))
  have inK (d : Nat) (h : d + 8 ≤ 32) : InRegions s₀.wr (K + BitVec.ofNat 64 d) 8 := by
    rw [hp.wr]; exact VG.Proof.CmacAes.X86_64.in_rw (r := ⟨K, 32⟩) (by simp) (Offset.contains_base _ h (by omega))
  -- Before the call.
  obtain ⟨s₁, run₁, rdi₁, rsi₁, rdx₁, rcx₁, r8₁, r9₁, rbx₁, rbp₁, cs₁, mem₁, rd₁, wr₁⟩ :=
    VG.Proof.CmacAes.X86_64.subkeysPre_ok s₀ (by rw [hp.rcx]; exact inS _ (by decide)) (by rw [hp.rcx]; exact inS _ (by decide))
      (by rw [hp.rcx]; exact inS _ (by decide)) (by rw [hp.rcx]; exact inS _ (by decide))
      (by rw [hp.rdx]; exact inK _ (by decide)) (by rw [hp.rdx]; exact inK _ (by decide))
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  -- The memory before the call.
  have f₁ : Frame [⟨S + BitVec.ofNat 64 2048, 32⟩, ⟨K, 16⟩] s₀.mem s₁.mem := by
    rw [mem₁, ← hp.rcx, ← hp.rdx]; exact VG.Proof.CmacAes.X86_64.preMem_frame s₀
  have cK : (⟨K, 16⟩ : Region).Disjoint ⟨S + BitVec.ofNat 64 2048, 16⟩ :=
    (hp.k_scr.sub_left (Region.sub_prefix (by decide))).sub_right (VG.Proof.CmacAes.X86_64.scr_sub' (by decide))
  have zC : Spec.Aes.bytesAt s₁.mem (S + BitVec.ofNat 64 2048) 16 = Spec.Cmac.zeros 16 := by
    rw [mem₁, VG.Proof.CmacAes.X86_64.preMem, hp.rcx, hp.rdx]
    rw [VG.Proof.CmacAes.X86_64.bytesAt_frame' (VG.Proof.CmacAes.X86_64.frame_store2' K _ _) (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact cK.symm)]
    rw [(Offset.add_add_eq S (a := 2048) (b := 8) (c := 2056) rfl).symm, Proof.Cmac.bytesAt_store2, VG.Proof.CmacAes.X86_64.zero_le8,
      VG.Proof.CmacAes.X86_64.zeros_8_8]
  have zK : Spec.Aes.bytesAt s₁.mem K 16 = Spec.Cmac.zeros 16 := by
    rw [mem₁, VG.Proof.CmacAes.X86_64.preMem, hp.rdx, VG.Proof.CmacAes.X86_64.k0, Proof.Cmac.bytesAt_store2, VG.Proof.CmacAes.X86_64.zero_le8, VG.Proof.CmacAes.X86_64.zeros_8_8]
  have schB : ∀ m : Mem, Frame [⟨S + BitVec.ofNat 64 2048, 32⟩, ⟨K, 16⟩] s₀.mem m →
      Spec.Aes.bytesAt m W (16 * (R + 1)) = Spec.Aes.bytesAt s₀.mem W (16 * (R + 1)) := fun m hf =>
    VG.Proof.CmacAes.X86_64.bytesAt_frame hf (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hp.sch_scr.sub_left (Region.sub_prefix hRb)).sub_right (VG.Proof.CmacAes.X86_64.scr_sub' (by decide))
      · exact (hp.sch_k.sub_left (Region.sub_prefix hRb)).sub_right (Region.sub_prefix (by decide))) (by omega)
  -- The call.
  have rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := cs₁ .rsp (by simp [calleeSaved]) (by decide) (by decide)
  have pre := VG.Proof.CmacAes.X86_64.callPre_of hp rdi₁ rsi₁ rdx₁ rcx₁ r8₁ r9₁ rsp₁ mem₁ rd₁ wr₁
  refine WP.seq (WP.mono (VG.Proof.CmacAes.X86_64.ctr_call v pre) fun s₂ h₂ => ?_)
  -- After the call.
  have rbx₂ : s₂.gpr .rbx = K := by rw [h₂.saved .rbx (by simp [calleeSaved]), rbx₁, hp.rdx]
  have rbp₂ : s₂.gpr .rbp = S := by rw [h₂.saved .rbp (by simp [calleeSaved]), rbp₁, hp.rcx]
  have rdwr₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [h₂.rd, h₂.wr, rd₁, wr₁]
  have wr₂ : s₂.wr = s₀.wr := by rw [h₂.wr, wr₁]
  have rIn (a : Addr) (h : InRegions s₀.wr a 8) : InRegions (s₀.rd ++ s₀.wr) a 8 := by
    obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩
  rw [subkeysPost, WP.block_append_iff, WP.block_append_iff]
  obtain ⟨s₃, run₃, mem₃, g₃, rd₃, wr₃⟩ := VG.Proof.CmacAes.X86_64.dbl_ok s₂ rbx₂ (src := 0) (dst := 0)
    (by rw [rdwr₂]; exact rIn _ (inK 0 (by decide))) (by rw [rdwr₂]; exact rIn _ (inK 8 (by decide)))
    (by rw [wr₂]; exact inK 0 (by decide)) (by rw [wr₂]; exact inK 8 (by decide))
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have rbx₃ : s₃.gpr .rbx = K := by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), rbx₂]
  obtain ⟨s₄, run₄, mem₄, g₄, rd₄, wr₄⟩ := VG.Proof.CmacAes.X86_64.dbl_ok s₃ rbx₃ (src := 0) (dst := 16)
    (by rw [rd₃, wr₃, rdwr₂]; exact rIn _ (inK 0 (by decide)))
    (by rw [rd₃, wr₃, rdwr₂]; exact rIn _ (inK 8 (by decide)))
    (by rw [wr₃, wr₂]; exact inK 16 (by decide)) (by rw [wr₃, wr₂]; exact inK 24 (by decide))
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  have rbp₄ : s₄.gpr .rbp = S := by
    rw [g₄ _ (by decide) (by decide) (by decide) (by decide), g₃ _ (by decide) (by decide) (by decide) (by decide),
      rbp₂]
  obtain ⟨s₅, run₅, rbx₅, rbp₅, g₅, mem₅⟩ := VG.Proof.CmacAes.X86_64.restore2_ok s₄ rbp₄
    (by rw [rd₄, wr₄, rd₃, wr₃, rdwr₂]; exact rIn _ (inS 2064 (by decide)))
    (by rw [rd₄, wr₄, rd₃, wr₃, rdwr₂]; exact rIn _ (inS 2072 (by decide)))
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  -- Memory.
  have f₂ := h₂.frame
  have f₃ : Frame [⟨K + BitVec.ofNat 64 0, 16⟩] s₂.mem s₃.mem := by rw [mem₃]; exact VG.Proof.CmacAes.X86_64.dblMem_frame _ _ _ _
  have f₄ : Frame [⟨K + BitVec.ofNat 64 16, 16⟩] s₃.mem s₄.mem := by rw [mem₄]; exact VG.Proof.CmacAes.X86_64.dblMem_frame _ _ _ _
  have slotD : ∀ r ∈ [⟨S + BitVec.ofNat 64 2048, 16⟩, ⟨K, 16⟩, ⟨S, 2048⟩, below (s₁.gpr .rsp) 8],
      (⟨S + BitVec.ofNat 64 2064, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Offset.disjoint S (by decide) (by omega) (by omega)
    · exact (hp.k_scr.symm.sub_left (VG.Proof.CmacAes.X86_64.scr_sub' (by decide))).sub_right (Region.sub_prefix (by decide))
    · exact Offset.disjoint_base _ (by decide) (by omega)
    · rw [rsp₁]; exact (hp.stk_scr.symm.sub_left (VG.Proof.CmacAes.X86_64.scr_sub' (by decide)))
  have slotK (e : Nat) (he : e ≤ 16) : (⟨S + BitVec.ofNat 64 2064, 16⟩ : Region).Disjoint ⟨K + BitVec.ofNat 64 e, 16⟩ :=
    (hp.k_scr.symm.sub_left (VG.Proof.CmacAes.X86_64.scr_sub' (by decide))).sub_right (Offset.sub_base _ (by omega))
  have slot (d : Nat) (h₁ : 2064 ≤ d) (h₂' : d + 8 ≤ 2080) :
      s₄.mem.readW (S + BitVec.ofNat 64 d) 64 = s₁.mem.readW (S + BitVec.ofNat 64 d) 64 := by
    have c : (⟨S + BitVec.ofNat 64 2064, 16⟩ : Region).Contains (S + BitVec.ofNat 64 d) (64 / 8) := by
      rw [show S + BitVec.ofNat 64 d = S + BitVec.ofNat 64 2064 + BitVec.ofNat 64 (d - 2064) from
        (Offset.add_add_eq S (by omega)).symm]
      exact Offset.contains_base _ (by omega) (by omega)
    rw [f₄.readW c (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact slotK 16 (by decide))
        (by decide),
      f₃.readW c (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact slotK 0 (by decide))
        (by decide),
      f₂.readW c slotD (by decide)]
  have pslot := fun d hd => VG.Proof.CmacAes.X86_64.preMem_slot s₀ (d := d) hd (by rw [hp.rdx, hp.rcx]; exact hp.k_scr)
  rw [hp.rcx] at pslot
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · by_cases hb : r = .rbx
    · subst hb; rw [rbx₅, slot 2064 (by decide) (by decide), mem₁, pslot 2064 (.inl rfl)]; rfl
    by_cases hb' : r = .rbp
    · subst hb'; rw [rbp₅, slot 2072 (by decide) (by decide), mem₁, pslot 2072 (.inr rfl)]; rfl
    rw [g₅ r hb hb', g₄ r (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)
      (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr),
      g₃ r (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)
      (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr),
      h₂.saved r hr, cs₁ r hr hb hb']
  · have fall : Frame [⟨K, 32⟩, ⟨S, 2176⟩, below (s₀.gpr .rsp) 8] s₀.mem s₅.mem := by
      rw [mem₅]
      refine ((f₁.sub fun r hr => ?_).trans (f₂.sub fun r hr => ?_)).trans
        ((f₃.sub fun r hr => ?_).trans (f₄.sub fun r hr => ?_))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨⟨S, 2176⟩, by simp, VG.Proof.CmacAes.X86_64.scr_sub' (by decide)⟩
        · exact ⟨⟨K, 32⟩, by simp, Region.sub_prefix (by decide)⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact ⟨⟨S, 2176⟩, by simp, VG.Proof.CmacAes.X86_64.scr_sub' (by decide)⟩
        · exact ⟨⟨K, 32⟩, by simp, Region.sub_prefix (by decide)⟩
        · exact ⟨⟨S, 2176⟩, by simp, Region.sub_prefix (by decide)⟩
        · exact ⟨below (s₀.gpr .rsp) 8, by simp, by rw [rsp₁]; exact fun _ h => h⟩
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨⟨K, 32⟩, by simp, Offset.sub_base _ (by decide)⟩
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨⟨K, 32⟩, by simp, Offset.sub_base _ (by decide)⟩
    refine fall.readW (r := ⟨s₀.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.ret_k
    · exact hp.ret_scr
    · exact Offset.base_disjoint_below _ (by decide)
  · show Spec.Aes.bytesAt s₅.mem (s₀.gpr .rdx) 32 = _
    rw [hp.rdx, hp.rdi, hp.rsi, mem₅, VG.Proof.CmacAes.X86_64.bytesAt_32]
    have L : Spec.Aes.bytesAt s₂.mem K 16 = VG.Proof.CmacAes.X86_64.ciphAt s₀.mem W R (Spec.Cmac.zeros 16) := by
      rw [h₂.out, schB _ f₁, zC]
    have b3 : Spec.Aes.bytesAt s₃.mem K 16 = Spec.Cmac.dbl 16 (Spec.Aes.bytesAt s₂.mem K 16) := by
      have := VG.Proof.CmacAes.X86_64.dblMem_bytes s₂.mem K 0 0
      rw [VG.Proof.CmacAes.X86_64.k0] at this; rw [mem₃, this]
    have b4lo : Spec.Aes.bytesAt s₄.mem K 16 = Spec.Aes.bytesAt s₃.mem K 16 :=
      VG.Proof.CmacAes.X86_64.bytesAt_frame' f₄ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (Offset.disjoint_base K (by decide) (by omega)).symm
    have b4hi : Spec.Aes.bytesAt s₄.mem (K + BitVec.ofNat 64 16) 16 =
        Spec.Cmac.dbl 16 (Spec.Aes.bytesAt s₃.mem K 16) := by
      have := VG.Proof.CmacAes.X86_64.dblMem_bytes s₃.mem K 0 16
      rw [VG.Proof.CmacAes.X86_64.k0] at this; rw [mem₄, this]
    rw [b4lo, b4hi, b3, L]
    rfl

end VG.Proof.CmacAes.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.X86_64.Finalize`. -/
section

/-!
# AES-CMAC on x86-64: `vg_cmac_aes_finalize`, the last block

The steps that form the counter block `C ⊕ Mₙ` in the scratch buffer before
the call.
-/

namespace VG.Proof.CmacAes.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.CmacAes.X86_64

/-! ## XORing two blocks, a word at a time -/

/-- The memory after storing at `c` the XOR of the blocks at `p` and `q`,
a word at a time. -/
def xor2Mem (m : Mem) (c p q : Addr) : Mem :=
  let m₁ := m.writeW c (m.readW p 64 ^^^ m.readW q 64)
  m₁.writeW (c + BitVec.ofNat 64 8) (m₁.readW (p + BitVec.ofNat 64 8) 64 ^^^ m₁.readW (q + BitVec.ofNat 64 8) 64)

theorem xor2Mem_frame (m : Mem) (c p q : Addr) : Frame [⟨c, 16⟩] m (VG.Proof.CmacAes.X86_64.xor2Mem m c p q) := VG.Proof.CmacAes.X86_64.frame_store2 _ _ _

theorem xor2Mem_bytes (m : Mem) {c p q : Addr}
    (hp : (⟨c, 8⟩ : Region).Disjoint ⟨p + BitVec.ofNat 64 8, 8⟩)
    (hq : (⟨c, 8⟩ : Region).Disjoint ⟨q + BitVec.ofNat 64 8, 8⟩) :
    Spec.Aes.bytesAt (VG.Proof.CmacAes.X86_64.xor2Mem m c p q) c 16 =
      Spec.Cmac.xor (Spec.Aes.bytesAt m p 16) (Spec.Aes.bytesAt m q 16) := by
  have g : Frame [⟨c, 8⟩] m (m.writeW c (m.readW p 64 ^^^ m.readW q 64)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  rw [VG.Proof.CmacAes.X86_64.xor2Mem, Proof.Cmac.bytesAt_store2,
    g.readW (r := ⟨p + BitVec.ofNat 64 8, 8⟩) (Region.contains_self _ _)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.symm) (by decide),
    g.readW (r := ⟨q + BitVec.ofNat 64 8, 8⟩) (Region.contains_self _ _)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hq.symm) (by decide)]
  exact Proof.Cmac.xor_words m p q

theorem xor_comm (x y : List Byte) : Spec.Cmac.xor x y = Spec.Cmac.xor y x := by
  simp only [Spec.Cmac.xor]
  exact List.zipWith_comm_of_comm (fun a b => BitVec.xor_comm a b)

/-! ## Copying the last bytes -/

/-- The copy loop's body. -/
abbrev copyBody : List Instr :=
  [.movzx8 .rax lastByte, .store8 padByte .rax, .alu .add .r10 (.imm 1), .alu .cmp .r10 (.reg .r8)]

theorem copyStep_ok (s : State) {P C : Addr} {i L : Nat} (hc : s.gpr .rcx = P)
    (h9 : s.gpr .r9 + BitVec.ofNat 64 2048 = C) (hi : s.gpr .r10 = BitVec.ofNat 64 i)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 L)
    (r : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) 1) (w : InRegions s.wr (C + BitVec.ofNat 64 i) 1) :
    ∃ s', runBlock isa VG.Proof.CmacAes.X86_64.copyBody s = some s' ∧
      s'.mem = s.mem.writeW (C + BitVec.ofNat 64 i) (s.mem (P + BitVec.ofNat 64 i)) ∧
      s'.gpr .r10 = BitVec.ofNat 64 i + 1 ∧
      s'.zf = some (BitVec.ofNat 64 i + 1 - BitVec.ofNat 64 L == 0) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ea₁ : s.gpr .rcx + s.gpr .r10 * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 = P + BitVec.ofNat 64 i := by
    rw [hc, hi, BitVec.mul_one]; simp
  have ea₂ : s.gpr .r9 + s.gpr .r10 * BitVec.ofNat 64 1 + BitVec.ofInt 64 (cOff : Int) = C + BitVec.ofNat 64 i := by
    rw [hi, BitVec.mul_one, ← h9, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 i)]
    rfl
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, BitVec.reduceSignExtend, VG.Proof.CmacAes.X86_64.copyBody, lastByte, padByte, runBlock_cons, runStep_some,
      runBlock_nil, exec, readSrc, execAlu, State.load8, State.store8, State.ea, Option.bind_some,
      Option.map_some, gpr_setReg, gpr_arithFlags, mem_setReg, rd_setReg, wr_setReg,
      ea₁, ea₂, r, w]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 64 by decide),
      BitVec.setWidth_eq]
  · simp [gpr_setReg, hi]
  · simp [hi, h8]
  · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]
  · rfl
  · rfl

theorem succ_ofNat (i : Nat) : BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) := (BitVec.ofNat_add i 1).symm

open VG.WriteBytes in
theorem bytesAt_succ (m : Mem) (p : Addr) (i : Nat) :
    Spec.Aes.bytesAt m p (i + 1) = Spec.Aes.bytesAt m p i ++ [m (p + BitVec.ofNat 64 i)] := by
  simp [Spec.Aes.bytesAt, List.range_succ]

open VG.WriteBytes in
theorem copy_ok (s : State) {P C : Addr} {L : Nat} (hL₀ : 0 < L) (hL : L < 16) (hc : s.gpr .rcx = P)
    (h9 : s.gpr .r9 + BitVec.ofNat 64 2048 = C) (h8 : s.gpr .r8 = BitVec.ofNat 64 L)
    (hr : ∀ i < L, InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < 16, InRegions s.wr (C + BitVec.ofNat 64 i) 1)
    (hd : (⟨P, L⟩ : Region).Disjoint ⟨C, 16⟩) :
    WP isa copy s fun s' => s'.mem = writeBytes s.mem C (Spec.Aes.bytesAt s.mem P L) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, r10₁, g₁⟩ : ∃ s₁, runBlock isa [.mov32 .r10 (.imm 0)] s = some s₁ ∧
      s₁.gpr .r10 = BitVec.ofNat 64 0 ∧ s₁ = s.setReg .r10 (BitVec.setWidth 64 (0 : BitVec 32)) :=
    ⟨_, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
      State.setReg32], by simp [gpr_setReg], rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  subst g₁
  refine WP.loop (M := isa) (body := .block VG.Proof.CmacAes.X86_64.copyBody) (c := .ne)
    (fun (n : Nat) (t : State) => ∃ i, n = L - i ∧ i < L ∧ t.gpr .r10 = BitVec.ofNat 64 i ∧
      t.mem = writeBytes s.mem C (Spec.Aes.bytesAt s.mem P i) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (L - 0) _
    ⟨0, rfl, hL₀, r10₁, by simp [Spec.Aes.bytesAt, writeBytes_nil, mem_setReg],
      fun r h₁ h₂ => by simp [gpr_setReg, h₂], rfl, rfl⟩
  rintro n t ⟨i, rfl, hi, r10, mem, g, rd, wr⟩
  have tc : t.gpr .rcx = P := by rw [g _ (by decide) (by decide), hc]
  have t9 : t.gpr .r9 + BitVec.ofNat 64 2048 = C := by rw [g _ (by decide) (by decide), h9]
  have t8 : t.gpr .r8 = BitVec.ofNat 64 L := by rw [g _ (by decide) (by decide), h8]
  obtain ⟨t', run', mem', r10', zf', g', rd', wr'⟩ := VG.Proof.CmacAes.X86_64.copyStep_ok t tc t9 r10 t8
    (by rw [rd, wr]; exact hr i hi) (by rw [wr]; exact hw i (by omega))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hlen : (Spec.Aes.bytesAt s.mem P i).length = i := by simp [Spec.Aes.bytesAt]
  have hx : writeBytes s.mem C (Spec.Aes.bytesAt s.mem P i) (P + BitVec.ofNat 64 i) = s.mem (P + BitVec.ofNat 64 i) :=
    (writeBytes_frame s.mem C _ (R := ⟨C, i⟩) (by rw [hlen]; exact Region.contains_self _ _)) _
      fun r hr hcon => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hd _ (Offset.contains_base P (by omega) (by omega)) (Region.sub_prefix (by omega) _ hcon)
  have hmem : t'.mem = writeBytes s.mem C (Spec.Aes.bytesAt s.mem P (i + 1)) := by
    rw [mem', mem, hx, VG.Proof.CmacAes.X86_64.bytesAt_succ, writeBytes_snoc s.mem C (Spec.Aes.bytesAt s.mem P i) (s.mem (P + BitVec.ofNat 64 i))
      (by rw [hlen]; omega), hlen]
  have hz : t'.zf = some (decide (i + 1 = L)) := by
    rw [zf', VG.Proof.CmacAes.X86_64.succ_ofNat, Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
  have gg : ∀ r, r ≠ .rax → r ≠ .r10 → t'.gpr r = s.gpr r := fun r h₁ h₂ => by rw [g' r h₁ h₂, g r h₁ h₂]
  by_cases he : i + 1 = L
  · left
    refine ⟨by simp [eval, hz, he], by rw [hmem, he], gg, by rw [rd', rd], by rw [wr', wr]⟩
  · right
    refine ⟨by simp [eval, hz, he], L - (i + 1), by omega, i + 1, rfl, by omega, by rw [r10', VG.Proof.CmacAes.X86_64.succ_ofNat], hmem, gg,
      by rw [rd', rd], by rw [wr', wr]⟩

/-! ## The straight-line pieces -/

/-- Two words XORed from `[p]` and `[q]` into `[c]`, as `full`, `padK2` and
`finArgs` do. -/
theorem xor2_ok (s : State) (pb qb cb : Reg) (pd qd cd : Nat) {P Q C : Addr}
    (hp : s.gpr pb + BitVec.ofNat 64 pd = P) (hp8 : s.gpr pb + BitVec.ofNat 64 (pd + 8) = P + BitVec.ofNat 64 8)
    (hq : s.gpr qb + BitVec.ofNat 64 qd = Q) (hq8 : s.gpr qb + BitVec.ofNat 64 (qd + 8) = Q + BitVec.ofNat 64 8)
    (hc : s.gpr cb + BitVec.ofNat 64 cd = C) (hc8 : s.gpr cb + BitVec.ofNat 64 (cd + 8) = C + BitVec.ofNat 64 8)
    (hrax : pb ≠ .rax ∧ qb ≠ .rax ∧ cb ≠ .rax)
    (rp : InRegions (s.rd ++ s.wr) P 8) (rp8 : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 8) 8)
    (rq : InRegions (s.rd ++ s.wr) Q 8) (rq8 : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 8) 8)
    (wc : InRegions s.wr C 8) (wc8 : InRegions s.wr (C + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa [.mov .rax (.mem (at_ pb pd)), .alu .xor .rax (.mem (at_ qb qd)), .store (at_ cb cd) .rax,
        .mov .rax (.mem (at_ pb (pd + 8))), .alu .xor .rax (.mem (at_ qb (qd + 8))), .store (at_ cb (cd + 8)) .rax]
        s = some s' ∧
      s'.mem = VG.Proof.CmacAes.X86_64.xor2Mem s.mem C P Q ∧ (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨h₁, h₂, h₃⟩ := hrax
  refine ⟨_, by
    simp only [↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc,
      execAlu, State.load64, State.store64, State.ea, VG.Proof.CmacAes.X86_64.offset_nat, Option.bind_some, Option.map_some,
      gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags,
      h₁, h₂, h₃, hp, hp8, hq, hq8, hc, hc8, rp, rp8, rq, rq8, wc, wc8]
    rfl, ?_⟩
  refine ⟨rfl, ?_, rfl, rfl⟩
  intro r hr; simp [gpr_setReg, hr]

theorem cmp16_ok (s : State) {L : Nat} (h8 : s.gpr .r8 = BitVec.ofNat 64 L) (hL : L ≤ 16) :
    ∃ s', runBlock isa [.alu .cmp .r8 (.imm 16)] s = some s' ∧ s'.zf = some (decide (L = 16)) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some]; rfl,
    ?_⟩
  refine ⟨?_, rfl, rfl, rfl, rfl⟩
  rw [zf_arithFlags, h8, show BitVec.signExtend 64 (16 : BitVec 32) = BitVec.ofNat 64 16 from rfl,
    Offset.ofNat_sub_ofNat_beq (by omega) (by decide)]

/-- The memory after zeroing the block at `c`. -/
def zero2 (m : Mem) (c : Addr) : Mem :=
  (m.writeW c (BitVec.setWidth 64 (0 : BitVec 32))).writeW (c + BitVec.ofNat 64 8) (BitVec.setWidth 64 (0 : BitVec 32))

theorem zero2_bytes (m : Mem) (c : Addr) : Spec.Aes.bytesAt (VG.Proof.CmacAes.X86_64.zero2 m c) c 16 = Spec.Cmac.zeros 16 := by
  rw [VG.Proof.CmacAes.X86_64.zero2, Proof.Cmac.bytesAt_store2, VG.Proof.CmacAes.X86_64.zero_le8, VG.Proof.CmacAes.X86_64.zeros_8_8]

theorem zero_ok (s : State) {C : Addr} {L : Nat} (hc : s.gpr .r9 + BitVec.ofNat 64 2048 = C)
    (hc8 : s.gpr .r9 + BitVec.ofNat 64 2056 = C + BitVec.ofNat 64 8) (h8 : s.gpr .r8 = BitVec.ofNat 64 L)
    (hL : L < 2 ^ 64) (wc : InRegions s.wr C 8) (wc8 : InRegions s.wr (C + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa zero s = some s' ∧ s'.zf = some (decide (L = 0)) ∧ s'.mem = VG.Proof.CmacAes.X86_64.zero2 s.mem C ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceAdd, zero, cOff, runBlock_cons, runStep_some, runBlock_nil, at_, exec,
      readSrc, readSrc32, execAlu, State.store64, State.ea, State.setReg32, VG.Proof.CmacAes.X86_64.offset_nat, Option.bind_some,
      Option.map_some, gpr_setReg, mem_setReg, rd_setReg, wr_setReg, hc, hc8, wc, wc8]
    rfl, ?_⟩
  refine ⟨?_, rfl, ?_, rfl, rfl⟩
  · rw [zf_arithFlags]
    simp only [h8, BitVec.and_self]
    rw [VG.Proof.CmacAes.X86_64.beq_zero hL]
  · intro r hr; simp [gpr_setReg, hr]

theorem pad_ok (s : State) {C : Addr} {L : Nat} (hc : s.gpr .r9 + s.gpr .r8 * BitVec.ofNat 64 1 +
      BitVec.ofInt 64 (cOff : Int) = C + BitVec.ofNat 64 L) (wc : InRegions s.wr (C + BitVec.ofNat 64 L) 1) :
    ∃ s', runBlock isa [.mov32 .rax (.imm 0x80), .store8 { base := .r9, index := some .r8, disp := cOff } .rax] s =
        some s' ∧ s'.mem = s.mem.writeW (C + BitVec.ofNat 64 L) (0x80 : Byte) ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32,
      State.store8, State.ea, State.setReg32, Option.map_some, gpr_setReg, mem_setReg, rd_setReg, wr_setReg,
      ite_true, ite_false, hc, wc]
    rfl, ?_⟩
  refine ⟨rfl, ?_, rfl, rfl⟩
  intro r hr; simp [gpr_setReg, hr]

theorem args_ok (s : State) {D : Addr} (hd : s.gpr .rdx = D)
    (wd : InRegions s.wr (D + BitVec.ofNat 64 0) 8) (wd8 : InRegions s.wr (D + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa [.mov32 .rax (.imm 0), .store (at_ .rdx 0) .rax, .store (at_ .rdx 8) .rax,
        .mov .rcx (.reg .rdx), .mov .rdx (.reg .r9), .alu .add .rdx (.imm (BitVec.ofNat 32 cOff)),
        .mov32 .r8 (.imm 1)] s = some s' ∧
      s'.mem = (s.mem.writeW (D + BitVec.ofNat 64 0) (BitVec.setWidth 64 (0 : BitVec 32))).writeW
        (D + BitVec.ofNat 64 8) (BitVec.setWidth 64 (0 : BitVec 32)) ∧
      s'.gpr .rcx = D ∧ s'.gpr .rdx = s.gpr .r9 + BitVec.ofNat 64 2048 ∧ s'.gpr .r8 = 1 ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .r8 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, BitVec.reduceSignExtend, cOff, runBlock_cons, runStep_some, runBlock_nil, at_, exec,
      readSrc, readSrc32, execAlu, State.store64, State.ea, State.setReg32, VG.Proof.CmacAes.X86_64.offset_nat, Option.bind_some,
      Option.map_some, gpr_setReg, mem_setReg, rd_setReg, wr_setReg, hd, wd, wd8]
    rfl, ?_⟩
  refine ⟨rfl, ?_, ?_, ?_, ?_, rfl, rfl⟩
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · intro r h₁ h₂ h₃ h₄; simp [gpr_setReg, h₁, h₂, h₃, h₄]

open VG.WriteBytes in
/-- The padded last block `Mₙ* ‖ 10ʲ`, from the bytes copied onto zeros. -/
theorem padded_bytes (m : Mem) (C : Addr) (xs : List Byte) (hL : xs.length < 16)
    (hz : Spec.Aes.bytesAt m C 16 = Spec.Cmac.zeros 16) :
    Spec.Aes.bytesAt ((writeBytes m C xs).writeW (C + BitVec.ofNat 64 xs.length) (0x80 : Byte)) C 16 =
      xs ++ [0x80] ++ Spec.Cmac.zeros (16 - xs.length - 1) := by
  refine Proof.Cmac.ext16 (by simp [Spec.Aes.bytesAt]) (by simp [Spec.Cmac.zeros]; omega) fun k hk => ?_
  rw [Proof.Cmac.getD_bytesAt _ _ hk, writeW8_apply]
  have hz' : m (C + BitVec.ofNat 64 k) = 0 := by
    have := congrArg (fun l => l.getD k 0) hz
    rw [Proof.Cmac.getD_bytesAt _ _ hk] at this
    rw [this]; simp only [Spec.Cmac.zeros, List.getD_eq_getElem?_getD, List.getElem?_replicate, hk,
      ite_true, Option.getD_some]
  have hsub : (C + BitVec.ofNat 64 k - C).toNat = k := Mem.sub_ofNat_toNat C (by omega)
  have heq : (C + BitVec.ofNat 64 k = C + BitVec.ofNat 64 xs.length) ↔ k = xs.length := by
    constructor
    · intro h
      have := congrArg (fun a => (a - C).toNat) h
      simp only [Mem.sub_ofNat_toNat C (show k < 2 ^ 64 by omega),
        Mem.sub_ofNat_toNat C (show xs.length < 2 ^ 64 by omega)] at this
      exact this
    · intro h; rw [h]
  rcases Nat.lt_trichotomy k xs.length with h | h | h
  · have hne : ¬ (C + BitVec.ofNat 64 k = C + BitVec.ofNat 64 xs.length) := by rw [heq]; omega
    simp only [hne, ite_false, writeBytes, hsub, h, ite_true]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · have hne : ¬ (C + BitVec.ofNat 64 k = C + BitVec.ofNat 64 xs.length) := by rw [heq]; omega
    simp only [hne, ite_false, writeBytes, hsub, show ¬ k < xs.length by omega, hz']
    obtain ⟨j, hj⟩ : ∃ j, k - xs.length = j + 1 := ⟨k - xs.length - 1, by omega⟩
    rw [List.getD_eq_getElem?_getD, List.append_assoc, List.getElem?_append_right (show xs.length ≤ k by omega),
      hj, List.singleton_append, List.getElem?_cons_succ, Spec.Cmac.zeros, List.getElem?_replicate]
    simp only [show j < 16 - xs.length - 1 by omega, ite_true, Option.getD_some]

end VG.Proof.CmacAes.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.X86_64.FinalizeCorrect`. -/
section

/-!
# AES-CMAC on x86-64: `vg_cmac_aes_finalize` is correct

Before the call, the counter block (at `S + 2048`) holds `Mₙ ⊕ C`, for the
last block `Mₙ` of §6.2 step 4 and the chaining value `C` at `state`, and the
state is zeroed; the call leaves `CIPH_K(C ⊕ Mₙ)` there, the MAC
(`macFull_split`).
-/

namespace VG.Proof.CmacAes.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.CmacAes.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- The precondition, by name: the key (schedule and subkeys) `W`, the state
`St`, the last bytes `P` (`L` of them), the scratch buffer `S` and the
rounds `R`. -/
structure FPre (s₀ : State) (W St P S : Addr) (L R : Nat) : Prop where
  rdi : s₀.gpr .rdi = W
  rdx : s₀.gpr .rdx = St
  rcx : s₀.gpr .rcx = P
  r8 : (s₀.gpr .r8).toNat = L
  r9 : s₀.gpr .r9 = S
  rsi : (s₀.gpr .rsi).toNat = R
  rd : s₀.rd = [⟨W, 272⟩, ⟨P, L⟩]
  wr : s₀.wr = [⟨St, 16⟩, ⟨S, 2176⟩]
  key_st : (⟨W, 272⟩ : Region).Disjoint ⟨St, 16⟩
  key_scr : (⟨W, 272⟩ : Region).Disjoint ⟨S, 2176⟩
  last_st : (⟨P, L⟩ : Region).Disjoint ⟨St, 16⟩
  last_scr : (⟨P, L⟩ : Region).Disjoint ⟨S, 2176⟩
  st_scr : (⟨St, 16⟩ : Region).Disjoint ⟨S, 2176⟩
  ret_st : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨St, 16⟩
  ret_scr : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨S, 2176⟩
  stk_key : (below (s₀.gpr .rsp) 8).Disjoint ⟨W, 272⟩
  stk_last : (below (s₀.gpr .rsp) 8).Disjoint ⟨P, L⟩
  stk_st : (below (s₀.gpr .rsp) 8).Disjoint ⟨St, 16⟩
  stk_scr : (below (s₀.gpr .rsp) 8).Disjoint ⟨S, 2176⟩
  key_wrap : W.toNat + 272 ≤ 2 ^ 64
  st_wrap : St.toNat + 16 ≤ 2 ^ 64
  last_wrap : P.toNat + L ≤ 2 ^ 64
  scr_wrap : S.toNat + 2176 ≤ 2 ^ 64
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  len : L ≤ 16

theorem FPre.of {s₀ : State} (h : finalizeX86_64.pre s₀) :
    VG.Proof.CmacAes.X86_64.FPre s₀ (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .r9) (s₀.gpr .r8).toNat (s₀.gpr .rsi).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s⟩ := h
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s⟩

/-- The last block `Mₙ` (§6.2 step 4), from the key and the last bytes in `m`. -/
abbrev mn (m : Mem) (W P : Addr) (L : Nat) : List Byte :=
  Spec.Cmac.lastBlock 16 (Spec.Aes.bytesAt m (W + BitVec.ofNat 64 240) 16)
    (Spec.Aes.bytesAt m (W + BitVec.ofNat 64 256) 16) (Spec.Aes.bytesAt m P L)

/-- What the branch on the length leaves: `Mₙ` in the counter block. -/
structure BPost (s₀ : State) (W St P S : Addr) (L : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = W
  rdx : s.gpr .rdx = St
  r9 : s.gpr .r9 = S
  rsi : s.gpr .rsi = s₀.gpr .rsi
  saved : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨S + BitVec.ofNat 64 2048, 16⟩] s₀.mem s.mem
  blk : Spec.Aes.bytesAt s.mem (S + BitVec.ofNat 64 2048) 16 = VG.Proof.CmacAes.X86_64.mn s₀.mem W P L

section
variable {s₀ : State} {W St P S : Addr} {L R : Nat} (hp : VG.Proof.CmacAes.X86_64.FPre s₀ W St P S L R)
include hp

theorem FPre.inScr {d n : Nat} (h : d + n ≤ 2176) : InRegions s₀.wr (S + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact VG.Proof.CmacAes.X86_64.in_rw (r := ⟨S, 2176⟩) (by simp) (Offset.contains_base _ h (by have := hp.scr_wrap; omega))

theorem FPre.inKey {d n : Nat} (h : d + n ≤ 272) : InRegions (s₀.rd ++ s₀.wr) (W + BitVec.ofNat 64 d) n := by
  rw [hp.rd]; exact VG.Proof.CmacAes.X86_64.in_rw (r := ⟨W, 272⟩) (by simp) (Offset.contains_base _ h (by have := hp.key_wrap; omega))

theorem FPre.inLast {d n : Nat} (h : d + n ≤ L) : InRegions (s₀.rd ++ s₀.wr) (P + BitVec.ofNat 64 d) n := by
  rw [hp.rd]; exact VG.Proof.CmacAes.X86_64.in_rw (r := ⟨P, L⟩) (by simp) (Offset.contains_base _ h (by have := hp.len; omega))

end

theorem FPre.scrD {S : Addr} {d n : Nat} (h : d + n ≤ 2176) : Region.Sub ⟨S + BitVec.ofNat 64 d, n⟩ ⟨S, 2176⟩ :=
  Offset.sub_base _ h

theorem wr_in {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n := by
  obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem full_wp {s₀ : State} {W St P S : Addr} {L R : Nat} (hp : VG.Proof.CmacAes.X86_64.FPre s₀ W St P S L R) (hL : L = 16)
    {s : State} (hg : s.gpr = s₀.gpr) (hm : s.mem = s₀.mem) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block full) s (VG.Proof.CmacAes.X86_64.BPost s₀ W St P S L) := by
  subst hL
  have e : full = [.mov .rax (.mem (at_ .rcx 0)), .alu .xor .rax (.mem (at_ .rdi 240)), .store (at_ .r9 2048) .rax,
      .mov .rax (.mem (at_ .rcx (0 + 8))), .alu .xor .rax (.mem (at_ .rdi (240 + 8))),
      .store (at_ .r9 (2048 + 8)) .rax] := rfl
  have sw := hp.scr_wrap
  have kw := hp.key_wrap
  obtain ⟨s', run, mem, g, rd, wr⟩ := VG.Proof.CmacAes.X86_64.xor2_ok s .rcx .rdi .r9 0 240 2048
    (P := P) (Q := W + BitVec.ofNat 64 240) (C := S + BitVec.ofNat 64 2048)
    (by rw [hg, hp.rcx, VG.Proof.CmacAes.X86_64.k0]) (by rw [hg, hp.rcx])
    (by rw [hg, hp.rdi]) (by rw [hg, hp.rdi, Offset.add_add])
    (by rw [hg, hp.r9]) (by rw [hg, hp.r9, Offset.add_add])
    ⟨by decide, by decide, by decide⟩
    (by rw [hrd, hwr]; simpa using hp.inLast (d := 0) (n := 8) (by decide))
    (by rw [hrd, hwr]; exact hp.inLast (d := 8) (n := 8) (by decide))
    (by rw [hrd, hwr]; exact hp.inKey (d := 240) (n := 8) (by decide))
    (by rw [hrd, hwr, Offset.add_add]; exact hp.inKey (d := 248) (n := 8) (by decide))
    (by rw [hwr]; exact hp.inScr (d := 2048) (n := 8) (by decide))
    (by rw [hwr, Offset.add_add]; exact hp.inScr (d := 2056) (n := 8) (by decide))
  rw [e]
  refine WP.of_runBlock ⟨s', run, ?_⟩
  have gg (r : Reg) (hr : r ≠ .rax) : s'.gpr r = s₀.gpr r := by rw [g r hr, hg]
  refine ⟨by rw [gg _ (by decide), hp.rdi], by rw [gg _ (by decide), hp.rdx], by rw [gg _ (by decide), hp.r9],
    gg _ (by decide), fun r hr => gg r (by rintro rfl; simp [calleeSaved] at hr), by rw [rd, hrd],
    by rw [wr, hwr], by rw [mem, hm]; exact VG.Proof.CmacAes.X86_64.xor2Mem_frame _ _ _ _, ?_⟩
  rw [mem, hm, VG.Proof.CmacAes.X86_64.xor2Mem_bytes]
  · simp only [VG.Proof.CmacAes.X86_64.mn, Spec.Cmac.lastBlock, Proof.Cmac.bytesAt_length, ite_true]
    exact VG.Proof.CmacAes.X86_64.xor_comm _ _
  · exact (hp.last_scr.symm.sub_left (FPre.scrD (d := 2048) (n := 8) (by decide))).sub_right
      (Offset.sub_base P (d := 8) (n := 8) (k := 16) (by decide))
  · rw [Offset.add_add]
    exact (hp.key_scr.symm.sub_left (FPre.scrD (d := 2048) (n := 8) (by decide))).sub_right
      (Offset.sub_base W (d := 248) (n := 8) (k := 272) (by decide))

open VG.WriteBytes in
theorem partial_wp {s₀ : State} {W St P S : Addr} {L R : Nat} (hp : VG.Proof.CmacAes.X86_64.FPre s₀ W St P S L R) (hL : L < 16)
    {s : State} (hg : s.gpr = s₀.gpr) (hm : s.mem = s₀.mem) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa partialBlock s (VG.Proof.CmacAes.X86_64.BPost s₀ W St P S L) := by
  have sw := hp.scr_wrap
  have kw := hp.key_wrap
  have h8 : s.gpr .r8 = BitVec.ofNat 64 L := by
    rw [hg, ← hp.r8]; apply BitVec.eq_of_toNat_eq; simp
  obtain ⟨C, hC⟩ : ∃ C, S + BitVec.ofNat 64 2048 = C := ⟨_, rfl⟩
  have hc : s.gpr .r9 + BitVec.ofNat 64 2048 = C := by rw [hg, hp.r9, hC]
  have hc8 : s.gpr .r9 + BitVec.ofNat 64 2056 = C + BitVec.ofNat 64 8 := by rw [hg, hp.r9, ← hC, Offset.add_add]
  have dPC : (⟨P, L⟩ : Region).Disjoint ⟨C, 16⟩ := by rw [← hC]; exact hp.last_scr.sub_right (FPre.scrD (by decide))
  have dKC (d n : Nat) (h : d + n ≤ 272) : (⟨W + BitVec.ofNat 64 d, n⟩ : Region).Disjoint ⟨C, 16⟩ := by
    rw [← hC]; exact (hp.key_scr.sub_left (Offset.sub_base _ h)).sub_right (FPre.scrD (by decide))
  -- Zero the block.
  obtain ⟨s₁, run₁, zf₁, mem₁, g₁, rd₁, wr₁⟩ := VG.Proof.CmacAes.X86_64.zero_ok s hc hc8 h8 (by omega)
    (by rw [hwr, ← hC]; exact hp.inScr (d := 2048) (n := 8) (by decide))
    (by rw [hwr, ← hC, Offset.add_add]; exact hp.inScr (d := 2056) (n := 8) (by decide))
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have zf : s₁.mem = VG.Proof.CmacAes.X86_64.zero2 s₀.mem C := by rw [mem₁, hm]
  have fz : Frame [⟨C, 16⟩] s₀.mem (VG.Proof.CmacAes.X86_64.zero2 s₀.mem C) := VG.Proof.CmacAes.X86_64.frame_store2 _ _ _
  have lastZ : Spec.Aes.bytesAt (VG.Proof.CmacAes.X86_64.zero2 s₀.mem C) P L = Spec.Aes.bytesAt s₀.mem P L :=
    VG.Proof.CmacAes.X86_64.bytesAt_frame fz (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dPC) (by omega)
  -- Copy the last bytes.
  refine WP.seq (WP.mono (Q := fun (s₂ : State) => s₂.mem = writeBytes (VG.Proof.CmacAes.X86_64.zero2 s₀.mem C) C (Spec.Aes.bytesAt s₀.mem P L) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → s₂.gpr r = s₀.gpr r) ∧ s₂.rd = s₀.rd ∧ s₂.wr = s₀.wr) ?_ fun s₂ h₂ => ?_)
  · by_cases hL0 : L = 0
    · subst hL0
      refine WP.ite true (by show s₁.zf = _; rw [zf₁]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      refine ⟨by rw [zf]; simp [Spec.Aes.bytesAt, writeBytes_nil], fun r h₁ _ => by rw [g₁ r h₁, hg],
        by rw [rd₁, hrd], by rw [wr₁, hwr]⟩
    · refine WP.ite false (by show s₁.zf = _; rw [zf₁]; simp [hL0]) (fun h => by cases h) fun _ => ?_
      refine WP.mono (VG.Proof.CmacAes.X86_64.copy_ok s₁ (by omega) hL (by rw [g₁ _ (by decide), hg, hp.rcx])
        (by rw [g₁ _ (by decide)]; exact hc) (by rw [g₁ _ (by decide)]; exact h8)
        (fun i hi => by rw [rd₁, wr₁, hrd, hwr]; exact hp.inLast (d := i) (n := 1) (by omega))
        (fun i hi => by
          rw [wr₁, hwr, ← hC, Offset.add_add]; exact hp.inScr (d := 2048 + i) (n := 1) (by omega)) dPC) ?_
      rintro s₂ ⟨m₂, g₂, rd₂, wr₂⟩
      refine ⟨by rw [m₂, zf, lastZ], fun r h₁ h₂ => by rw [g₂ r h₁ h₂, g₁ r h₁, hg], by rw [rd₂, rd₁, hrd],
        by rw [wr₂, wr₁, hwr]⟩
  · obtain ⟨m₂, g₂, rd₂, wr₂⟩ := h₂
    have e : padK2 = [.mov32 .rax (.imm 0x80), .store8 { base := .r9, index := some .r8, disp := cOff } .rax] ++
        [.mov .rax (.mem (at_ .r9 2048)), .alu .xor .rax (.mem (at_ .rdi 256)), .store (at_ .r9 2048) .rax,
          .mov .rax (.mem (at_ .r9 (2048 + 8))), .alu .xor .rax (.mem (at_ .rdi (256 + 8))),
          .store (at_ .r9 (2048 + 8)) .rax] := rfl
    rw [e, WP.block_append_iff]
    have r9₂ : s₂.gpr .r9 = S := by rw [g₂ _ (by decide) (by decide), hp.r9]
    have r8₂ : s₂.gpr .r8 = BitVec.ofNat 64 L := by rw [g₂ _ (by decide) (by decide), ← hg]; exact h8
    obtain ⟨s₃, run₃, m₃, g₃, rd₃, wr₃⟩ := VG.Proof.CmacAes.X86_64.pad_ok s₂ (C := C) (L := L)
      (by rw [r9₂, r8₂, BitVec.mul_one, VG.Proof.CmacAes.X86_64.offset_nat, ← hC, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 L),
        ← BitVec.add_assoc]; rfl)
      (by rw [wr₂, ← hC, Offset.add_add]; exact hp.inScr (d := 2048 + L) (n := 1) (by omega))
    refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
    have r9₃ : s₃.gpr .r9 = S := by rw [g₃ _ (by decide), r9₂]
    have rdi₃ : s₃.gpr .rdi = W := by rw [g₃ _ (by decide), g₂ _ (by decide) (by decide), hp.rdi]
    obtain ⟨s₄, run₄, m₄, g₄, rd₄, wr₄⟩ := VG.Proof.CmacAes.X86_64.xor2_ok s₃ .r9 .rdi .r9 2048 256 2048
      (P := C) (Q := W + BitVec.ofNat 64 256) (C := C)
      (by rw [r9₃, hC]) (by rw [r9₃, ← hC, Offset.add_add]) (by rw [rdi₃]) (by rw [rdi₃, Offset.add_add])
      (by rw [r9₃, hC]) (by rw [r9₃, ← hC, Offset.add_add]) ⟨by decide, by decide, by decide⟩
      (by rw [rd₃, wr₃, rd₂, wr₂, ← hC]; exact VG.Proof.CmacAes.X86_64.wr_in (hp.inScr (d := 2048) (n := 8) (by decide)))
      (by rw [rd₃, wr₃, rd₂, wr₂, ← hC, Offset.add_add]; exact VG.Proof.CmacAes.X86_64.wr_in (hp.inScr (d := 2056) (n := 8) (by decide)))
      (by rw [rd₃, wr₃, rd₂, wr₂]; exact hp.inKey (d := 256) (n := 8) (by decide))
      (by rw [rd₃, wr₃, rd₂, wr₂, Offset.add_add]; exact hp.inKey (d := 264) (n := 8) (by decide))
      (by rw [wr₃, wr₂, ← hC]; exact hp.inScr (d := 2048) (n := 8) (by decide))
      (by rw [wr₃, wr₂, ← hC, Offset.add_add]; exact hp.inScr (d := 2056) (n := 8) (by decide))
    refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
    have gg (r : Reg) (h₁ : r ≠ .rax) (h₂ : r ≠ .r10) : s₄.gpr r = s₀.gpr r := by rw [g₄ r h₁, g₃ r h₁, g₂ r h₁ h₂]
    have hlen : (Spec.Aes.bytesAt s₀.mem P L).length = L := Proof.Cmac.bytesAt_length _ _ _
    have fW : Frame [⟨C, 16⟩] (writeBytes (VG.Proof.CmacAes.X86_64.zero2 s₀.mem C) C (Spec.Aes.bytesAt s₀.mem P L)) s₃.mem := by
      rw [m₃, m₂]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
    have fB : Frame [⟨C, 16⟩] (VG.Proof.CmacAes.X86_64.zero2 s₀.mem C) (writeBytes (VG.Proof.CmacAes.X86_64.zero2 s₀.mem C) C (Spec.Aes.bytesAt s₀.mem P L)) :=
      writeBytes_frame _ _ _ (by
        rw [hlen]; simpa using Offset.contains_base C (d := 0) (n := L) (k := 16) (by omega) (by decide))
    have f₃ : Frame [⟨C, 16⟩] s₀.mem s₃.mem := (fz.trans fB).trans fW
    have k2 : Spec.Aes.bytesAt s₃.mem (W + BitVec.ofNat 64 256) 16 = Spec.Aes.bytesAt s₀.mem (W + BitVec.ofNat 64 256) 16 :=
      VG.Proof.CmacAes.X86_64.bytesAt_frame' f₃ fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dKC 256 16 (by decide)
    have pad : Spec.Aes.bytesAt s₃.mem C 16 =
        Spec.Aes.bytesAt s₀.mem P L ++ [0x80] ++ Spec.Cmac.zeros (16 - L - 1) := by
      have := VG.Proof.CmacAes.X86_64.padded_bytes (VG.Proof.CmacAes.X86_64.zero2 s₀.mem C) C (Spec.Aes.bytesAt s₀.mem P L) (by rw [hlen]; exact hL) (VG.Proof.CmacAes.X86_64.zero2_bytes _ _)
      rw [hlen] at this
      rw [m₃, m₂]; exact this
    refine ⟨by rw [gg _ (by decide) (by decide), hp.rdi], by rw [gg _ (by decide) (by decide), hp.rdx],
      by rw [gg _ (by decide) (by decide), hp.r9], gg _ (by decide) (by decide),
      fun r hr => gg r (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr),
      by rw [rd₄, rd₃, rd₂], by rw [wr₄, wr₃, wr₂], ?_, ?_⟩
    · rw [m₄, hC]; exact f₃.trans (VG.Proof.CmacAes.X86_64.xor2Mem_frame _ _ _ _)
    · rw [m₄, hC, VG.Proof.CmacAes.X86_64.xor2Mem_bytes, pad, k2]
      · simp only [VG.Proof.CmacAes.X86_64.mn, Spec.Cmac.lastBlock, hlen, show L ≠ 16 by omega, ite_false]
        exact VG.Proof.CmacAes.X86_64.xor_comm _ _
      · simpa using Offset.disjoint C (d := 0) (n := 8) (e := 8) (k := 8) (by decide) (by decide) (by decide)
      · rw [Offset.add_add]
        exact (dKC 264 8 (by decide)).symm.sub_left (Region.sub_prefix (by decide))

/-! ## Up to the call -/

/-- What the code before the call leaves. -/
structure FMid (s₀ : State) (W St P S : Addr) (L R : Nat) (s : State) : Prop where
  pre : VG.Proof.CmacAes.X86_64.CallPre s W (S + BitVec.ofNat 64 2048) St S R
  blk : Spec.Aes.bytesAt s.mem (S + BitVec.ofNat 64 2048) 16 =
    Spec.Cmac.xor (VG.Proof.CmacAes.X86_64.mn s₀.mem W P L) (Spec.Aes.bytesAt s₀.mem St 16)
  frame : Frame [⟨S + BitVec.ofNat 64 2048, 16⟩, ⟨St, 16⟩] s₀.mem s.mem
  saved : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r

theorem finArgs_wp {s₀ : State} {W St P S : Addr} {L R : Nat} (hp : VG.Proof.CmacAes.X86_64.FPre s₀ W St P S L R) {s : State}
    (h : VG.Proof.CmacAes.X86_64.BPost s₀ W St P S L s) : WP isa (.block finArgs) s (VG.Proof.CmacAes.X86_64.FMid s₀ W St P S L R) := by
  have sw := hp.scr_wrap
  have tw := hp.st_wrap
  have e : finArgs = [.mov .rax (.mem (at_ .r9 2048)), .alu .xor .rax (.mem (at_ .rdx 0)), .store (at_ .r9 2048) .rax,
        .mov .rax (.mem (at_ .r9 (2048 + 8))), .alu .xor .rax (.mem (at_ .rdx (0 + 8))),
        .store (at_ .r9 (2048 + 8)) .rax] ++
      [.mov32 .rax (.imm 0), .store (at_ .rdx 0) .rax, .store (at_ .rdx 8) .rax,
        .mov .rcx (.reg .rdx), .mov .rdx (.reg .r9), .alu .add .rdx (.imm (BitVec.ofNat 32 cOff)),
        .mov32 .r8 (.imm 1)] := rfl
  rw [e, WP.block_append_iff]
  have hRegs : s.rd ++ s.wr = [⟨W, 272⟩, ⟨P, L⟩, ⟨St, 16⟩, ⟨S, 2176⟩] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have inC (d : Nat) (hd : d + 8 ≤ 2176) : InRegions s.wr (S + BitVec.ofNat 64 d) 8 := by
    rw [h.wr]; exact hp.inScr (by omega)
  have inSt (d : Nat) (hd : d + 8 ≤ 16) : InRegions s.wr (St + BitVec.ofNat 64 d) 8 := by
    rw [h.wr, hp.wr]; exact VG.Proof.CmacAes.X86_64.in_rw (r := ⟨St, 16⟩) (by simp) (Offset.contains_base _ hd (by omega))
  obtain ⟨s₁, run₁, m₁, g₁, rd₁, wr₁⟩ := VG.Proof.CmacAes.X86_64.xor2_ok s .r9 .rdx .r9 2048 0 2048
    (P := S + BitVec.ofNat 64 2048) (Q := St) (C := S + BitVec.ofNat 64 2048)
    (by rw [h.r9]) (by rw [h.r9, Offset.add_add]) (by rw [h.rdx, VG.Proof.CmacAes.X86_64.k0]) (by rw [h.rdx])
    (by rw [h.r9]) (by rw [h.r9, Offset.add_add]) ⟨by decide, by decide, by decide⟩
    (VG.Proof.CmacAes.X86_64.wr_in (inC 2048 (by decide))) (by rw [Offset.add_add]; exact VG.Proof.CmacAes.X86_64.wr_in (inC 2056 (by decide)))
    (by simpa using VG.Proof.CmacAes.X86_64.wr_in (inSt 0 (by decide))) (VG.Proof.CmacAes.X86_64.wr_in (inSt 8 (by decide)))
    (inC 2048 (by decide)) (by rw [Offset.add_add]; exact inC 2056 (by decide))
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain ⟨s₂, run₂, m₂, rcx₂, rdx₂, r8₂, g₂, rd₂, wr₂⟩ := VG.Proof.CmacAes.X86_64.args_ok s₁ (D := St)
    (by rw [g₁ _ (by decide), h.rdx]) (by rw [wr₁]; exact inSt 0 (by decide)) (by rw [wr₁]; exact inSt 8 (by decide))
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have g (r : Reg) (h₁ : r ≠ .rax) (h₂ : r ≠ .rcx) (h₃ : r ≠ .rdx) (h₄ : r ≠ .r8) : s₂.gpr r = s.gpr r := by
    rw [g₂ r h₁ h₂ h₃ h₄, g₁ r h₁]
  have rsp₂ : s₂.gpr .rsp = s₀.gpr .rsp := by
    rw [g _ (by decide) (by decide) (by decide) (by decide), h.saved _ (by simp [calleeSaved])]
  have dCSt : (⟨S + BitVec.ofNat 64 2048, 16⟩ : Region).Disjoint ⟨St, 16⟩ :=
    hp.st_scr.symm.sub_left (FPre.scrD (by decide))
  have fA : Frame [⟨St, 16⟩] s₁.mem s₂.mem := by
    rw [m₂, VG.Proof.CmacAes.X86_64.k0]; exact VG.Proof.CmacAes.X86_64.frame_store2 _ _ _
  have stS : Spec.Aes.bytesAt s.mem St 16 = Spec.Aes.bytesAt s₀.mem St 16 :=
    VG.Proof.CmacAes.X86_64.bytesAt_frame' h.frame fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dCSt.symm
  have hR := hp.rounds
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact
    { rdi := by rw [g _ (by decide) (by decide) (by decide) (by decide), h.rdi]
      rsi := by
        rw [g _ (by decide) (by decide) (by decide) (by decide), h.rsi]
        apply BitVec.eq_of_toNat_eq; simp [hp.rsi]; omega
      rdx := by rw [rdx₂, g₁ _ (by decide), h.r9]
      rcx := rcx₂
      r8 := r8₂
      r9 := by rw [g _ (by decide) (by decide) (by decide) (by decide), h.r9]
      rounds := hR
      wc := (hp.key_scr.sub_left (Region.sub_prefix (by decide))).sub_right (FPre.scrD (by decide))
      wd := hp.key_st.sub_left (Region.sub_prefix (by decide))
      ws := (hp.key_scr.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
      cd := dCSt
      cs := Offset.disjoint_base _ (by decide) (by have := hp.scr_wrap; omega)
      ds := hp.st_scr.sub_right (Region.sub_prefix (by decide))
      stkW := by rw [rsp₂]; exact hp.stk_key.sub_right (Region.sub_prefix (by decide))
      stkC := by rw [rsp₂]; exact hp.stk_scr.sub_right (FPre.scrD (by decide))
      stkD := by rw [rsp₂]; exact hp.stk_st
      stkS := by rw [rsp₂]; exact hp.stk_scr.sub_right (Region.sub_prefix (by decide))
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
      zero := by rw [m₂, VG.Proof.CmacAes.X86_64.k0, Proof.Cmac.bytesAt_store2, VG.Proof.CmacAes.X86_64.zero_le8, VG.Proof.CmacAes.X86_64.zeros_8_8] }
  · rw [VG.Proof.CmacAes.X86_64.bytesAt_frame' fA (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dCSt), m₁,
      VG.Proof.CmacAes.X86_64.xor2Mem_bytes, h.blk, stS]
    · simpa using Offset.disjoint (S + BitVec.ofNat 64 2048) (d := 0) (n := 8) (e := 8) (k := 8) (by decide)
        (by decide) (by decide)
    · exact (dCSt.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base _ (by decide))
  · refine (h.frame.trans (m₁ ▸ VG.Proof.CmacAes.X86_64.xor2Mem_frame _ _ _ _)).mono (by simp) |>.trans (fA.mono (by simp))
  · intro r hr
    rw [g r (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)
      (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr), h.saved r hr]

theorem finPre_wp {s₀ : State} {W St P S : Addr} {L R : Nat} (hp : VG.Proof.CmacAes.X86_64.FPre s₀ W St P S L R) :
    WP isa finPre s₀ (VG.Proof.CmacAes.X86_64.FMid s₀ W St P S L R) := by
  have h8 : s₀.gpr .r8 = BitVec.ofNat 64 L := by rw [← hp.r8]; apply BitVec.eq_of_toNat_eq; simp
  obtain ⟨s₁, run₁, zf₁, g₁, m₁, rd₁, wr₁⟩ := VG.Proof.CmacAes.X86_64.cmp16_ok s₀ h8 hp.len
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (Q := VG.Proof.CmacAes.X86_64.BPost s₀ W St P S L) ?_ fun _ h => VG.Proof.CmacAes.X86_64.finArgs_wp hp h)
  by_cases hL : L = 16
  · exact WP.ite true (by show s₁.zf = _; rw [zf₁]; simp [hL]) (fun _ => VG.Proof.CmacAes.X86_64.full_wp hp hL g₁ m₁ rd₁ wr₁)
      (fun h => by cases h)
  · exact WP.ite false (by show s₁.zf = _; rw [zf₁]; simp [hL]) (fun h => by cases h)
      (fun _ => VG.Proof.CmacAes.X86_64.partial_wp hp (by have := hp.len; omega) g₁ m₁ rd₁ wr₁)

theorem k1k2 {m : Mem} {W : Addr} {k1 k2 : List Byte} (h1 : k1.length = 16)
    (h : Spec.Aes.bytesAt m (W + BitVec.ofNat 64 240) 32 = k1 ++ k2) :
    Spec.Aes.bytesAt m (W + BitVec.ofNat 64 240) 16 = k1 ∧ Spec.Aes.bytesAt m (W + BitVec.ofNat 64 256) 16 = k2 := by
  rw [VG.Proof.CmacAes.X86_64.bytesAt_32, Offset.add_add] at h
  exact List.append_inj h (by rw [Proof.Cmac.bytesAt_length, h1])

theorem finalize_wp (v : Ctr32Impl) {s₀ : State} (h0 : finalizeX86_64.pre s₀) :
    WP isa (finalize v.callee) s₀ fun s' => gprPreserved s₀ s' ∧ finalizeX86_64.post s₀ s' := by
  have hp := FPre.of h0
  generalize s₀.gpr .rdi = W at hp
  generalize s₀.gpr .rdx = St at hp
  generalize s₀.gpr .rcx = P at hp
  generalize s₀.gpr .r9 = S at hp
  generalize (s₀.gpr .r8).toNat = L at hp
  generalize (s₀.gpr .rsi).toNat = R at hp
  have hR := hp.rounds
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with h | h | h <;> omega
  refine WP.seq (WP.mono (VG.Proof.CmacAes.X86_64.finPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.mono (VG.Proof.CmacAes.X86_64.ctr_call v h₁.pre) fun s₂ h₂ => ?_
  have rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := h₁.saved _ (by simp [calleeSaved])
  -- The key and the frame.
  have big : Frame [⟨St, 16⟩, ⟨S, 2176⟩, below (s₀.gpr .rsp) 8] s₀.mem s₂.mem := by
    refine (h₁.frame.sub fun r hr => ?_).trans (h₂.frame.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨S, 2176⟩, by simp, FPre.scrD (by decide)⟩
      · exact ⟨⟨St, 16⟩, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨S, 2176⟩, by simp, FPre.scrD (by decide)⟩
      · exact ⟨⟨St, 16⟩, by simp, fun _ h => h⟩
      · exact ⟨⟨S, 2176⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨below (s₀.gpr .rsp) 8, by simp, by rw [rsp₁]; exact fun _ h => h⟩
  have sch : Spec.Aes.bytesAt s₁.mem W (16 * (R + 1)) = Spec.Aes.bytesAt s₀.mem W (16 * (R + 1)) :=
    VG.Proof.CmacAes.X86_64.bytesAt_frame h₁.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hp.key_scr.sub_left (Region.sub_prefix (by omega))).sub_right (FPre.scrD (by decide))
      · exact hp.key_st.sub_left (Region.sub_prefix (by omega))) (by omega)
  refine ⟨⟨fun r hr => by rw [h₂.saved r hr, h₁.saved r hr], ?_⟩, ?_⟩
  · refine big.readW (r := ⟨s₀.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.ret_st
    · exact hp.ret_scr
    · exact Offset.base_disjoint_below _ (by decide)
  · intro hk msg hm hne hst
    rw [hp.rdi, hp.rsi] at hk hst ⊢
    rw [hp.rdx] at hst ⊢
    rw [hp.r8] at hne
    rw [hp.rcx, hp.r8]
    obtain ⟨e1, e2⟩ := VG.Proof.CmacAes.X86_64.k1k2 (Proof.Cmac.subkeys_aes_length _ _) hk
    rw [h₂.out, sch, h₁.blk, VG.Proof.CmacAes.X86_64.mn, e1, e2, hst,
      Proof.Cmac.macFull_split _ hm (by rw [Proof.Cmac.bytesAt_length]; exact hp.len)
        (by rw [Proof.Cmac.bytesAt_length]; exact hne), VG.Proof.CmacAes.X86_64.xor_comm]

end VG.Proof.CmacAes.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.X86_64.Verified`. -/
section

section

/-!
# AES-CMAC on x86-64: `vg_cmac_aes_update` is constant time

Two runs from states that agree on the public arguments are related piece by
piece (`RelCT`): the taint analysis covers the code between the calls, from
the registers the correctness proof pins to the public arguments (`LInv`), and
each call of `vg_aes_ctr32` is constant time by its own proof (`ctr_rel`).
-/

namespace VG.Proof.CmacAes.X86_64

open VG VG.X86_64 VG.Impl.CmacAes.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)

section
variable {s₀ s₀' : State} (hq : updateX86_64.pub s₀ s₀')
include hq

theorem pub_W : VG.Proof.CmacAes.X86_64.W s₀ = VG.Proof.CmacAes.X86_64.W s₀' := hq.1
theorem pub_rsi : s₀.gpr .rsi = s₀'.gpr .rsi := hq.2.1
theorem pub_R : VG.Proof.CmacAes.X86_64.R s₀ = VG.Proof.CmacAes.X86_64.R s₀' := by rw [VG.Proof.CmacAes.X86_64.R, VG.Proof.CmacAes.X86_64.R, VG.Proof.CmacAes.X86_64.pub_rsi hq]
theorem pub_St : VG.Proof.CmacAes.X86_64.St s₀ = VG.Proof.CmacAes.X86_64.St s₀' := hq.2.2.1
theorem pub_Dp : VG.Proof.CmacAes.X86_64.Dp s₀ = VG.Proof.CmacAes.X86_64.Dp s₀' := hq.2.2.2.1
theorem pub_N : VG.Proof.CmacAes.X86_64.N s₀ = VG.Proof.CmacAes.X86_64.N s₀' := by rw [VG.Proof.CmacAes.X86_64.N, VG.Proof.CmacAes.X86_64.N, hq.2.2.2.2.1]
theorem pub_S : VG.Proof.CmacAes.X86_64.S s₀ = VG.Proof.CmacAes.X86_64.S s₀' := hq.2.2.2.2.2.1
theorem pub_rsp : s₀.gpr .rsp = s₀'.gpr .rsp := hq.2.2.2.2.2.2

/-- The registers the invariant pins agree in both runs. -/
theorem LInv.agree {k : Nat} {s₁ s₂ : State} (h₁ : VG.Proof.CmacAes.X86_64.LInv s₀ k s₁) (h₂ : VG.Proof.CmacAes.X86_64.LInv s₀' k s₂) :
    ∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp], s₁.gpr r = s₂.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h₁.rbx, h₂.rbx, VG.Proof.CmacAes.X86_64.pub_W hq]
  · rw [h₁.rbp, h₂.rbp, VG.Proof.CmacAes.X86_64.pub_rsi hq]
  · rw [h₁.r12, h₂.r12, VG.Proof.CmacAes.X86_64.pub_St hq]
  · rw [h₁.r13, h₂.r13, VG.Proof.CmacAes.X86_64.pub_Dp hq]
  · rw [h₁.r14, h₂.r14, VG.Proof.CmacAes.X86_64.pub_N hq]
  · rw [h₁.r15, h₂.r15, VG.Proof.CmacAes.X86_64.pub_S hq]
  · rw [h₁.rsp, h₂.rsp, VG.Proof.CmacAes.X86_64.pub_rsp hq]

end

/-! ## One block -/

/-- What is known between the code before the call and the call. -/
structure Mid (s₀ : State) (k : Nat) (s : State) : Prop where
  pre : VG.Proof.CmacAes.X86_64.CallPre s (VG.Proof.CmacAes.X86_64.W s₀) (VG.Proof.CmacAes.X86_64.S s₀ + BitVec.ofNat 64 2048) (VG.Proof.CmacAes.X86_64.St s₀) (VG.Proof.CmacAes.X86_64.S s₀) (VG.Proof.CmacAes.X86_64.R s₀)
  r13 : s.gpr .r13 = VG.Proof.CmacAes.X86_64.Dp s₀ + BitVec.ofNat 64 (16 * k)
  r14 : s.gpr .r14 = BitVec.ofNat 64 (VG.Proof.CmacAes.X86_64.N s₀ - k)
  rsp : s.gpr .rsp = s₀.gpr .rsp

theorem bodyMid_wp {s₀ : State} (hp : VG.Proof.CmacAes.X86_64.UPre s₀) {k : Nat} (hk : k < VG.Proof.CmacAes.X86_64.N s₀) {s : State} (h : VG.Proof.CmacAes.X86_64.LInv s₀ k s) :
    WP isa (.block (chainIn ++ updArgs)) s (VG.Proof.CmacAes.X86_64.Mid s₀ k) :=
  WP.mono (VG.Proof.CmacAes.X86_64.bodyA_wp hp hk h) fun _ hb =>
    ⟨hb.pre, by rw [hb.saved .r13 (by simp [calleeSaved]), h.r13],
      by rw [hb.saved .r14 (by simp [calleeSaved]), h.r14], by rw [hb.saved .rsp (by simp [calleeSaved]), h.rsp]⟩

/-- What is known after the call. -/
structure After (s₀ : State) (k : Nat) (s : State) : Prop where
  r13 : s.gpr .r13 = VG.Proof.CmacAes.X86_64.Dp s₀ + BitVec.ofNat 64 (16 * k)
  r14 : s.gpr .r14 = BitVec.ofNat 64 (VG.Proof.CmacAes.X86_64.N s₀ - k)

theorem body_ct (v : Ctr32Impl) {s₀ s₀' : State} (hp : VG.Proof.CmacAes.X86_64.UPre s₀) (hp' : VG.Proof.CmacAes.X86_64.UPre s₀')
    (hq : updateX86_64.pub s₀ s₀') (k : Nat) :
    RelCT isa (fun s₁ s₂ => k < VG.Proof.CmacAes.X86_64.N s₀ ∧ VG.Proof.CmacAes.X86_64.LInv s₀ k s₁ ∧ VG.Proof.CmacAes.X86_64.LInv s₀' k s₂) (body v.callee) fun _ _ => True := by
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp])
      (.block (chainIn ++ updArgs)) h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r13, .r14]) (.block advance) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun s₁ s₂ => k < VG.Proof.CmacAes.X86_64.N s₀ ∧ VG.Proof.CmacAes.X86_64.LInv s₀ k s₁ ∧ VG.Proof.CmacAes.X86_64.LInv s₀' k s₂) _
    (fun _ _ h => Taint.agree_ofRegs (LInv.agree hq h.2.1 h.2.2)) hA).wp
    (F₁ := VG.Proof.CmacAes.X86_64.Mid s₀ k) (F₂ := VG.Proof.CmacAes.X86_64.Mid s₀' k) fun _ _ h =>
      ⟨VG.Proof.CmacAes.X86_64.bodyMid_wp hp h.1 h.2.1, VG.Proof.CmacAes.X86_64.bodyMid_wp hp' (by rw [← VG.Proof.CmacAes.X86_64.pub_N hq]; exact h.1) h.2.2⟩
  have c := (VG.Proof.CmacAes.X86_64.ctr_rel v (P := fun s₁ s₂ => VG.Proof.CmacAes.X86_64.Mid s₀ k s₁ ∧ VG.Proof.CmacAes.X86_64.Mid s₀' k s₂) fun s₁ s₂ h =>
      ⟨_, _, _, _, _, h.1.pre, by
        rw [VG.Proof.CmacAes.X86_64.pub_W hq, VG.Proof.CmacAes.X86_64.pub_S hq, VG.Proof.CmacAes.X86_64.pub_St hq, VG.Proof.CmacAes.X86_64.pub_R hq]; exact h.2.pre,
        by rw [h.1.rsp, h.2.rsp, VG.Proof.CmacAes.X86_64.pub_rsp hq]⟩).wp
    (F₁ := VG.Proof.CmacAes.X86_64.After s₀ k) (F₂ := VG.Proof.CmacAes.X86_64.After s₀' k) fun s₁ s₂ h =>
      ⟨WP.mono (VG.Proof.CmacAes.X86_64.ctr_call v h.1.pre) fun _ hc =>
        ⟨by rw [hc.saved .r13 (by simp [calleeSaved]), h.1.r13],
          by rw [hc.saved .r14 (by simp [calleeSaved]), h.1.r14]⟩,
       WP.mono (VG.Proof.CmacAes.X86_64.ctr_call v h.2.pre) fun _ hc =>
        ⟨by rw [hc.saved .r13 (by simp [calleeSaved]), h.2.r13],
          by rw [hc.saved .r14 (by simp [calleeSaved]), h.2.r14]⟩⟩
  have b := RelCT.taint (A := taint) (P := fun s₁ s₂ => VG.Proof.CmacAes.X86_64.After s₀ k s₁ ∧ VG.Proof.CmacAes.X86_64.After s₀' k s₂) _
    (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.r13, h.2.r13, VG.Proof.CmacAes.X86_64.pub_Dp hq]
      · rw [h.1.r14, h.2.r14, VG.Proof.CmacAes.X86_64.pub_N hq]) hB
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((c.mono (fun _ _ h => h) fun _ _ h => h.2).seq b)

/-! ## The loop -/

/-- The loop's relation, with the number of iterations left. -/
def LRel (s₀ s₀' : State) (n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ k, n = VG.Proof.CmacAes.X86_64.N s₀ - k ∧ k < VG.Proof.CmacAes.X86_64.N s₀ ∧ VG.Proof.CmacAes.X86_64.LInv s₀ k s₁ ∧ VG.Proof.CmacAes.X86_64.LInv s₀' k s₂

theorem loop_ct (v : Ctr32Impl) {s₀ s₀' : State} (hp : VG.Proof.CmacAes.X86_64.UPre s₀) (hp' : VG.Proof.CmacAes.X86_64.UPre s₀')
    (hq : updateX86_64.pub s₀ s₀') (n : Nat) :
    RelCT isa (VG.Proof.CmacAes.X86_64.LRel s₀ s₀' n) (.loop (body v.callee) .ne)
      fun s₁ s₂ => VG.Proof.CmacAes.X86_64.LInv s₀ (VG.Proof.CmacAes.X86_64.N s₀) s₁ ∧ VG.Proof.CmacAes.X86_64.LInv s₀' (VG.Proof.CmacAes.X86_64.N s₀') s₂ := by
  refine RelCT.loop (M := isa) (VG.Proof.CmacAes.X86_64.LRel s₀ s₀') (fun n => ?_) n
  have hN := VG.Proof.CmacAes.X86_64.pub_N hq
  refine (RelCT.exists_ fun k => ?_).mono (fun s₁ s₂ (h : VG.Proof.CmacAes.X86_64.LRel s₀ s₀' n s₁ s₂) => h) fun _ _ h => h
  by_cases hn : n = VG.Proof.CmacAes.X86_64.N s₀ - k
  swap
  · exact RelCT.of_false fun _ _ h => hn h.1
  subst hn
  by_cases hk : k < VG.Proof.CmacAes.X86_64.N s₀
  swap
  · exact RelCT.of_false fun _ _ h => hk h.2.1
  have ct := (VG.Proof.CmacAes.X86_64.body_ct v hp hp' hq k).wp
    (F₁ := fun (s' : State) => VG.Proof.CmacAes.X86_64.LInv s₀ (k + 1) s' ∧ s'.zf = some (decide (VG.Proof.CmacAes.X86_64.N s₀ - (k + 1) = 0)))
    (F₂ := fun (s' : State) => VG.Proof.CmacAes.X86_64.LInv s₀' (k + 1) s' ∧ s'.zf = some (decide (VG.Proof.CmacAes.X86_64.N s₀' - (k + 1) = 0)))
    fun _ _ h => ⟨VG.Proof.CmacAes.X86_64.body_ok v hp h.1 h.2.1, VG.Proof.CmacAes.X86_64.body_ok v hp' (by rw [← hN]; exact h.1) h.2.2⟩
  refine ct.mono (fun _ _ h => h.2) fun s₁ s₂ ⟨_, ⟨l₁, z₁⟩, ⟨l₂, z₂⟩⟩ => ?_
  rw [← hN] at z₂
  have e₁ : isa.eval .ne s₁ = some (!decide (VG.Proof.CmacAes.X86_64.N s₀ - (k + 1) = 0)) := by
    show s₁.zf.map _ = _; rw [z₁]; rfl
  have e₂ : isa.eval .ne s₂ = some (!decide (VG.Proof.CmacAes.X86_64.N s₀ - (k + 1) = 0)) := by
    show s₂.zf.map _ = _; rw [z₂]; rfl
  refine ⟨by rw [e₁, e₂], fun hf => ?_, fun ht => ?_⟩
  · rw [e₁] at hf
    have h0 : VG.Proof.CmacAes.X86_64.N s₀ = k + 1 := by
      have : VG.Proof.CmacAes.X86_64.N s₀ - (k + 1) = 0 := by simpa using hf
      omega
    exact ⟨h0 ▸ l₁, by rw [← hN, h0]; exact l₂⟩
  · rw [e₁] at ht
    have h0 : VG.Proof.CmacAes.X86_64.N s₀ - (k + 1) ≠ 0 := by simpa using ht
    exact ⟨VG.Proof.CmacAes.X86_64.N s₀ - (k + 1), by omega, k + 1, rfl, by omega, l₁, l₂⟩

/-! ## The whole function -/

theorem update_rel (v : Ctr32Impl) {s₀ s₀' : State} (h0 : updateX86_64.pre s₀) (h0' : updateX86_64.pre s₀')
    (hq : updateX86_64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (update v.callee) fun _ _ => True := by
  have hp := UPre.of h0
  have hp' := UPre.of h0'
  have hN := VG.Proof.CmacAes.X86_64.pub_N hq
  obtain ⟨_, hpro⟩ : ∃ h, (taint.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp])
      (.block (save ++ setup)) h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hepi⟩ : ∃ h, (taint.check (Taint.ofRegs [.r15]) (.block restore) h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hnil⟩ : ∃ h, (taint.check (Taint.ofRegs []) (.block []) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have pro := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine Taint.agree_ofRegs fun r hr => ?_
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption) hpro).wp
    (F₁ := fun (s : State) => VG.Proof.CmacAes.X86_64.LInv s₀ 0 s ∧ s.zf = some (decide (VG.Proof.CmacAes.X86_64.N s₀ = 0)))
    (F₂ := fun (s : State) => VG.Proof.CmacAes.X86_64.LInv s₀' 0 s ∧ s.zf = some (decide (VG.Proof.CmacAes.X86_64.N s₀' = 0)))
    fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨VG.Proof.CmacAes.X86_64.prologue_wp hp, VG.Proof.CmacAes.X86_64.prologue_wp hp'⟩
  have nil := RelCT.taint (A := taint)
    (P := fun a b => ((VG.Proof.CmacAes.X86_64.LInv s₀ 0 a ∧ a.zf = some (decide (VG.Proof.CmacAes.X86_64.N s₀ = 0))) ∧
      (VG.Proof.CmacAes.X86_64.LInv s₀' 0 b ∧ b.zf = some (decide (VG.Proof.CmacAes.X86_64.N s₀' = 0)))) ∧ isa.eval .e a = some true) _
    (fun _ _ _ => Taint.agree_ofRegs fun r hr => by simp at hr) hnil
  have mid : RelCT isa (fun a b => (VG.Proof.CmacAes.X86_64.LInv s₀ 0 a ∧ a.zf = some (decide (VG.Proof.CmacAes.X86_64.N s₀ = 0))) ∧
      (VG.Proof.CmacAes.X86_64.LInv s₀' 0 b ∧ b.zf = some (decide (VG.Proof.CmacAes.X86_64.N s₀' = 0))))
      (.ite .e (.block []) (.loop (body v.callee) .ne))
      (fun a b => VG.Proof.CmacAes.X86_64.LInv s₀ (VG.Proof.CmacAes.X86_64.N s₀) a ∧ VG.Proof.CmacAes.X86_64.LInv s₀' (VG.Proof.CmacAes.X86_64.N s₀') b) := by
    refine RelCT.ite (fun a b h => ?_) ?_ ?_
    · show a.zf = b.zf; rw [h.1.2, h.2.2, hN]
    · refine (nil.wp (F₁ := VG.Proof.CmacAes.X86_64.LInv s₀ (VG.Proof.CmacAes.X86_64.N s₀)) (F₂ := VG.Proof.CmacAes.X86_64.LInv s₀' (VG.Proof.CmacAes.X86_64.N s₀')) fun a b h => ?_).mono
        (fun _ _ h => h) fun _ _ h => h.2
      have h0 : VG.Proof.CmacAes.X86_64.N s₀ = 0 := by
        have := h.2; change a.zf = _ at this; rw [h.1.1.2] at this; simpa using this
      exact ⟨WP.block_nil (h0 ▸ h.1.1.1), WP.block_nil (by rw [← hN, h0]; exact h.1.2.1)⟩
    · refine (VG.Proof.CmacAes.X86_64.loop_ct v hp hp' hq (VG.Proof.CmacAes.X86_64.N s₀ - 0)).mono (fun a b h => ⟨0, rfl, ?_, h.1.1.1, h.1.2.1⟩)
        fun _ _ h => h
      have := h.2; change a.zf = _ at this; rw [h.1.1.2] at this
      have : VG.Proof.CmacAes.X86_64.N s₀ ≠ 0 := by simpa using this
      omega
  have epi := RelCT.taint (A := taint) (P := fun a b => VG.Proof.CmacAes.X86_64.LInv s₀ (VG.Proof.CmacAes.X86_64.N s₀) a ∧ VG.Proof.CmacAes.X86_64.LInv s₀' (VG.Proof.CmacAes.X86_64.N s₀') b) _
    (fun a b h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [h.1.r15, h.2.r15, VG.Proof.CmacAes.X86_64.pub_S hq]) hepi
  exact (pro.mono (fun _ _ h => h) fun _ _ h => h.2).seq (mid.seq epi)

theorem update_ct (v : Ctr32Impl) :
    ConstantTime isa updateX86_64.pre updateX86_64.pub (update v.callee) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (VG.Proof.CmacAes.X86_64.update_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.X86_64

end

section

/-!
# AES-CMAC on x86-64: `vg_cmac_aes_subkeys` is constant time

The code before the call and after it is checked by the taint analysis, from
the registers the correctness proof pins (the arguments, then `rbx` and
`rbp`); the call of `vg_aes_ctr32` is constant time by its own proof
(`ctr_rel`).
-/

namespace VG.Proof.CmacAes.X86_64

open VG VG.X86_64 VG.Impl.CmacAes.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- What is known between the code before the call and the call. -/
structure SMid (s₀ : State) (W K S : Addr) (R : Nat) (s : State) : Prop where
  pre : VG.Proof.CmacAes.X86_64.CallPre s W (S + BitVec.ofNat 64 2048) K S R
  rbx : s.gpr .rbx = K
  rbp : s.gpr .rbp = S
  rsp : s.gpr .rsp = s₀.gpr .rsp

theorem smid_wp {s₀ : State} {W K S : Addr} {R : Nat} (hp : VG.Proof.CmacAes.X86_64.SPre s₀ W K S R) :
    WP isa (.block subkeysPre) s₀ (VG.Proof.CmacAes.X86_64.SMid s₀ W K S R) := by
  have sw := hp.scr_wrap
  have kw := hp.k_wrap
  have inS (d : Nat) (h : d + 8 ≤ 2176) : InRegions s₀.wr (s₀.gpr .rcx + BitVec.ofNat 64 d) 8 := by
    rw [hp.wr, hp.rcx]; exact VG.Proof.CmacAes.X86_64.in_rw (r := ⟨S, 2176⟩) (by simp) (Offset.contains_base _ h (by omega))
  have inK (d : Nat) (h : d + 8 ≤ 32) : InRegions s₀.wr (s₀.gpr .rdx + BitVec.ofNat 64 d) 8 := by
    rw [hp.wr, hp.rdx]; exact VG.Proof.CmacAes.X86_64.in_rw (r := ⟨K, 32⟩) (by simp) (Offset.contains_base _ h (by omega))
  obtain ⟨s₁, run₁, rdi₁, rsi₁, rdx₁, rcx₁, r8₁, r9₁, rbx₁, rbp₁, cs₁, mem₁, rd₁, wr₁⟩ :=
    VG.Proof.CmacAes.X86_64.subkeysPre_ok s₀ (inS _ (by decide)) (inS _ (by decide)) (inS _ (by decide)) (inS _ (by decide))
      (inK _ (by decide)) (inK _ (by decide))
  have rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := cs₁ .rsp (by simp [calleeSaved]) (by decide) (by decide)
  exact WP.of_runBlock ⟨s₁, run₁,
    VG.Proof.CmacAes.X86_64.callPre_of hp rdi₁ rsi₁ rdx₁ rcx₁ r8₁ r9₁ rsp₁ mem₁ rd₁ wr₁, by rw [rbx₁, hp.rdx], by rw [rbp₁, hp.rcx], rsp₁⟩

theorem subkeys_rel (v : Ctr32Impl) {s₀ s₀' : State} (h0 : subkeysX86_64.pre s₀)
    (h0' : subkeysX86_64.pre s₀') (hq : subkeysX86_64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (subkeys v.callee) fun _ _ => True := by
  obtain ⟨q1, q2, q3, q4, q5⟩ := hq
  have hp := SPre.of h0
  have hp' : VG.Proof.CmacAes.X86_64.SPre s₀' (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .rsi).toNat := by
    rw [q1, q2, q3, q4]; exact SPre.of h0'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .rsp]) (.block subkeysPre) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.rbx, .rbp]) (.block subkeysPost) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption) hA).wp
    (F₁ := VG.Proof.CmacAes.X86_64.SMid s₀ _ _ _ _) (F₂ := VG.Proof.CmacAes.X86_64.SMid s₀' _ _ _ _) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨VG.Proof.CmacAes.X86_64.smid_wp hp, VG.Proof.CmacAes.X86_64.smid_wp hp'⟩
  have c := (VG.Proof.CmacAes.X86_64.ctr_rel v (P := fun s₁ s₂ =>
      VG.Proof.CmacAes.X86_64.SMid s₀ (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .rsi).toNat s₁ ∧
      VG.Proof.CmacAes.X86_64.SMid s₀' (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .rsi).toNat s₂) fun s₁ s₂ h =>
      ⟨_, _, _, _, _, h.1.pre, h.2.pre, by rw [h.1.rsp, h.2.rsp, q5]⟩).wp
    (F₁ := fun (s : State) => s.gpr .rbx = s₀.gpr .rdx ∧ s.gpr .rbp = s₀.gpr .rcx)
    (F₂ := fun (s : State) => s.gpr .rbx = s₀.gpr .rdx ∧ s.gpr .rbp = s₀.gpr .rcx) fun s₁ s₂ h =>
      ⟨WP.mono (VG.Proof.CmacAes.X86_64.ctr_call v h.1.pre) fun _ hc =>
        ⟨by rw [hc.saved .rbx (by simp [calleeSaved]), h.1.rbx],
          by rw [hc.saved .rbp (by simp [calleeSaved]), h.1.rbp]⟩,
       WP.mono (VG.Proof.CmacAes.X86_64.ctr_call v h.2.pre) fun _ hc =>
        ⟨by rw [hc.saved .rbx (by simp [calleeSaved]), h.2.rbx],
          by rw [hc.saved .rbp (by simp [calleeSaved]), h.2.rbp]⟩⟩
  have b := RelCT.taint (A := taint)
    (P := fun s₁ s₂ => (s₁.gpr .rbx = s₀.gpr .rdx ∧ s₁.gpr .rbp = s₀.gpr .rcx) ∧
      (s₂.gpr .rbx = s₀.gpr .rdx ∧ s₂.gpr .rbp = s₀.gpr .rcx)) _
    (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.1, h.2.1]
      · rw [h.1.2, h.2.2]) hB
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((c.mono (fun _ _ h => h) fun _ _ h => h.2).seq b)

theorem subkeys_ct (v : Ctr32Impl) :
    ConstantTime isa subkeysX86_64.pre subkeysX86_64.pub (subkeys v.callee) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (VG.Proof.CmacAes.X86_64.subkeys_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.X86_64

end

section

/-!
# AES-CMAC on x86-64: `vg_cmac_aes_finalize` is constant time

The code before the call is checked by the taint analysis (its branches and
the copy loop depend only on `last_len`), and the call of `vg_aes_ctr32` is
constant time by its own proof (`ctr_rel`), its arguments pinned by the
correctness proof (`FMid`).
-/

namespace VG.Proof.CmacAes.X86_64

open VG VG.X86_64 VG.Impl.CmacAes.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)

theorem finalize_rel (v : Ctr32Impl) {s₀ s₀' : State} (h0 : finalizeX86_64.pre s₀)
    (h0' : finalizeX86_64.pre s₀') (hq : finalizeX86_64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (finalize v.callee) fun _ _ => True := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := hq
  have hp := FPre.of h0
  have hp' : VG.Proof.CmacAes.X86_64.FPre s₀' (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .r9) (s₀.gpr .r8).toNat
      (s₀.gpr .rsi).toNat := by
    rw [q1, q2, q3, q4, q5, q6]; exact FPre.of h0'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) finPre h).isSome =
      true := ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption) hA).wp
    (F₁ := VG.Proof.CmacAes.X86_64.FMid s₀ _ _ _ _ _ _) (F₂ := VG.Proof.CmacAes.X86_64.FMid s₀' _ _ _ _ _ _) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨VG.Proof.CmacAes.X86_64.finPre_wp hp, VG.Proof.CmacAes.X86_64.finPre_wp hp'⟩
  have c := VG.Proof.CmacAes.X86_64.ctr_rel v (P := fun s₁ s₂ =>
      VG.Proof.CmacAes.X86_64.FMid s₀ (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .r9) (s₀.gpr .r8).toNat (s₀.gpr .rsi).toNat s₁ ∧
      VG.Proof.CmacAes.X86_64.FMid s₀' (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .r9) (s₀.gpr .r8).toNat (s₀.gpr .rsi).toNat s₂)
    fun s₁ s₂ h => ⟨_, _, _, _, _, h.1.pre, h.2.pre, by
      rw [h.1.saved _ (by simp [calleeSaved]), h.2.saved _ (by simp [calleeSaved]), q7]⟩
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq c

theorem finalize_ct (v : Ctr32Impl) :
    ConstantTime isa finalizeX86_64.pre finalizeX86_64.pub (finalize v.callee) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (VG.Proof.CmacAes.X86_64.finalize_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.X86_64

end

/-!
# AES-CMAC on x86-64: `Verified`

Correctness and constant time (for any implementation `v` of `vg_aes_ctr32`),
a state satisfying each precondition, and the shared contracts of
`Spec/Cmac/Contract.lean` (with 8 bytes of stack, for the return address of
the call of `vg_aes_ctr32`).
-/

namespace VG.Proof.CmacAes.X86_64

open VG VG.X86_64 VG.Impl.CmacAes.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)

theorem update_mx (v : Ctr32Impl) : (update v.callee).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [update, body, Code.allInstrs, v.mxcsr]; decide +kernel

theorem subkeys_mx (v : Ctr32Impl) : (subkeys v.callee).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [subkeys, Code.allInstrs, v.mxcsr]; decide +kernel

theorem finalize_mx (v : Ctr32Impl) : (finalize v.callee).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [finalize, Code.allInstrs, v.mxcsr]; decide +kernel

theorem update_spSafe (v : Ctr32Impl) : (update v.callee).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [update, body, Code.all, v.spSafe]; decide +kernel

theorem subkeys_spSafe (v : Ctr32Impl) : (subkeys v.callee).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [subkeys, Code.all, v.spSafe]; decide +kernel

theorem finalize_spSafe (v : Ctr32Impl) : (finalize v.callee).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [finalize, Code.all, v.spSafe]; decide +kernel

theorem update_correct (v : Ctr32Impl) (s : State) (hs : updateX86_64.pre s) :
    ∃ t s', Exec isa (update v.callee) s t s' ∧ abiPreserved s s' ∧ updateX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := VG.Proof.CmacAes.X86_64.update_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (VG.Proof.CmacAes.X86_64.update_mx v) he hg, hp⟩

theorem subkeys_correct (v : Ctr32Impl) (s : State) (hs : subkeysX86_64.pre s) :
    ∃ t s', Exec isa (subkeys v.callee) s t s' ∧ abiPreserved s s' ∧ subkeysX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := VG.Proof.CmacAes.X86_64.subkeys_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (VG.Proof.CmacAes.X86_64.subkeys_mx v) he hg, hp⟩

theorem finalize_correct (v : Ctr32Impl) (s : State) (hs : finalizeX86_64.pre s) :
    ∃ t s', Exec isa (finalize v.callee) s t s' ∧ abiPreserved s s' ∧ finalizeX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := VG.Proof.CmacAes.X86_64.finalize_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (VG.Proof.CmacAes.X86_64.finalize_mx v) he hg, hp⟩

/-- A state satisfying `vg_cmac_aes_update`'s precondition (with no blocks). -/
def updSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x2000 | .rcx => 0x3000 | .r9 => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 240⟩, ⟨0x3000, 0⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x4000, 2176⟩]

theorem update_verified (v : Ctr32Impl) :
    Verified X86_64.target (update v.callee) (Spec.Cmac.aesUpdateContract X86_64.abi 8) :=
  Verified.of_correct (VG.Proof.CmacAes.X86_64.update_correct v) (VG.Proof.CmacAes.X86_64.update_ct v) (by
    sig_implies [Spec.Cmac.aesUpdateContract, Spec.Cmac.aesUpdateSig, VG.Proof.CmacAes.X86_64.updateX86_64, X86_64.abi,
      X86_64.argRegs] [updSat] using VG.Proof.CmacAes.X86_64.updSat)

/-- A state satisfying `vg_cmac_aes_subkeys`'s precondition. -/
def subSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x2000 | .rcx => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 240⟩]
  wr := [⟨0x2000, 32⟩, ⟨0x4000, 2176⟩]

theorem subkeys_verified (v : Ctr32Impl) :
    Verified X86_64.target (subkeys v.callee) (Spec.Cmac.aesSubkeysContract X86_64.abi 8) :=
  Verified.of_correct (VG.Proof.CmacAes.X86_64.subkeys_correct v) (VG.Proof.CmacAes.X86_64.subkeys_ct v) (by
    sig_implies [Spec.Cmac.aesSubkeysContract, Spec.Cmac.aesSubkeysSig, VG.Proof.CmacAes.X86_64.subkeysX86_64, X86_64.abi,
      X86_64.argRegs] [subSat] using VG.Proof.CmacAes.X86_64.subSat)

/-- A state satisfying `vg_cmac_aes_finalize`'s precondition (with no last bytes). -/
def finSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x2000 | .rcx => 0x3000 | .r9 => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 272⟩, ⟨0x3000, 0⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x4000, 2176⟩]

theorem finalize_verified (v : Ctr32Impl) :
    Verified X86_64.target (finalize v.callee) (Spec.Cmac.aesFinalizeContract X86_64.abi 8) :=
  Verified.of_correct (VG.Proof.CmacAes.X86_64.finalize_correct v) (VG.Proof.CmacAes.X86_64.finalize_ct v) (by
    sig_implies [Spec.Cmac.aesFinalizeContract, Spec.Cmac.aesFinalizeSig, VG.Proof.CmacAes.X86_64.finalizeX86_64, X86_64.abi,
      X86_64.argRegs] [finSat] using VG.Proof.CmacAes.X86_64.finSat)

end VG.Proof.CmacAes.X86_64

end
