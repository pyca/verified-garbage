module

public import VerifiedGarbage.Impl.Sm4Gcm.AArch64
public import VerifiedGarbage.Proof.AesGcm.AArch64.Callee
public import VerifiedGarbage.Spec.Sm4.Gcm
public import VerifiedGarbage.Proof.Sm4.Contract
public import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Sm4.AArch64.Ctr32Verified
import VerifiedGarbage.Proof.Sm4.AArch64.KeyVerified
import VerifiedGarbage.Proof.Sm4.AArch64.Ctr32Lit
import VerifiedGarbage.Proof.Sm4.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Depth
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# SM4-GCM on AArch64: the functions called

Untrusted: everything here is checked by Lean. Each call of `vg_sm4_ctr32`
and `vg_sm4_expand_key` from its callee's contract (with `WP.callF`), with
the regions it is given: what it needs (`CtrCall`, `KeyCall`) and what it
leaves (`CtrPost`, `KeyPost`); and that it is constant time (`ctr_rel`,
`key_rel`). Both keep their working space in frames below the stack pointer,
within the 3264 bytes there (`stk`), which they change. The calls of
`vg_ghash` are AES-GCM's (`Proof/AesGcm/AArch64/Callee.lean`).

The callees' contracts are the shared ones (`Proof.Sm4.ctr32Contract`,
`Spec.Sm4.expandKeyContract`) with their stack, which imply the simpler ones
here (`ctrF`, `keyF`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.AArch64

open VG VG.AArch64 VG.Impl.Sm4Gcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ctr32)

/-- The stack below `SP` the callees may use. -/
abbrev stk (SP : Addr) : Region := below SP 3264

/-- `vg_sm4_ctr32(schedule = x0, counter = x1, data = x2, n = x3)` with its
3264 bytes of stack. -/
def ctrF : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .x0, 128⟩
    let ctr : Region := ⟨s.gpr .x1, 16⟩
    let data : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat * 16⟩
    3264 ≤ s.sp.toNat ∧ s.rd = [sched] ∧ s.wr = [ctr, data] ∧ sched.Disjoint ctr ∧ sched.Disjoint data ∧
      ctr.Disjoint data ∧ (stk s.sp).Disjoint sched ∧ (stk s.sp).Disjoint ctr ∧ (stk s.sp).Disjoint data ∧
      (s.gpr .x0).toNat + 128 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 16 ≤ 2 ^ 64 ∧
      (s.gpr .x2).toNat + (s.gpr .x3).toNat * 16 ≤ 2 ^ 64
  post s s' :=
    blocksAt s'.mem (s.gpr .x2) (s.gpr .x3).toNat =
        ctr32 (Spec.Sm4.gcmCipher (Spec.Sm4.scheduleAt s.mem (s.gpr .x0))) (blockAt s.mem (s.gpr .x1))
          (blocksAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) ∧
      blockAt s'.mem (s.gpr .x1) = Nat.repeat Spec.Gcm.inc32 (s.gpr .x3).toNat (blockAt s.mem (s.gpr .x1))
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3

/-- A state satisfying `ctrF`'s precondition. -/
def ctrSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 1 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 16⟩]

theorem ctrF_implies : (Proof.Sm4.ctr32Contract AArch64.abi 3264).Implies ctrF where
  pre s hs := by
    sig_pre [Proof.Sm4.ctr32Contract, Proof.Sm4.ctr32Sig, AArch64.abi, AArch64.argRegs]
    exact hs
  post s s' _ h := by
    sig_reduce [Proof.Sm4.ctr32Contract, Proof.Sm4.ctr32Sig, AArch64.abi, AArch64.argRegs] at h
    rw [BitVec.setWidth_eq] at h
    exact h
  pub s₁ s₂ _ _ h := by
    sig_reduce [Proof.Sm4.ctr32Contract, Proof.Sm4.ctr32Sig, AArch64.abi, AArch64.argRegs]
    obtain ⟨hsp, h0, h1, h2, h3⟩ := h
    exact ⟨hsp, fun _ _ => by rw [h0, h1, h2, h3], fun _ hr => absurd hr List.not_mem_nil⟩
  sat := ⟨ctrSat, by
    refine ⟨by decide, rfl, rfl, Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
      Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
      Region.disjoint_of_sep (by decide), by decide, by decide, by decide⟩⟩

/-- `vg_sm4_expand_key(key = x0, schedule = x1)` with its 3168 bytes of
stack, within `stk`. -/
def keyF : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, 16⟩
    let sched : Region := ⟨s.gpr .x1, 128⟩
    3264 ≤ s.sp.toNat ∧ s.rd = [key] ∧ s.wr = [sched] ∧ key.Disjoint sched ∧ (stk s.sp).Disjoint key ∧
      (stk s.sp).Disjoint sched ∧ (s.gpr .x0).toNat + 16 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 128 ≤ 2 ^ 64
  post s s' := Spec.Sm4.scheduleAt s'.mem (s.gpr .x1) = Spec.Sm4.expandKey (Spec.Sm4.blockAt s.mem (s.gpr .x0))
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1

/-- A state satisfying `keyF`'s precondition. -/
def keySat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 128⟩]

/-- `vg_sm4_expand_key`'s stack within `stk`. -/
theorem key_stk (sp : Addr) : Region.Sub (below sp 3168) (stk sp) :=
  fun x hx => Offset.below_mono sp (by decide) (by decide) x hx

theorem keyF_implies : (Spec.Sm4.expandKeyContract AArch64.abi 3168).Implies keyF where
  pre s hs := by
    obtain ⟨hsp, hrd, hwr, dKS, dSK, dSS, fK, fS⟩ := hs
    sig_pre [Spec.Sm4.expandKeyContract, Spec.Sm4.expandKeySig, AArch64.abi, AArch64.argRegs]
    exact ⟨by omega, hrd, hwr, dKS, dSK.sub_left (key_stk _), dSS.sub_left (key_stk _), fK, fS⟩
  post s s' _ h := by
    sig_reduce [Spec.Sm4.expandKeyContract, Spec.Sm4.expandKeySig, AArch64.abi, AArch64.argRegs] at h
    exact h
  pub s₁ s₂ _ _ h := by
    sig_reduce [Spec.Sm4.expandKeyContract, Spec.Sm4.expandKeySig, AArch64.abi, AArch64.argRegs]
    obtain ⟨hsp, h0, h1⟩ := h
    exact ⟨hsp, fun _ _ => by rw [h0, h1], fun _ hr => absurd hr List.not_mem_nil⟩
  sat := ⟨keySat, by
    refine ⟨by decide, rfl, rfl, Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
      Region.disjoint_of_sep (by decide), by decide, by decide⟩⟩

theorem ctr_ok : ∀ s, ctrF.pre s → ∃ t s', Exec isa ctrCode s t s' ∧ abiPreserved s s' ∧ ctrF.post s s' :=
  (Proof.Sm4.AArch64.ctr32_framed.of_implies ctrF_implies).1

theorem ctr_ct : ConstantTime isa ctrF.pre ctrF.pub ctrCode :=
  (Proof.Sm4.AArch64.ctr32_framed.of_implies ctrF_implies).2.1

theorem key_ok : ∀ s, keyF.pre s → ∃ t s', Exec isa keyCode s t s' ∧ abiPreserved s s' ∧ keyF.post s s' :=
  (Proof.Sm4.AArch64.expandKey_framed.of_implies keyF_implies).1

theorem key_ct : ConstantTime isa keyF.pre keyF.pub keyCode :=
  (Proof.Sm4.AArch64.expandKey_framed.of_implies keyF_implies).2.1

theorem ctr_depth : 16 * ctrCode.aarch64Depth ≤ 3264 := by lit_decide

theorem key_depth : 16 * keyCode.aarch64Depth ≤ 3264 := by lit_decide

/-- The callees keep the low halves of `v8`–`v15`. -/
theorem ctrCode_keepsV : ctrCode.allInstrs keepsV = true := by lit_decide

theorem keyCode_keepsV : keyCode.allInstrs keepsV = true := by lit_decide

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-! ## `vg_sm4_ctr32` -/

/-- What a call of `vg_sm4_ctr32` needs: the key schedule at `K`, the counter
block at `C` and `n` blocks at `D`, apart from each other and from the stack
below the stack pointer. -/
structure CtrCall (s : State) (K C D : Addr) (n : Nat) : Prop where
  x0 : s.gpr .x0 = K
  x1 : s.gpr .x1 = C
  x2 : s.gpr .x2 = D
  x3 : s.gpr .x3 = BitVec.ofNat 64 n
  sp : 3264 ≤ s.sp.toNat
  n_lt : n < 2 ^ 64
  wrap : D.toNat + 16 * n ≤ 2 ^ 64
  kw : K.toNat + 128 ≤ 2 ^ 64
  cw : C.toNat + 16 ≤ 2 ^ 64
  kc : (⟨K, 128⟩ : Region).Disjoint ⟨C, 16⟩
  kd : (⟨K, 128⟩ : Region).Disjoint ⟨D, 16 * n⟩
  cd : (⟨C, 16⟩ : Region).Disjoint ⟨D, 16 * n⟩
  sk : (stk s.sp).Disjoint ⟨K, 128⟩
  sc : (stk s.sp).Disjoint ⟨C, 16⟩
  sd : (stk s.sp).Disjoint ⟨D, 16 * n⟩
  reads : Covers ([⟨K, 128⟩] ++ [⟨C, 16⟩, ⟨D, 16 * n⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨C, 16⟩, ⟨D, 16 * n⟩] s.wr

/-- What a call of `vg_sm4_ctr32` leaves. -/
structure CtrPost (s : State) (K C D : Addr) (n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r
  frame : Frame [⟨C, 16⟩, ⟨D, 16 * n⟩, stk s.sp] s.mem s'.mem
  out : blocksAt s'.mem D n = ctr32 (Spec.Sm4.gcmCipher (Spec.Sm4.scheduleAt s.mem K)) (blockAt s.mem C)
    (blocksAt s.mem D n)
  ctr : blockAt s'.mem C = Nat.repeat Spec.Gcm.inc32 n (blockAt s.mem C)

theorem CtrCall.pre {s : State} {K C D : Addr} {n : Nat} (h : CtrCall s K C D n) :
    ctrF.pre (s.callEntry.withRegions [⟨K, 128⟩] [⟨C, 16⟩, ⟨D, 16 * n⟩]) := by
  have hn := toNat_ofNat_lt h.n_lt
  simp only [ctrF, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp,
    State.callEntry_sp, AesGcm.AArch64.callEntry_x0, AesGcm.AArch64.callEntry_x1, AesGcm.AArch64.callEntry_x2,
    AesGcm.AArch64.callEntry_x3, h.x0, h.x1, h.x2, h.x3, hn, Nat.mul_comm n 16]
  exact ⟨h.sp, trivial, trivial, h.kc, h.kd, h.cd, h.sk, h.sc, h.sd, h.kw, h.cw, h.wrap⟩

theorem ctr_call {s : State} {K C D : Addr} {n : Nat} (h : CtrCall s K C D n) :
    WP isa ctrCall s (CtrPost s K C D n) := by
  have hn := toNat_ofNat_lt h.n_lt
  refine WP.callF (k := ctrF) ctr_ok (rd := [⟨K, 128⟩]) (wr := [⟨C, 16⟩, ⟨D, 16 * n⟩]) h.pre h.reads h.writes ?_
    (by lit_decide)
  intro s' hrd hwr hsp hf hsaved hpost
  obtain ⟨hdata, hctr⟩ := hpost
  simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    AesGcm.AArch64.callEntry_x0, AesGcm.AArch64.callEntry_x1, AesGcm.AArch64.callEntry_x2,
    AesGcm.AArch64.callEntry_x3, h.x0, h.x1, h.x2, h.x3, hn] at hdata hctr
  exact ⟨hrd, hwr, hsp, hsaved, Frame.below_mono hf ctr_depth (by decide), hdata, hctr⟩

theorem ctr_rel {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ K C D : Addr, ∃ n : Nat,
      CtrCall s₁ K C D n ∧ CtrCall s₂ K C D n ∧ s₁.sp = s₂.sp) :
    RelCT isa P ctrCall fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨K, C, D, n, h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine RelCT.call (P := fun a b => a = s₁ ∧ b = s₂) ctr_ok ctr_ct [⟨K, 128⟩]
    [⟨C, 16⟩, ⟨D, 16 * n⟩] (fun a b hab => ?_) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂
  obtain ⟨rfl, rfl⟩ := hab
  refine ⟨h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes⟩
  simp only [ctrF, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    AesGcm.AArch64.callEntry_x0, AesGcm.AArch64.callEntry_x1, AesGcm.AArch64.callEntry_x2,
    AesGcm.AArch64.callEntry_x3, h₁.x0, h₁.x1, h₁.x2, h₁.x3, h₂.x0, h₂.x1, h₂.x2, h₂.x3, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

/-! ## `vg_sm4_expand_key` -/

/-- What a call of `vg_sm4_expand_key` needs: the 16-byte key at `K` and the
key schedule at `C`, apart from each other and from the stack below the
stack pointer. -/
structure KeyCall (s : State) (K C : Addr) : Prop where
  x0 : s.gpr .x0 = K
  x1 : s.gpr .x1 = C
  sp : 3264 ≤ s.sp.toNat
  kw : K.toNat + 16 ≤ 2 ^ 64
  cw : C.toNat + 128 ≤ 2 ^ 64
  kc : (⟨K, 16⟩ : Region).Disjoint ⟨C, 128⟩
  sk : (stk s.sp).Disjoint ⟨K, 16⟩
  sc : (stk s.sp).Disjoint ⟨C, 128⟩
  reads : Covers ([⟨K, 16⟩] ++ [⟨C, 128⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨C, 128⟩] s.wr

/-- What a call of `vg_sm4_expand_key` leaves. -/
structure KeyPost (s : State) (K C : Addr) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r
  frame : Frame [⟨C, 128⟩, stk s.sp] s.mem s'.mem
  out : Spec.Sm4.scheduleAt s'.mem C = Spec.Sm4.expandKey (Spec.Sm4.blockAt s.mem K)

theorem KeyCall.pre {s : State} {K C : Addr} (h : KeyCall s K C) :
    keyF.pre (s.callEntry.withRegions [⟨K, 16⟩] [⟨C, 128⟩]) := by
  simp only [keyF, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp,
    State.callEntry_sp, AesGcm.AArch64.callEntry_x0, AesGcm.AArch64.callEntry_x1, h.x0, h.x1]
  exact ⟨h.sp, trivial, trivial, h.kc, h.sk, h.sc, h.kw, h.cw⟩

theorem key_call {s : State} {K C : Addr} (h : KeyCall s K C) :
    WP isa (.call "vg_sm4_expand_key" keyCode) s (KeyPost s K C) := by
  refine WP.callF (k := keyF) key_ok (rd := [⟨K, 16⟩]) (wr := [⟨C, 128⟩]) h.pre h.reads h.writes ?_
    (by lit_decide)
  intro s' hrd hwr hsp hf hsaved hpost
  simp only [keyF, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    AesGcm.AArch64.callEntry_x0, AesGcm.AArch64.callEntry_x1, h.x0, h.x1] at hpost
  exact ⟨hrd, hwr, hsp, hsaved, Frame.below_mono hf key_depth (by decide), hpost⟩

theorem key_rel {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ K C : Addr, KeyCall s₁ K C ∧ KeyCall s₂ K C ∧ s₁.sp = s₂.sp) :
    RelCT isa P (.call "vg_sm4_expand_key" keyCode) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨K, C, h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine RelCT.call (P := fun a b => a = s₁ ∧ b = s₂) key_ok key_ct [⟨K, 16⟩] [⟨C, 128⟩]
    (fun a b hab => ?_) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂
  obtain ⟨rfl, rfl⟩ := hab
  refine ⟨h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes⟩
  simp only [keyF, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    AesGcm.AArch64.callEntry_x0, AesGcm.AArch64.callEntry_x1, h₁.x0, h₁.x1, h₂.x0, h₂.x1, hsp]
  exact ⟨trivial, trivial, trivial⟩

/-! ## The implementations, together -/

/-- What an SM4-GCM function calls besides `vg_sm4_ctr32` and
`vg_sm4_expand_key`: an implementation of `vg_ghash`. -/
structure GcmImpl where
  gh : AesGcm.AArch64.GhashImpl

namespace GcmImpl

variable (v : GcmImpl)

def callees : Callees := ⟨v.gh.fn⟩

/-- What the names of the SM4-GCM functions end with: the suffix of the
implementation of `vg_ghash`. -/
def suffix : String := v.gh.suffix

end GcmImpl

end VG.Proof.Sm4Gcm.AArch64
