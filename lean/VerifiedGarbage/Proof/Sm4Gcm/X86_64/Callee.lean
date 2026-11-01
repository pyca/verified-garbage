module

import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe

public import VerifiedGarbage.Proof.Sm4.X86_64.Ctr32Verified
import VerifiedGarbage.Proof.Sm4.X86_64.KeyVerified
import VerifiedGarbage.Proof.Framework.X86_64.CallFrame
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Impl.Sm4Gcm.X86_64
public import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Sm4.CtrCipher
import VerifiedGarbage.Proof.Sm4.X86_64.Ctr32Lit
import VerifiedGarbage.Proof.Sm4.X86_64.Lit
public import VerifiedGarbage.Impl.Sm4.X86_64.ExpandKey
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.X86_64.Depth
public import VerifiedGarbage.Spec.Sm4.Contract
public import VerifiedGarbage.Proof.Sm4.Contract
public import VerifiedGarbage.TCB.X86_64.Target

/-!
# SM4-GCM on x86-64: the SM4 functions called

Untrusted: everything here is checked by Lean. The calls of
`vg_sm4_ctr32` and `vg_sm4_expand_key`, as registered: with their working
space in frames of their own on the stack, below the `stkN` bytes under the
stack pointer they use with their return address (`WP.callF`), from their
shared contracts (`Proof.Sm4.ctr32Contract`, `Spec.Sm4.expandKeyContract`):
what a call needs (`CtrCall`, `KeyCall`) and leaves (`CtrPost`, `KeyPost`),
and that it is constant time (`ctr_rel`, `key_rel`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.X86_64

open VG VG.X86_64 VG.Impl.Sm4Gcm.X86_64
open VG.Spec.Gcm (Block blockAt blocksAt)
open VG.Proof.AesGcm.X86_64 (blockAt_frame blocksAt_frame callEntry_frame toNat_ofNat_lt)

/-- The stack below the stack pointer that a call of `vg_sm4_ctr32` uses: its
return address, its frame of 3208 bytes and the return address of its own
call. A call of `vg_sm4_expand_key` uses less, and one of `vg_ghash` 8 bytes. -/
abbrev stkN : Nat := 3224

theorem stkN_eq : stkN = 3224 := rfl

/-- `vg_sm4_ctr32`'s contract, for its frames and calls. -/
abbrev ctrK : Contract isa := Proof.Sm4.ctr32Contract X86_64.abi 3216

/-- `vg_sm4_expand_key`'s contract, for its frame. -/
abbrev keyK : Contract isa := Spec.Sm4.expandKeyContract X86_64.abi 3144

theorem ctr_spSafe : SpSafe ctrFn.code := by
  have hcore : (Impl.Sm4.X86_64.ctr32).all (fun i => !isa.writesSp i) = true :=
    Code.all_of_allInstrs (by lit_decide)
  apply SpSafe.of_all
  refine withStackScratch_spSafe (r := .r8) (by decide) ?_
  simp only [Code.all, hcore, wipe_spSafe, Bool.and_self]

theorem key_spSafe : SpSafe keyFn.code := by
  have hcore : (Impl.Sm4.X86_64.expandKey).all (fun i => !isa.writesSp i) = true :=
    Code.all_of_allInstrs (by lit_decide)
  apply SpSafe.of_all
  refine withStackScratch_spSafe (r := .rdx) (by decide) ?_
  simp only [Code.all, hcore, wipe_spSafe, Bool.and_self]

theorem ctr_depth :
    (Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 Impl.Sm4.X86_64.ctr32).x86_64Depth ≤ 3216 := by
  lit_decide

theorem key_depth :
    (Impl.StackScratch.X86_64.withStackScratchWiped 3144 .rdx 392 Impl.Sm4.X86_64.expandKey).x86_64Depth ≤ 3144 := by
  lit_decide

/-- The stack a callee using `d` bytes below its return address writes is
within `stkN` bytes below the stack pointer. -/
theorem below_stk (sp : Addr) {d : Nat} (hd : d ≤ stkN - 8) : Region.Sub (below sp (d + 8)) (below sp stkN) := by
  have := stkN_eq
  exact Offset.sub_below sp (by omega) (by omega)

/-- The return address and the reserved stack of a callee's contract, from
the state after the call stored its return address: within `stkN` bytes below
the caller's stack pointer. -/
theorem reserved_stk (sp : Addr) {d : Nat} (hd : d ≤ stkN - 8) :
    Region.Sub ⟨sp - 8, 8⟩ (below sp stkN) ∧ Region.Sub ⟨sp - 8 - BitVec.ofNat 64 d, d⟩ (below sp stkN) := by
  have := stkN_eq
  refine ⟨Offset.sub_below sp (a := 8) (by decide) (by omega), ?_⟩
  rw [show sp - 8 - BitVec.ofNat 64 d = sp - BitVec.ofNat 64 (d + 8) by
    rw [BitVec.sub_sub, show (8 : Addr) = BitVec.ofNat 64 8 from rfl, BitVec.ofNat_add_ofNat, Nat.add_comm]]
  exact Offset.sub_below sp (by omega) (by omega)

/-! ## `vg_sm4_ctr32` -/

/-- What a call of `vg_sm4_ctr32` needs: the key schedule at `K`, the counter
block at `C` and `n` blocks at `D`, apart from each other and from the stack
the call uses. -/
structure CtrCall (s : State) (K C D : Addr) (n : Nat) : Prop where
  rdi : s.gpr .rdi = K
  rsi : s.gpr .rsi = C
  rdx : s.gpr .rdx = D
  rcx : s.gpr .rcx = BitVec.ofNat 64 n
  sp : stkN ≤ (s.gpr .rsp).toNat
  kw : K.toNat + 128 ≤ 2 ^ 64
  cw : C.toNat + 16 ≤ 2 ^ 64
  wrap : D.toNat + 16 * n ≤ 2 ^ 64
  kc : (⟨K, 128⟩ : Region).Disjoint ⟨C, 16⟩
  kd : (⟨K, 128⟩ : Region).Disjoint ⟨D, 16 * n⟩
  cd : (⟨C, 16⟩ : Region).Disjoint ⟨D, 16 * n⟩
  stkK : (below (s.gpr .rsp) stkN).Disjoint ⟨K, 128⟩
  stkC : (below (s.gpr .rsp) stkN).Disjoint ⟨C, 16⟩
  stkD : (below (s.gpr .rsp) stkN).Disjoint ⟨D, 16 * n⟩
  reads : Covers ([⟨K, 128⟩] ++ [⟨C, 16⟩, ⟨D, 16 * n⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨C, 16⟩, ⟨D, 16 * n⟩] s.wr

/-- What a call of `vg_sm4_ctr32` leaves. -/
structure CtrPost (s : State) (K C D : Addr) (n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨C, 16⟩, ⟨D, 16 * n⟩, below (s.gpr .rsp) stkN] s.mem s'.mem
  out : blocksAt s'.mem D n =
    Spec.Gcm.ctr32 (Spec.Sm4.gcmCipher (Spec.Sm4.scheduleAt s.mem K)) (blockAt s.mem C) (blocksAt s.mem D n)
  ctr : blockAt s'.mem C = Nat.repeat Spec.Gcm.inc32 n (blockAt s.mem C)

theorem CtrCall.pre {s : State} {K C D : Addr} {n : Nat} (h : CtrCall s K C D n) :
    ctrK.pre (s.callEntry.withRegions [⟨K, 128⟩] [⟨C, 16⟩, ⟨D, 16 * n⟩]) := by
  have hn := toNat_ofNat_lt (show n < 2 ^ 64 by have := h.wrap; omega)
  have ⟨rR, rS⟩ := reserved_stk (s.gpr .rsp) (d := 3216) (by decide)
  sig_pre [ctrK, Proof.Sm4.ctr32Contract, Proof.Sm4.ctr32Sig, X86_64.abi, X86_64.argRegs]
  simp only [h.rdi, h.rsi, h.rdx, h.rcx, hn, Nat.mul_comm n 16]
  have hsp := h.sp
  have := stkN_eq
  refine ⟨?_, trivial, trivial, h.kc, h.kd, h.cd, (h.stkK.sub_left rR), (h.stkC.sub_left rR), (h.stkD.sub_left rR),
    (h.stkK.sub_left rS), (h.stkC.sub_left rS), (h.stkD.sub_left rS), h.kw, h.cw, h.wrap⟩
  rw [BitVec.toNat_sub, show (8 : Addr).toNat = 8 from rfl]; omega

theorem ctr_call {s : State} {K C D : Addr} {n : Nat} (h : CtrCall s K C D n) :
    WP isa (.call ctrFn.name ctrFn.code) s (CtrPost s K C D n) := by
  have hn := toNat_ofNat_lt (show n < 2 ^ 64 by have := h.wrap; omega)
  refine WP.callF (k := ctrK) Proof.Sm4.X86_64.ctr32_framed.1 ctr_spSafe
    (Nat.lt_of_le_of_lt (Nat.add_le_add_right ctr_depth 16) (by decide))
    (rd := [⟨K, 128⟩]) (wr := [⟨C, 16⟩, ⟨D, 16 * n⟩]) h.pre h.reads h.writes ?_
  intro s' hrd hwr hcs hf ⟨s₂, hm₂, _, hpost⟩ _
  sig_post [ctrK, Proof.Sm4.ctr32Contract, Proof.Sm4.ctr32Sig, X86_64.abi, X86_64.argRegs] at hpost
  rw [h.rdi, h.rsi, h.rdx, h.rcx, hn, hm₂] at hpost
  obtain ⟨hdata, hctr⟩ := hpost
  have fE : Frame [below (s.gpr .rsp) 8] s.mem (s.mem.writeW (s.gpr .rsp - 8) (s.unknowns 0)) :=
    callEntry_frame s
  have s8 : Region.Sub (below (s.gpr .rsp) 8) (below (s.gpr .rsp) stkN) := below_stk _ (d := 0) (by decide)
  have dK : ∀ r ∈ [below (s.gpr .rsp) 8], (⟨K, 128⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact (h.stkK.sub_left s8).symm
  have dC : ∀ r ∈ [below (s.gpr .rsp) 8], (⟨C, 16⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact (h.stkC.sub_left s8).symm
  have dD : ∀ r ∈ [below (s.gpr .rsp) 8], (⟨D, 16 * n⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact (h.stkD.sub_left s8).symm
  have eK : Spec.Sm4.scheduleAt (s.mem.writeW (s.gpr .rsp - 8) (s.unknowns 0)) K = Spec.Sm4.scheduleAt s.mem K :=
    Proof.Sm4.scheduleAt_congr fun i hi => fE.bytes (R := ⟨K, 128⟩) dK (by show 128 ≤ 2 ^ 64; omega) hi
  rw [blockAt_frame fE dC, blocksAt_frame fE dD (by have := h.wrap; omega), eK] at hdata
  rw [blockAt_frame fE dC] at hctr
  refine ⟨hrd, hwr, hcs, hf.sub fun r hr => ?_, hdata, hctr⟩
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
  · exact ⟨_, by simp, below_stk _ (by have := ctr_depth; have := stkN_eq; omega)⟩

theorem ctr_rel {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ K C D : Addr, ∃ n : Nat,
      CtrCall s₁ K C D n ∧ CtrCall s₂ K C D n ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (.call ctrFn.name ctrFn.code) fun _ _ => True := by
  refine RelCT.callEx Proof.Sm4.X86_64.ctr32_framed.1 Proof.Sm4.X86_64.ctr32_framed.2.1 fun s₁ s₂ hp => ?_
  obtain ⟨K, C, D, n, h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨_, _, _, _, h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes, hsp⟩
  sig_pub [ctrK, Proof.Sm4.ctr32Contract, Proof.Sm4.ctr32Sig, X86_64.abi, X86_64.argRegs]
  simp only [h₁.rdi, h₁.rsi, h₁.rdx, h₁.rcx, h₂.rdi, h₂.rsi, h₂.rdx, h₂.rcx, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

/-! ## `vg_sm4_expand_key` -/

/-- What a call of `vg_sm4_expand_key` needs: the key at `Kk` and room for the
key schedule at `Sc`, apart from each other and from the stack the call uses. -/
structure KeyCall (s : State) (Kk Sc : Addr) : Prop where
  rdi : s.gpr .rdi = Kk
  rsi : s.gpr .rsi = Sc
  sp : stkN ≤ (s.gpr .rsp).toNat
  kw : Kk.toNat + 16 ≤ 2 ^ 64
  sw : Sc.toNat + 128 ≤ 2 ^ 64
  ks : (⟨Kk, 16⟩ : Region).Disjoint ⟨Sc, 128⟩
  stkK : (below (s.gpr .rsp) stkN).Disjoint ⟨Kk, 16⟩
  stkS : (below (s.gpr .rsp) stkN).Disjoint ⟨Sc, 128⟩
  reads : Covers ([⟨Kk, 16⟩] ++ [⟨Sc, 128⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨Sc, 128⟩] s.wr

/-- What a call of `vg_sm4_expand_key` leaves. -/
structure KeyPost (s : State) (Kk Sc : Addr) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨Sc, 128⟩, below (s.gpr .rsp) stkN] s.mem s'.mem
  out : Spec.Sm4.scheduleAt s'.mem Sc = Spec.Sm4.expandKey (Spec.Sm4.blockAt s.mem Kk)

theorem KeyCall.pre {s : State} {Kk Sc : Addr} (h : KeyCall s Kk Sc) :
    keyK.pre (s.callEntry.withRegions [⟨Kk, 16⟩] [⟨Sc, 128⟩]) := by
  have ⟨rR, rS⟩ := reserved_stk (s.gpr .rsp) (d := 3144) (by decide)
  sig_pre [keyK, Spec.Sm4.expandKeyContract, Spec.Sm4.expandKeySig, X86_64.abi, X86_64.argRegs]
  simp only [h.rdi, h.rsi]
  have hsp := h.sp
  have := stkN_eq
  refine ⟨?_, trivial, trivial, h.ks, (h.stkK.sub_left rR), (h.stkS.sub_left rR), (h.stkK.sub_left rS),
    (h.stkS.sub_left rS), h.kw, h.sw⟩
  rw [BitVec.toNat_sub, show (8 : Addr).toNat = 8 from rfl]; omega

theorem key_call {s : State} {Kk Sc : Addr} (h : KeyCall s Kk Sc) :
    WP isa (.call keyFn.name keyFn.code) s (KeyPost s Kk Sc) := by
  refine WP.callF (k := keyK) Proof.Sm4.X86_64.expandKey_framed.1 key_spSafe
    (Nat.lt_of_le_of_lt (Nat.add_le_add_right key_depth 16) (by decide))
    (rd := [⟨Kk, 16⟩]) (wr := [⟨Sc, 128⟩]) h.pre h.reads h.writes ?_
  intro s' hrd hwr hcs hf ⟨s₂, hm₂, _, hpost⟩ _
  sig_post [keyK, Spec.Sm4.expandKeyContract, Spec.Sm4.expandKeySig, X86_64.abi, X86_64.argRegs] at hpost
  rw [h.rdi, h.rsi, hm₂] at hpost
  have fE : Frame [below (s.gpr .rsp) 8] s.mem (s.mem.writeW (s.gpr .rsp - 8) (s.unknowns 0)) :=
    callEntry_frame s
  have s8 : Region.Sub (below (s.gpr .rsp) 8) (below (s.gpr .rsp) stkN) := below_stk _ (d := 0) (by decide)
  have eK : Spec.Sm4.blockAt (s.mem.writeW (s.gpr .rsp - 8) (s.unknowns 0)) Kk = Spec.Sm4.blockAt s.mem Kk := by
    apply Vector.ext
    intro i hi
    simp only [Spec.Sm4.blockAt, Vector.getElem_ofFn]
    exact fE.bytes (R := ⟨Kk, 16⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (h.stkK.sub_left s8).symm)
      (by show 16 ≤ 2 ^ 64; omega) hi
  rw [eK] at hpost
  refine ⟨hrd, hwr, hcs, hf.sub fun r hr => ?_, hpost⟩
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  · exact ⟨_, by simp, below_stk _ (by have := key_depth; have := stkN_eq; omega)⟩

theorem key_rel {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ Kk Sc : Addr,
      KeyCall s₁ Kk Sc ∧ KeyCall s₂ Kk Sc ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (.call keyFn.name keyFn.code) fun _ _ => True := by
  refine RelCT.callEx Proof.Sm4.X86_64.expandKey_framed.1 Proof.Sm4.X86_64.expandKey_framed.2.1
    fun s₁ s₂ hp => ?_
  obtain ⟨Kk, Sc, h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨_, _, _, _, h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes, hsp⟩
  sig_pub [keyK, Spec.Sm4.expandKeyContract, Spec.Sm4.expandKeySig, X86_64.abi, X86_64.argRegs]
  simp only [h₁.rdi, h₁.rsi, h₂.rdi, h₂.rsi, hsp]
  exact ⟨trivial, trivial, trivial⟩

end VG.Proof.Sm4Gcm.X86_64
