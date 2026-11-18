module

import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.Framework.X86_64.Spill
public import VerifiedGarbage.Impl.CmacAes.X86_64
public import VerifiedGarbage.Proof.Aes.X86_64.Variant
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Spec.Cmac
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.EntryBranch

/-! ### `CmacAes.X86_64.UpdateLoop`, which this module and modules that import it used -/

section

@[expose] public section

section

section

section

/-!
# AES-CMAC on x86-64: calling `vg_aes_ctr32` on one block

`ctr_call`: a call of any implementation of `vg_aes_ctr32` with the counter
block `C`, one data block `D` holding zeros, and working space `S`, from its
contract (with `WP.call`): `D` then holds `CIPH_K(C)`, as bytes
(`Cmac.aesWith`), and only `C`, `D`, `S` and the return address change.
The functions here make that call through `ctrCall`, which gives the
implementation its working space where it takes it in the scratch buffer
(`ctrCall_ok`, `AesCall`).
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
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_using [hR])

theorem one_toNat : (1 : BitVec 64).toNat = 1 := rfl

/-- `CallPre` for an implementation that needs no scratch buffer
(`Aes.X86_64.Ctr32Free`): none is given, `r9` any public value. -/
structure CallPreF (s : State) (W C D S : Addr) (R : Nat) : Prop where
  rdi : s.gpr .rdi = W
  rsi : s.gpr .rsi = BitVec.ofNat 64 R
  rdx : s.gpr .rdx = C
  rcx : s.gpr .rcx = D
  r8 : s.gpr .r8 = 1
  r9 : s.gpr .r9 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  wc : (⟨W, 240⟩ : Region).Disjoint ⟨C, 16⟩
  wd : (⟨W, 240⟩ : Region).Disjoint ⟨D, 16⟩
  cd : (⟨C, 16⟩ : Region).Disjoint ⟨D, 16⟩
  stkW : (below (s.gpr .rsp) 8).Disjoint ⟨W, 240⟩
  stkC : (below (s.gpr .rsp) 8).Disjoint ⟨C, 16⟩
  stkD : (below (s.gpr .rsp) 8).Disjoint ⟨D, 16⟩
  wrap : D.toNat + 16 ≤ 2 ^ 64
  reads : Covers ([⟨W, 240⟩] ++ [⟨C, 16⟩, ⟨D, 16⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨C, 16⟩, ⟨D, 16⟩] s.wr
  zero : Spec.Aes.bytesAt s.mem D 16 = Spec.Cmac.zeros 16

/-- What a call of `vg_aes_ctr32` on one block, without a scratch buffer, leaves. -/
structure CallPostF (s : State) (W C D : Addr) (R : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨C, 16⟩, ⟨D, 16⟩, below (s.gpr .rsp) 8] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem D 16 =
    Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem W (16 * (R + 1))) (Spec.Aes.bytesAt s.mem C 16)

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

/-- The block a call of `vg_aes_ctr32` on one zero block leaves, from the
postcondition of any of its contracts. -/
theorem CallPreF.out {s s₂ : State} {W C D S : Addr} {R : Nat} (h : CallPreF s W C D S R)
    {rd wr : List Region} (hpost : Proof.Aes.ctr32X86_64.post (s.callEntry.withRegions rd wr) s₂) :
    Spec.Aes.bytesAt s₂.mem D 16 =
      Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem W (16 * (R + 1))) (Spec.Aes.bytesAt s.mem C 16) := by
  have hR := toNat_rounds h.rounds
  obtain ⟨hdata, -⟩ := hpost
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
    (by omega_using [hRb])
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
  rw [Proof.Cmac.bytesAt_blockAt, hdata.1,
    Proof.Cmac.aesWith_bytes _ _ (Proof.Cmac.bytesAt_length _ _ _)]

/-- The arguments of a call with a scratch buffer, without it. -/
theorem CallPre.toF {s : State} {W C D S : Addr} {R : Nat} (h : CallPre s W C D S R) : CallPreF s W C D S R :=
  { rdi := h.rdi, rsi := h.rsi, rdx := h.rdx, rcx := h.rcx, r8 := h.r8, r9 := h.r9, rounds := h.rounds
    wc := h.wc, wd := h.wd, cd := h.cd, stkW := h.stkW, stkC := h.stkC, stkD := h.stkD, wrap := h.wrap
    reads := Covers.trans (Covers.of_mem fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl <;> simp) h.reads
    writes := Covers.trans (Covers.of_mem fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl <;> simp) h.writes
    zero := h.zero }

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
  · rw [← hm₂]; exact h.toF.out hpost

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

/-! ## Without a scratch buffer -/

theorem CallPreF.ctr_pre {s : State} {W C D S : Addr} {R : Nat} (h : CallPreF s W C D S R) :
    Proof.Aes.X86_64.AesNi.ctr32X86_64F.pre (s.callEntry.withRegions [⟨W, 240⟩] [⟨C, 16⟩, ⟨D, 16⟩]) := by
  have hR := toNat_rounds h.rounds
  simp only [Proof.Aes.X86_64.AesNi.ctr32X86_64F, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.callEntry_rsp, State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp),
    h.rdi, h.rsi, h.rdx, h.rcx, h.r8, hR, one_toNat, Nat.mul_one]
  exact ⟨trivial, trivial, h.wc, by simpa using h.wd, by simpa using h.cd, h.stkC, by simpa using h.stkD,
    by simpa using h.wrap, h.rounds⟩

theorem ctr_callF (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Free v.callee) {s : State} {W C D S : Addr}
    {R : Nat} (h : CallPreF s W C D S R) :
    WP isa (.call v.callee.name v.callee.code) s (CallPostF s W C D R) := by
  have hR := toNat_rounds h.rounds
  refine WP.call (k := Proof.Aes.X86_64.AesNi.ctr32X86_64F) f.ok v.nosp (by rw [v.depth]; decide)
    (rd := [⟨W, 240⟩]) (wr := [⟨C, 16⟩, ⟨D, 16⟩]) h.ctr_pre h.reads h.writes ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  rw [v.depth] at hf
  refine ⟨hrd, hwr, hcs, ?_, ?_⟩
  · simpa using hf
  · rw [← hm₂]; exact h.out hpost

theorem ctr_relF (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Free v.callee) {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ W C D S : Addr, ∃ R : Nat,
      CallPreF s₁ W C D S R ∧ CallPreF s₂ W C D S R ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (.call v.callee.name v.callee.code) fun _ _ => True := by
  refine RelCT.callEx f.ok f.ct fun s₁ s₂ hp => ?_
  obtain ⟨W, C, D, S, R, h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨_, _, _, _, h₁.ctr_pre, h₂.ctr_pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes, hsp⟩
  simp only [Proof.Aes.X86_64.AesNi.ctr32X86_64F, Proof.Aes.X86_64.AesNi.ctr32X86_64, State.withRegions_gpr,
    State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.r9 ≠ .rsp),
    h₁.rdi, h₁.rsi, h₁.rdx, h₁.rcx, h₁.r8, h₁.r9, h₂.rdi, h₂.rsi, h₂.rdx, h₂.rcx, h₂.r8, h₂.r9]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## The call, with its working space where the implementation takes it

`ctrCall` (`Impl/CmacAes/X86_64.lean`) calls `vg_aes_ctr32` with its working
space `scrOff` bytes into the scratch buffer in `r9`: at its start
(`ctrCall_zero`), or, for an implementation that uses only 1480 bytes of it
(`Aes.X86_64.Ctr32Small`), 512 bytes into it (`ctrCall_512`), so that the
first 512 bytes of the buffer are never touched. With a scratch buffer of
2048 bytes, the call is the same for any implementation (`ctrCall_ok`). -/

section CtrCall

open VG.Impl.CmacAes.X86_64 (ctrCall)
open VG.Proof.Aes.X86_64 (Ctr32Small Ctr32Free)
open VG.X86_64.RegUpd

theorem ctrCall_zero {c : Impl.Aes.X86_64.Ctr32} (h : c.scrOff = 0) : ctrCall c = .call c.name c.code := by
  unfold ctrCall; rw [h]; rfl

theorem ctrCall_512 {c : Impl.Aes.X86_64.Ctr32} (h : c.scrOff = 512) :
    ctrCall c = .seq (.block [.alu .add .r9 (.imm (BitVec.ofNat 32 512))]) (.call c.name c.code) := by
  unfold ctrCall; rw [h]; rfl

/-- A property of every instruction of the callee that an `add` to `r9` has. -/
theorem ctrCall_allInstrs {c : Impl.Aes.X86_64.Ctr32} {p : Instr → Bool}
    (hp : ∀ x, p (.alu .add .r9 (.imm x)) = true) (hc : c.code.allInstrs p = true) :
    (ctrCall c).allInstrs p = true := by
  unfold ctrCall
  split
  · exact hc
  · show (p _ && true && c.code.allInstrs p) = true
    rw [hp, hc]; rfl

theorem ctrCall_all {c : Impl.Aes.X86_64.Ctr32} {p : Instr → Bool}
    (hp : ∀ x, p (.alu .add .r9 (.imm x)) = true) (hc : c.code.all p = true) :
    (ctrCall c).all p = true := by
  unfold ctrCall
  split
  · exact hc
  · show ([_].all p && c.code.all p) = true
    rw [hc, List.all_cons, hp]; rfl

theorem ctrCall_depth (c : Impl.Aes.X86_64.Ctr32) : (ctrCall c).depth = c.code.depth + 1 := by
  unfold ctrCall
  split
  · rfl
  · exact Nat.zero_max _

theorem ctrCall_xdepth (c : Impl.Aes.X86_64.Ctr32) : (ctrCall c).x86_64Depth = c.code.x86_64Depth + 8 := by
  unfold ctrCall
  split
  · rfl
  · exact Nat.zero_max _

/-- What an `add` of 512 to the register `x` leaves. -/
def ScrAdd (x : Reg) (s s₁ : State) : Prop :=
  s₁.gpr x = s.gpr x + BitVec.ofNat 64 512 ∧ (∀ r, r ≠ x → s₁.gpr r = s.gpr r) ∧
    s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr

/-- The `add` before a call. -/
theorem scrAdd_ok (x : Reg) (s : State) :
    ∃ s₁, runBlock isa [.alu .add x (.imm (BitVec.ofNat 32 512))] s = some s₁ ∧ ScrAdd x s s₁ := by
  refine ⟨_, by simp only [runBlock_cons, exec, readSrc, execAlu]; rfl, ?_⟩
  simp only [ScrAdd, gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags,
    rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, ↓reduceIte]
  exact ⟨by rw [show BitVec.signExtend 64 (BitVec.ofNat 32 512) = BitVec.ofNat 64 512 by decide],
    fun r h => by simp [h], trivial, trivial, trivial⟩

/-- The `add` leaks nothing. -/
theorem scrAdd_rel (x : Reg) {P : State → State → Prop} :
    RelCT isa P (.block [.alu .add x (.imm (BitVec.ofNat 32 512))])
      fun t₁ t₂ => ∃ s₁ s₂, P s₁ s₂ ∧ ScrAdd x s₁ t₁ ∧ ScrAdd x s₂ t₂ := by
  have nil : ∀ i ∈ [Instr.alu .add x (.imm (BitVec.ofNat 32 512))], ∀ s : State, isa.addrs i s = [] := by
    intro i hi s; simp only [List.mem_singleton] at hi; subst hi; rfl
  have a : RelCT isa P (.block [.alu .add x (.imm (BitVec.ofNat 32 512))]) fun _ _ => True :=
    fun _ _ _ _ _ _ _ e₁ e₂ =>
      ⟨by rw [execBlock_trace_nil nil (Exec.block_iff.mp e₁), execBlock_trace_nil nil (Exec.block_iff.mp e₂)],
        trivial⟩
  refine (a.wpDep (F := ScrAdd x) fun s₁ s₂ _ => ?_).mono (fun _ _ h => h) fun _ _ h => h.2
  obtain ⟨_, r₁, h₁⟩ := scrAdd_ok x s₁
  obtain ⟨_, r₂, h₂⟩ := scrAdd_ok x s₂
  exact ⟨WP.of_runBlock ⟨_, r₁, h₁⟩, WP.of_runBlock ⟨_, r₂, h₂⟩⟩

/-- What a `sub` of 512 from the register `x` leaves: the scratch pointer
of a function given a scratch buffer without its first 512 bytes. -/
def ScrSub (x : Reg) (s s₁ : State) : Prop :=
  s₁.gpr x = s.gpr x - BitVec.ofNat 64 512 ∧ (∀ r, r ≠ x → s₁.gpr r = s.gpr r) ∧
    s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr

theorem scrSub_ok (x : Reg) (s : State) :
    ∃ s₁, runBlock isa [.alu .sub x (.imm (BitVec.ofNat 32 512))] s = some s₁ ∧ ScrSub x s s₁ := by
  refine ⟨_, by simp only [runBlock_cons, exec, readSrc, execAlu]; rfl, ?_⟩
  simp only [ScrSub, gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags,
    rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, ↓reduceIte]
  exact ⟨by rw [show BitVec.signExtend 64 (BitVec.ofNat 32 512) = BitVec.ofNat 64 512 by decide],
    fun r h => by simp [h], trivial, trivial, trivial⟩

/-- The `sub` leaks nothing. -/
theorem scrSub_rel (x : Reg) {P : State → State → Prop} :
    RelCT isa P (.block [.alu .sub x (.imm (BitVec.ofNat 32 512))])
      fun t₁ t₂ => ∃ s₁ s₂, P s₁ s₂ ∧ ScrSub x s₁ t₁ ∧ ScrSub x s₂ t₂ := by
  have nil : ∀ i ∈ [Instr.alu .sub x (.imm (BitVec.ofNat 32 512))], ∀ s : State, isa.addrs i s = [] := by
    intro i hi s; simp only [List.mem_singleton] at hi; subst hi; rfl
  have a : RelCT isa P (.block [.alu .sub x (.imm (BitVec.ofNat 32 512))]) fun _ _ => True :=
    fun _ _ _ _ _ _ _ e₁ e₂ =>
      ⟨by rw [execBlock_trace_nil nil (Exec.block_iff.mp e₁), execBlock_trace_nil nil (Exec.block_iff.mp e₂)],
        trivial⟩
  refine (a.wpDep (F := ScrSub x) fun s₁ s₂ _ => ?_).mono (fun _ _ h => h) fun _ _ h => h.2
  obtain ⟨_, r₁, h₁⟩ := scrSub_ok x s₁
  obtain ⟨_, r₂, h₂⟩ := scrSub_ok x s₂
  exact ⟨WP.of_runBlock ⟨_, r₁, h₁⟩, WP.of_runBlock ⟨_, r₂, h₂⟩⟩

/-- What a call of `vg_aes_ctr32` on one block leaves, writing no more than
`X` of its working space. -/
structure CallPostX (s : State) (W C D : Addr) (R : Nat) (X : Region) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨C, 16⟩, ⟨D, 16⟩, X, below (s.gpr .rsp) 8] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem D 16 =
    Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem W (16 * (R + 1))) (Spec.Aes.bytesAt s.mem C 16)

theorem CallPost.x {s s' : State} {W C D S : Addr} {R : Nat} (h : CallPost s W C D S R s') :
    CallPostX s W C D R ⟨S, 2048⟩ s' :=
  ⟨h.rd, h.wr, h.saved, h.frame, h.out⟩

theorem CallPostF.x {s s' : State} {W C D : Addr} {R : Nat} {X : Region} (h : CallPostF s W C D R s') :
    CallPostX s W C D R X s' :=
  ⟨h.rd, h.wr, h.saved, h.frame.mono (by simp), h.out⟩

/-! ### Without a scratch buffer -/

/-- What the `add` leaves, of the arguments of a call without a scratch
buffer. -/
theorem CallPreF.scrAdd {s s₁ : State} {W C D S : Addr} {R : Nat} (h : CallPreF s W C D S R)
    (a : ScrAdd .r9 s s₁) : CallPreF s₁ W C D (S + BitVec.ofNat 64 512) R := by
  obtain ⟨r9₁, g, m, rd, wr⟩ := a
  have sp := g .rsp (by decide)
  exact
    { rdi := by rw [g _ (by decide), h.rdi], rsi := by rw [g _ (by decide), h.rsi]
      rdx := by rw [g _ (by decide), h.rdx], rcx := by rw [g _ (by decide), h.rcx]
      r8 := by rw [g _ (by decide), h.r8], r9 := by rw [r9₁, h.r9], rounds := h.rounds
      wc := h.wc, wd := h.wd, cd := h.cd
      stkW := by rw [sp]; exact h.stkW, stkC := by rw [sp]; exact h.stkC, stkD := by rw [sp]; exact h.stkD
      wrap := h.wrap, reads := by rw [rd, wr]; exact h.reads, writes := by rw [wr]; exact h.writes
      zero := by rw [m]; exact h.zero }

/-- What a call after the `add` leaves, from the state before it. -/
theorem CallPostX.scrAdd {s s₁ s' : State} {W C D : Addr} {R : Nat} {X : Region} (a : ScrAdd .r9 s s₁)
    (h : CallPostX s₁ W C D R X s') : CallPostX s W C D R X s' := by
  obtain ⟨-, g, m, rd, wr⟩ := a
  exact ⟨by rw [h.rd, rd], by rw [h.wr, wr],
    fun r hr => by rw [h.saved r hr, g r (by rintro rfl; simp [calleeSaved] at hr)],
    by rw [← m, ← g .rsp (by decide)]; exact h.frame, by rw [h.out, m]⟩

theorem ctrCall_okF (v : Ctr32Impl) (f : Ctr32Free v.callee) {s : State} {W C D S : Addr} {R : Nat}
    (h : CallPreF s W C D S R) : WP isa (ctrCall v.callee) s (CallPostF s W C D R) := by
  rcases hs : v.small with _ | g
  · rw [ctrCall_zero (v.scr hs)]; exact ctr_callF v f h
  · rw [ctrCall_512 g.off]
    obtain ⟨s₁, run₁, a⟩ := scrAdd_ok .r9 s
    refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
    refine WP.mono (ctr_callF v f (h.scrAdd a)) fun s₂ h₂ => ?_
    obtain ⟨-, g₁, m, rd, wr⟩ := a
    exact ⟨by rw [h₂.rd, rd], by rw [h₂.wr, wr],
      fun r hr => by rw [h₂.saved r hr, g₁ r (by rintro rfl; simp [calleeSaved] at hr)],
      by rw [← m, ← g₁ .rsp (by decide)]; exact h₂.frame, by rw [h₂.out, m]⟩

theorem ctrCall_relF (v : Ctr32Impl) (f : Ctr32Free v.callee) {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ W C D S : Addr, ∃ R : Nat,
      CallPreF s₁ W C D S R ∧ CallPreF s₂ W C D S R ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (ctrCall v.callee) fun _ _ => True := by
  rcases hs : v.small with _ | g
  · rw [ctrCall_zero (v.scr hs)]; exact ctr_relF v f h
  · rw [ctrCall_512 g.off]
    refine (scrAdd_rel .r9).seq (ctr_relF v f fun t₁ t₂ ⟨s₁, s₂, hp, a₁, a₂⟩ => ?_)
    obtain ⟨W, C, D, S, R, h₁, h₂, hsp⟩ := h s₁ s₂ hp
    exact ⟨W, C, D, _, R, h₁.scrAdd a₁, h₂.scrAdd a₂, by rw [a₁.2.1 _ (by decide), a₂.2.1 _ (by decide), hsp]⟩

/-! ### With a scratch buffer of 1480 bytes -/

/-- `CallPre` for an implementation that uses only 1480 bytes of working
space (`Aes.X86_64.Ctr32Small`), at `A`, where `r9` points when it is
called. -/
structure CallPreS (s : State) (W C D A : Addr) (R : Nat) : Prop where
  rdi : s.gpr .rdi = W
  rsi : s.gpr .rsi = BitVec.ofNat 64 R
  rdx : s.gpr .rdx = C
  rcx : s.gpr .rcx = D
  r8 : s.gpr .r8 = 1
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  wc : (⟨W, 240⟩ : Region).Disjoint ⟨C, 16⟩
  wd : (⟨W, 240⟩ : Region).Disjoint ⟨D, 16⟩
  ws : (⟨W, 240⟩ : Region).Disjoint ⟨A, 1480⟩
  cd : (⟨C, 16⟩ : Region).Disjoint ⟨D, 16⟩
  cs : (⟨C, 16⟩ : Region).Disjoint ⟨A, 1480⟩
  ds : (⟨D, 16⟩ : Region).Disjoint ⟨A, 1480⟩
  stkW : (below (s.gpr .rsp) 8).Disjoint ⟨W, 240⟩
  stkC : (below (s.gpr .rsp) 8).Disjoint ⟨C, 16⟩
  stkD : (below (s.gpr .rsp) 8).Disjoint ⟨D, 16⟩
  stkS : (below (s.gpr .rsp) 8).Disjoint ⟨A, 1480⟩
  wrap : D.toNat + 16 ≤ 2 ^ 64
  reads : Covers ([⟨W, 240⟩] ++ [⟨C, 16⟩, ⟨D, 16⟩, ⟨A, 1480⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨C, 16⟩, ⟨D, 16⟩, ⟨A, 1480⟩] s.wr
  zero : Spec.Aes.bytesAt s.mem D 16 = Spec.Cmac.zeros 16

theorem CallPreS.toF {s : State} {W C D A : Addr} {R : Nat} (h : CallPreS s W C D A R) :
    CallPreF s W C D (s.gpr .r9) R :=
  { rdi := h.rdi, rsi := h.rsi, rdx := h.rdx, rcx := h.rcx, r8 := h.r8, r9 := rfl, rounds := h.rounds
    wc := h.wc, wd := h.wd, cd := h.cd, stkW := h.stkW, stkC := h.stkC, stkD := h.stkD, wrap := h.wrap
    reads := Covers.trans (Covers.of_mem fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl <;> simp) h.reads
    writes := Covers.trans (Covers.of_mem fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl <;> simp) h.writes
    zero := h.zero }

/-- The arguments of a call without a scratch buffer, with one of 1480
bytes at `A` that the regions allow. -/
theorem CallPreF.small {s : State} {W C D S A : Addr} {R : Nat} (h : CallPreF s W C D S R)
    (ws : (⟨W, 240⟩ : Region).Disjoint ⟨A, 1480⟩) (cs : (⟨C, 16⟩ : Region).Disjoint ⟨A, 1480⟩)
    (ds : (⟨D, 16⟩ : Region).Disjoint ⟨A, 1480⟩) (stkS : (below (s.gpr .rsp) 8).Disjoint ⟨A, 1480⟩)
    (wr : Covers [⟨A, 1480⟩] s.wr) : CallPreS s W C D A R :=
  { rdi := h.rdi, rsi := h.rsi, rdx := h.rdx, rcx := h.rcx, r8 := h.r8, rounds := h.rounds
    wc := h.wc, wd := h.wd, ws := ws, cd := h.cd, cs := cs, ds := ds
    stkW := h.stkW, stkC := h.stkC, stkD := h.stkD, stkS := stkS, wrap := h.wrap
    reads := by
      intro a n ⟨x, hx, hc⟩
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact h.reads a n ⟨_, by simp, hc⟩
      · exact h.reads a n ⟨_, by simp, hc⟩
      · exact h.reads a n ⟨_, by simp, hc⟩
      · exact Covers.right wr a n ⟨_, List.mem_singleton_self _, hc⟩
    writes := by
      intro a n ⟨x, hx, hc⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact h.writes a n ⟨_, by simp, hc⟩
      · exact h.writes a n ⟨_, by simp, hc⟩
      · exact wr a n ⟨_, List.mem_singleton_self _, hc⟩
    zero := h.zero }

theorem CallPreS.scrAdd {s s₁ : State} {W C D A : Addr} {R : Nat} (h : CallPreS s W C D A R)
    (a : ScrAdd .r9 s s₁) : CallPreS s₁ W C D A R := by
  have p := h.toF.scrAdd a
  obtain ⟨-, g, -, -, wr⟩ := a
  have sp := g .rsp (by decide)
  exact p.small h.ws h.cs h.ds (by rw [sp]; exact h.stkS) (by
    rw [wr]
    exact Covers.trans (Covers.of_mem fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp) h.writes)

theorem CallPreS.ctr_pre {s : State} {W C D A : Addr} {R : Nat} (h : CallPreS s W C D A R)
    (h9 : s.gpr .r9 = A) :
    Proof.Aes.ctr32X86_64S.pre (s.callEntry.withRegions [⟨W, 240⟩] [⟨C, 16⟩, ⟨D, 16⟩, ⟨A, 1480⟩]) := by
  have hR := toNat_rounds h.rounds
  simp only [Proof.Aes.ctr32X86_64S, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.callEntry_rsp, State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.r9 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h9, hR,
    one_toNat, Nat.mul_one]
  exact ⟨trivial, trivial, h.wc, by simpa using h.wd, h.ws, by simpa using h.cd, h.cs,
    by simpa using h.ds, h.stkC, by simpa using h.stkD, h.stkS, by simpa using h.wrap, h.rounds⟩

/-- A call of `vg_aes_ctr32` itself, with its 1480 bytes of working space. -/
theorem ctr_callS (v : Ctr32Impl) (f : Ctr32Small v.callee) {s : State} {W C D A : Addr} {R : Nat}
    (h : CallPreS s W C D A R) (h9 : s.gpr .r9 = A) :
    WP isa (.call v.callee.name v.callee.code) s (CallPostX s W C D R ⟨A, 1480⟩) := by
  refine WP.call (k := Proof.Aes.ctr32X86_64S) f.ok v.nosp (by rw [v.depth]; decide)
    (rd := [⟨W, 240⟩]) (wr := [⟨C, 16⟩, ⟨D, 16⟩, ⟨A, 1480⟩]) (h.ctr_pre h9) h.reads h.writes ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  rw [v.depth] at hf
  refine ⟨hrd, hwr, hcs, ?_, ?_⟩
  · simpa using hf
  · rw [← hm₂]; exact h.toF.out hpost

theorem ctr_relS (v : Ctr32Impl) (f : Ctr32Small v.callee) {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ W C D A : Addr, ∃ R : Nat,
      CallPreS s₁ W C D A R ∧ CallPreS s₂ W C D A R ∧ s₁.gpr .r9 = A ∧ s₂.gpr .r9 = A ∧
      s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (.call v.callee.name v.callee.code) fun _ _ => True := by
  refine RelCT.callEx f.ok f.ct fun s₁ s₂ hp => ?_
  obtain ⟨W, C, D, A, R, h₁, h₂, e₁, e₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨_, _, _, _, h₁.ctr_pre e₁, h₂.ctr_pre e₂, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes, hsp⟩
  simp only [Proof.Aes.ctr32X86_64S, Proof.Aes.ctr32X86_64, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.r9 ≠ .rsp),
    h₁.rdi, h₁.rsi, h₁.rdx, h₁.rcx, h₁.r8, e₁, h₂.rdi, h₂.rsi, h₂.rdx, h₂.rcx, h₂.r8, e₂, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

/-- The call, over an implementation that uses 1480 bytes of working space,
512 bytes into the scratch buffer `S`. -/
theorem ctrCall_okS (v : Ctr32Impl) (f : Ctr32Small v.callee) {s : State} {W C D S : Addr} {R : Nat}
    (h : CallPreS s W C D (S + BitVec.ofNat 64 512) R) (h9 : s.gpr .r9 = S) :
    WP isa (ctrCall v.callee) s (CallPostX s W C D R ⟨S + BitVec.ofNat 64 512, 1480⟩) := by
  rw [ctrCall_512 f.off]
  obtain ⟨s₁, run₁, a⟩ := scrAdd_ok .r9 s
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  exact WP.mono (ctr_callS v f (h.scrAdd a) (by rw [a.1, h9])) fun _ h₂ => h₂.scrAdd a

theorem ctrCall_relS (v : Ctr32Impl) (f : Ctr32Small v.callee) {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ W C D S : Addr, ∃ R : Nat,
      CallPreS s₁ W C D (S + BitVec.ofNat 64 512) R ∧ CallPreS s₂ W C D (S + BitVec.ofNat 64 512) R ∧
      s₁.gpr .r9 = S ∧ s₂.gpr .r9 = S ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (ctrCall v.callee) fun _ _ => True := by
  rw [ctrCall_512 f.off]
  refine (scrAdd_rel .r9).seq (ctr_relS v f fun t₁ t₂ ⟨s₁, s₂, hp, a₁, a₂⟩ => ?_)
  obtain ⟨W, C, D, S, R, h₁, h₂, e₁, e₂, hsp⟩ := h s₁ s₂ hp
  exact ⟨W, C, D, _, R, h₁.scrAdd a₁, h₂.scrAdd a₂, by rw [a₁.1, e₁], by rw [a₂.1, e₂],
    by rw [a₁.2.1 _ (by decide), a₂.2.1 _ (by decide), hsp]⟩

/-! ### With a scratch buffer of 2048 bytes, for any implementation -/

/-- The 1480 bytes 512 bytes into a scratch buffer of 2048. -/
theorem CallPre.small {s : State} {W C D S : Addr} {R : Nat} (h : CallPre s W C D S R) :
    CallPreS s W C D (S + BitVec.ofNat 64 512) R :=
  have sb : Region.Sub ⟨S + BitVec.ofNat 64 512, 1480⟩ ⟨S, 2048⟩ := Offset.sub_base _ (by decide)
  h.toF.small (h.ws.sub_right sb) (h.cs.sub_right sb) (h.ds.sub_right sb) (h.stkS.sub_right sb)
    (Covers.trans (Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨S, 2048⟩, by simp, 512, rfl, by simp⟩) h.writes)

theorem CallPostX.full {s s' : State} {W C D S : Addr} {R : Nat}
    (h : CallPostX s W C D R ⟨S + BitVec.ofNat 64 512, 1480⟩ s') : CallPost s W C D S R s' :=
  ⟨h.rd, h.wr, h.saved, h.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨⟨D, 16⟩, by simp, fun _ h => h⟩
    · exact ⟨⟨S, 2048⟩, by simp, Offset.sub_base _ (by decide)⟩
    · exact ⟨below (s.gpr .rsp) 8, by simp, fun _ h => h⟩, h.out⟩

/-- The call, over any implementation, with a scratch buffer of 2048 bytes:
either it is given the whole of it, or the 1480 bytes it uses within it. -/
theorem ctrCall_ok (v : Ctr32Impl) {s : State} {W C D S : Addr} {R : Nat} (h : CallPre s W C D S R) :
    WP isa (ctrCall v.callee) s (CallPost s W C D S R) := by
  rcases hs : v.small with _ | f
  · rw [ctrCall_zero (v.scr hs)]; exact ctr_call v h
  · exact WP.mono (ctrCall_okS v f h.small h.r9) fun _ h' => h'.full

theorem ctrCall_rel (v : Ctr32Impl) {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ W C D S : Addr, ∃ R : Nat,
      CallPre s₁ W C D S R ∧ CallPre s₂ W C D S R ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (ctrCall v.callee) fun _ _ => True := by
  rcases hs : v.small with _ | f
  · rw [ctrCall_zero (v.scr hs)]; exact ctr_rel v h
  · refine ctrCall_relS v f fun s₁ s₂ hp => ?_
    obtain ⟨W, C, D, S, R, h₁, h₂, hsp⟩ := h s₁ s₂ hp
    exact ⟨W, C, D, S, R, h₁.small, h₂.small, h₁.r9, h₂.r9, hsp⟩

/-! ### For any part of the scratch buffer

What the functions here need of their call of `vg_aes_ctr32`, whatever part
of their scratch buffer is writable (`AesCall`): all of it, with any
implementation (`AesCall.base`); none of the working space, with one that
needs none (`AesCall.free`); or all but its first 512 bytes, with one that
uses 1480 bytes of working space (`AesCall.small`). -/

/-- What the writable part `Z` of a scratch buffer is apart from, at a call
with the key schedule `W` and the data block `D`. -/
structure ScrPre (s : State) (W D : Addr) (Z : Region) : Prop where
  w : (⟨W, 240⟩ : Region).Disjoint Z
  d : (⟨D, 16⟩ : Region).Disjoint Z
  stk : (below (s.gpr .rsp) 8).Disjoint Z
  wr : Covers [Z] s.wr

/-- The call of `vg_aes_ctr32 c` on the counter block at `S + 2048`, for the
writable part `Z S` of each scratch buffer `S`: from its arguments, it
writes no more of the scratch buffer than `X S`, within `Z S` and below the
counter block; and two calls with the same arguments leak the same. -/
structure AesCall (c : Impl.Aes.X86_64.Ctr32) (Z X : Addr → Region) : Prop where
  sub : ∀ S, Region.Sub (X S) (Z S)
  disj : ∀ S, (⟨S + BitVec.ofNat 64 2048, 128⟩ : Region).Disjoint (X S)
  ok : ∀ {s : State} {W D S : Addr} {R : Nat}, CallPreF s W (S + BitVec.ofNat 64 2048) D S R →
    ScrPre s W D (Z S) → WP isa (ctrCall c) s (CallPostX s W (S + BitVec.ofNat 64 2048) D R (X S))
  rel : ∀ {P : State → State → Prop}, (∀ s₁ s₂, P s₁ s₂ → ∃ W D S : Addr, ∃ R : Nat,
      (CallPreF s₁ W (S + BitVec.ofNat 64 2048) D S R ∧ ScrPre s₁ W D (Z S)) ∧
      (CallPreF s₂ W (S + BitVec.ofNat 64 2048) D S R ∧ ScrPre s₂ W D (Z S)) ∧
      s₁.gpr .rsp = s₂.gpr .rsp) →
    RelCT isa P (ctrCall c) fun _ _ => True

/-- With all of the scratch buffer writable, the arguments of the call
include its working space. -/
theorem CallPreF.full {s : State} {W D S : Addr} {R : Nat}
    (h : CallPreF s W (S + BitVec.ofNat 64 2048) D S R) (z : ScrPre s W D ⟨S, 2176⟩) :
    CallPre s W (S + BitVec.ofNat 64 2048) D S R :=
  have sb : Region.Sub ⟨S, 2048⟩ ⟨S, 2176⟩ := Region.sub_prefix (by decide)
  have zc : Covers [⟨S, 2048⟩] s.wr := Covers.trans (Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨S, 2176⟩, by simp, 0, by simp, by simp⟩) z.wr
  { rdi := h.rdi, rsi := h.rsi, rdx := h.rdx, rcx := h.rcx, r8 := h.r8, r9 := h.r9, rounds := h.rounds
    wc := h.wc, wd := h.wd, ws := z.w.sub_right sb, cd := h.cd
    cs := Offset.disjoint_base _ (by decide) (by decide), ds := z.d.sub_right sb
    stkW := h.stkW, stkC := h.stkC, stkD := h.stkD, stkS := z.stk.sub_right sb, wrap := h.wrap
    reads := by
      intro a n ⟨x, hx, hc⟩
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact h.reads a n ⟨_, by simp, hc⟩
      · exact h.reads a n ⟨_, by simp, hc⟩
      · exact h.reads a n ⟨_, by simp, hc⟩
      · exact Covers.right zc a n ⟨_, List.mem_singleton_self _, hc⟩
    writes := by
      intro a n ⟨x, hx, hc⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact h.writes a n ⟨_, by simp, hc⟩
      · exact h.writes a n ⟨_, by simp, hc⟩
      · exact zc a n ⟨_, List.mem_singleton_self _, hc⟩
    zero := h.zero }

/-- Over any implementation of `vg_aes_ctr32`, with all of the scratch buffer. -/
theorem AesCall.base (v : Ctr32Impl) : AesCall v.callee (fun S => ⟨S, 2176⟩) (fun S => ⟨S, 2048⟩) where
  sub _ := Region.sub_prefix (by decide)
  disj _ := Offset.disjoint_base _ (by decide) (by decide)
  ok h z := WP.mono (ctrCall_ok v (h.full z)) fun _ h => h.x
  rel h := ctrCall_rel v fun a b hab =>
    let ⟨W, D, S, R, h₁, h₂, q⟩ := h a b hab
    ⟨W, _, D, S, R, h₁.1.full h₁.2, h₂.1.full h₂.2, q⟩

/-- Over an implementation of `vg_aes_ctr32` that needs no working space,
whatever is writable. -/
theorem AesCall.free (v : Ctr32Impl) (f : Ctr32Free v.callee) (Z : Addr → Region) :
    AesCall v.callee Z (fun S => ⟨S + BitVec.ofNat 64 2048, 0⟩) where
  sub _ := fun _ h => absurd h (by simp [Region.Contains])
  disj _ := fun _ _ h => by simp [Region.Contains] at h
  ok h _ := WP.mono (ctrCall_okF v f h) fun _ h => h.x
  rel h := ctrCall_relF v f fun a b hab =>
    let ⟨W, D, S, R, h₁, h₂, q⟩ := h a b hab
    ⟨W, _, D, S, R, h₁.1, h₂.1, q⟩

/-- The arguments of the call with the 1480 bytes of working space 512 bytes
into the scratch buffer, when all but the first 512 bytes of it are
writable. -/
theorem CallPreF.smallOf {s : State} {W D S : Addr} {R : Nat}
    (h : CallPreF s W (S + BitVec.ofNat 64 2048) D S R)
    (z : ScrPre s W D ⟨S + BitVec.ofNat 64 512, 1664⟩) :
    CallPreS s W (S + BitVec.ofNat 64 2048) D (S + BitVec.ofNat 64 512) R :=
  have sb : Region.Sub ⟨S + BitVec.ofNat 64 512, 1480⟩ ⟨S + BitVec.ofNat 64 512, 1664⟩ :=
    Region.sub_prefix (by decide)
  h.small (z.w.sub_right sb) (Offset.disjoint S (by decide) (by decide) (by decide)) (z.d.sub_right sb)
    (z.stk.sub_right sb) (Covers.trans (Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨S + BitVec.ofNat 64 512, 1664⟩, by simp, 0, by simp, by simp⟩) z.wr)

/-- Over an implementation of `vg_aes_ctr32` that uses 1480 bytes of working
space, with all of the scratch buffer but its first 512 bytes. -/
theorem AesCall.small (v : Ctr32Impl) (f : Ctr32Small v.callee) :
    AesCall v.callee (fun S => ⟨S + BitVec.ofNat 64 512, 1664⟩) (fun S => ⟨S + BitVec.ofNat 64 512, 1480⟩) where
  sub _ := Region.sub_prefix (by decide)
  disj S := Offset.disjoint S (by decide) (by decide) (by decide)
  ok h z := ctrCall_okS v f (h.smallOf z) h.r9
  rel h := ctrCall_relS v f fun a b hab =>
    let ⟨W, D, S, R, h₁, h₂, q⟩ := h a b hab
    ⟨W, _, D, S, R, h₁.1.smallOf h₁.2, h₂.1.smallOf h₂.2, h₁.1.r9, h₂.1.r9, q⟩

end CtrCall

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

/-- `updateX86_64` over an implementation of `vg_aes_ctr32` that uses 1480
bytes of working space (`Aes.X86_64.Ctr32Small`), which it is given 512
bytes into `scratch`: the first 512 bytes of `scratch` are never touched,
so its caller need not give them. -/
def updateX86_64S : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .rdi, 240⟩
    let state : Region := ⟨s.gpr .rdx, 16⟩
    let data : Region := ⟨s.gpr .rcx, 16 * (s.gpr .r8).toNat⟩
    let scr : Region := ⟨s.gpr .r9 + BitVec.ofNat 64 512, 1664⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack := below (s.gpr .rsp) 8
    s.rd = [sched, data] ∧ s.wr = [state, scr] ∧
      sched.Disjoint state ∧ sched.Disjoint scr ∧ data.Disjoint state ∧ data.Disjoint scr ∧
      state.Disjoint scr ∧ ret.Disjoint state ∧ ret.Disjoint scr ∧
      stack.Disjoint sched ∧ stack.Disjoint data ∧ stack.Disjoint state ∧ stack.Disjoint scr ∧
      (s.gpr .rdx).toNat + 16 ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + 16 * (s.gpr .r8).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r9 + BitVec.ofNat 64 512).toNat + 1664 ≤ 2 ^ 64 ∧
      ((s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14)
  post := updateX86_64.post
  pub := updateX86_64.pub

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


/-- `finalizeX86_64` when `vg_aes_ctr32` needs no working space
(`Aes.X86_64.Ctr32Free`): of `scratch`, only the counter block at
`scratch + 2048` is written, so its caller need give no more. -/
def finalizeX86_64F : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, 272⟩
    let state : Region := ⟨s.gpr .rdx, 16⟩
    let last : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
    let cb : Region := ⟨s.gpr .r9 + BitVec.ofNat 64 2048, 16⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack := below (s.gpr .rsp) 8
    s.rd = [key, last] ∧ s.wr = [state, cb] ∧
      key.Disjoint state ∧ key.Disjoint cb ∧ last.Disjoint state ∧ last.Disjoint cb ∧
      state.Disjoint cb ∧ ret.Disjoint state ∧ ret.Disjoint cb ∧
      stack.Disjoint key ∧ stack.Disjoint last ∧ stack.Disjoint state ∧ stack.Disjoint cb ∧
      (s.gpr .rdi).toNat + 272 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 16 ≤ 2 ^ 64 ∧
      (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧ (s.gpr .r9 + BitVec.ofNat 64 2048).toNat + 16 ≤ 2 ^ 64 ∧
      ((s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14) ∧
      (s.gpr .r8).toNat ≤ 16
  post := finalizeX86_64.post
  pub := finalizeX86_64.pub

/-- `finalizeX86_64` over an implementation of `vg_aes_ctr32` that uses 1480
bytes of working space (`Aes.X86_64.Ctr32Small`), which it is given 512
bytes into `scratch`: the first 512 bytes of `scratch` are never touched,
so its caller need not give them. -/
def finalizeX86_64S : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, 272⟩
    let state : Region := ⟨s.gpr .rdx, 16⟩
    let last : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
    let scr : Region := ⟨s.gpr .r9 + BitVec.ofNat 64 512, 1664⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack := below (s.gpr .rsp) 8
    s.rd = [key, last] ∧ s.wr = [state, scr] ∧
      key.Disjoint state ∧ key.Disjoint scr ∧ last.Disjoint state ∧ last.Disjoint scr ∧
      state.Disjoint scr ∧ ret.Disjoint state ∧ ret.Disjoint scr ∧
      stack.Disjoint key ∧ stack.Disjoint last ∧ stack.Disjoint state ∧ stack.Disjoint scr ∧
      (s.gpr .rdi).toNat + 272 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 16 ≤ 2 ^ 64 ∧
      (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r9 + BitVec.ofNat 64 512).toNat + 1664 ≤ 2 ^ 64 ∧
      ((s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14) ∧
      (s.gpr .r8).toNat ≤ 16
  post := finalizeX86_64.post
  pub := finalizeX86_64.pub

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
(`r13` the next block, `r14` the blocks left), only the state, the counter
block, what the calls write of the scratch buffer and the stack below the
return address have
changed since the registers were saved, and the state is the chaining value
after the first `k` blocks. The proof is over the writable part `Z` of the
scratch buffer and the call of `vg_aes_ctr32` (`AesCall`).
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

/-- The precondition, by name, with the writable part `Z` of the scratch
buffer: all of it (`updateX86_64`), or all but its first 512 bytes, over an
implementation of `vg_aes_ctr32` that uses 1480 bytes of working space
(`updateX86_64S`). -/
structure UPre (s₀ : State) (Z : Region) : Prop where
  rd : s₀.rd = [schR s₀, dataR s₀]
  wr : s₀.wr = [stR s₀, Z]
  sch_st : (schR s₀).Disjoint (stR s₀)
  sch_scr : (schR s₀).Disjoint Z
  data_st : (dataR s₀).Disjoint (stR s₀)
  data_scr : (dataR s₀).Disjoint Z
  st_scr : (stR s₀).Disjoint Z
  ret_st : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint (stR s₀)
  ret_scr : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint Z
  stk_sch : (stkR s₀).Disjoint (schR s₀)
  stk_data : (stkR s₀).Disjoint (dataR s₀)
  stk_st : (stkR s₀).Disjoint (stR s₀)
  stk_scr : (stkR s₀).Disjoint Z
  st_wrap : (St s₀).toNat + 16 ≤ 2 ^ 64
  data_wrap : (Dp s₀).toNat + 16 * N s₀ ≤ 2 ^ 64
  /-- The counter block and the registers saved, at `S + 2048`, are in `Z`. -/
  cIn : ∀ {d n : Nat}, 2048 ≤ d → d + n ≤ 2112 → Z.Contains (S s₀ + BitVec.ofNat 64 d) n
  rounds : R s₀ = 10 ∨ R s₀ = 12 ∨ R s₀ = 14

theorem UPre.of {s₀ : State} (h : updateX86_64.pre s₀) : UPre s₀ (scrR s₀) :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, _, q⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o,
    fun _ h₂ => Offset.contains_base _ (by omega_using [h₂]) (by omega_using [h₂]), q⟩

theorem UPre.ofS {s₀ : State} (h : updateX86_64S.pre s₀) : UPre s₀ ⟨S s₀ + BitVec.ofNat 64 512, 1664⟩ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, _, q⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o,
    fun h₁ h₂ => Offset.contains _ (by omega_using [h₁]) (by omega_using [h₂]) (by decide), q⟩

/-- An access within a region, as a region, lies in it. -/
theorem sub_of_contains {Z : Region} {p : Addr} {n : Nat} (h : Z.Contains p n) : Region.Sub ⟨p, n⟩ Z :=
  fun a ha => by
    simp only [Region.Contains] at ha h ⊢
    rw [show a - Z.base = (a - p) + (p - Z.base) by rw [Offset.sub_add_sub_cancel], BitVec.toNat_add]
    have := Nat.mod_le ((a - p).toNat + (p - Z.base).toNat) (2 ^ 64)
    omega_using [h, ha]

/-- The loop invariant, after `k` blocks, with the part `X` of the scratch
buffer the calls of `vg_aes_ctr32` may write. -/
structure LInv (s₀ : State) (X : Region) (k : Nat) (s : State) : Prop where
  rbx : s.gpr .rbx = W s₀
  rbp : s.gpr .rbp = s₀.gpr .rsi
  r12 : s.gpr .r12 = St s₀
  r13 : s.gpr .r13 = Dp s₀ + BitVec.ofNat 64 (16 * k)
  r14 : s.gpr .r14 = BitVec.ofNat 64 (N s₀ - k)
  r15 : s.gpr .r15 = S s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR s₀, ⟨S s₀ + BitVec.ofNat 64 2048, 16⟩, X, stkR s₀] (savedMem s₀) s.mem
  state : Spec.Aes.bytesAt s.mem (St s₀) 16 =
    Spec.Cmac.chain (ciph s₀) (Spec.Aes.bytesAt s₀.mem (St s₀) 16) ((blks s₀).take k)

/-! ## Regions -/

section
variable {s₀ : State}

/-- A part of the counter block and the registers saved is in `Z`. -/
theorem UPre.cSub {Z : Region} (hp : UPre s₀ Z) {d n : Nat} (h₁ : 2048 ≤ d) (h₂ : d + n ≤ 2112) :
    Region.Sub ⟨S s₀ + BitVec.ofNat 64 d, n⟩ Z :=
  sub_of_contains (hp.cIn h₁ h₂)

/-- What the writable part of the scratch buffer is apart from, at a call. -/
theorem UPre.scrPre {Z : Region} (hp : UPre s₀ Z) {s : State} (rsp : s.gpr .rsp = s₀.gpr .rsp)
    (wr : s.wr = s₀.wr) : ScrPre s (W s₀) (St s₀) Z :=
  ⟨hp.sch_scr, hp.st_scr, by rw [rsp]; exact hp.stk_scr, by
    rw [wr, hp.wr]; exact Covers.of_mem fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]⟩

theorem UPre.data_sub {k : Nat} (hk : k < N s₀) :
    Region.Sub ⟨Dp s₀ + BitVec.ofNat 64 (16 * k), 16⟩ (dataR s₀) :=
  Offset.sub_base _ (by omega_using [hk])

end

theorem slot_contains (b : Addr) {d : Nat} (h₁ : 2064 ≤ d) (h₂ : d + 8 ≤ 2112) :
    (⟨b + BitVec.ofNat 64 2064, 48⟩ : Region).Contains (b + BitVec.ofNat 64 d) 8 := by
  rw [show b + BitVec.ofNat 64 d = (b + BitVec.ofNat 64 2064) + BitVec.ofNat 64 (d - 2064) from
    (Offset.add_add_eq b (by omega_using [h₁])).symm]
  exact Offset.contains_base _ (by omega_using [h₂]) (by omega_using [h₂])

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
  rw [List.take_add_one, List.getElem?_eq_getElem (by simp [Spec.Cmac.blocksAt]; omega_using [hk])]
  simp [Spec.Cmac.blocksAt]

theorem in_rw {rs : List Region} {r : Region} (hr : r ∈ rs) {a : Addr} {n : Nat} (hc : r.Contains a n) :
    InRegions rs a n := ⟨r, hr, hc⟩

/-! ## Memory outside the writable regions -/

/-- The regions the function writes. -/
abbrev Big (s₀ : State) (Z : Region) : List Region := [stR s₀, Z, stkR s₀]

section
variable {s₀ : State} {Z : Region} (hp : UPre s₀ Z)
include hp

theorem UPre.sched_bytes {m : Mem} (hf : Frame (Big s₀ Z) s₀.mem m) :
    Spec.Aes.bytesAt m (W s₀) (16 * (R s₀ + 1)) = Spec.Aes.bytesAt s₀.mem (W s₀) (16 * (R s₀ + 1)) := by
  have hR : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega_using [h]
  refine bytesAt_frame hf (fun r hr => ?_) (by omega_using [hR])
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.sch_st.sub_left (Region.sub_prefix hR)
  · exact hp.sch_scr.sub_left (Region.sub_prefix hR)
  · exact hp.stk_sch.symm.sub_left (Region.sub_prefix hR)

theorem UPre.block_bytes {m : Mem} (hf : Frame (Big s₀ Z) s₀.mem m) {k : Nat} (hk : k < N s₀) :
    Spec.Aes.bytesAt m (Dp s₀ + BitVec.ofNat 64 (16 * k)) 16 =
      Spec.Aes.bytesAt s₀.mem (Dp s₀ + BitVec.ofNat 64 (16 * k)) 16 := by
  refine bytesAt_frame hf (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.data_st.sub_left (UPre.data_sub hk)
  · exact hp.data_scr.sub_left (UPre.data_sub hk)
  · exact hp.stk_data.symm.sub_left (UPre.data_sub hk)

theorem UPre.big_of {X : Region} (hX : Region.Sub X Z) {m : Mem}
    (hf : Frame [stR s₀, ⟨S s₀ + BitVec.ofNat 64 2048, 16⟩, X, stkR s₀] (savedMem s₀) m) :
    Frame (Big s₀ Z) s₀.mem m := by
  have f₀ : Frame (Big s₀ Z) s₀.mem (savedMem s₀) :=
    (savedMem_frame s₀).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨Z, by simp, hp.cSub (by decide) (by decide)⟩
  exact f₀.trans (hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨stR s₀, by simp, fun _ h => h⟩
    · exact ⟨Z, by simp, hp.cSub (by decide) (by decide)⟩
    · exact ⟨Z, by simp, hX⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩)

end

/-! ## One block -/

/-- What the code before the call leaves. -/
structure BodyA (s₀ : State) (k : Nat) (s s₁ : State) : Prop where
  pre : CallPreF s₁ (W s₀) (S s₀ + BitVec.ofNat 64 2048) (St s₀) (S s₀) (R s₀)
  saved : ∀ r ∈ calleeSaved, s₁.gpr r = s.gpr r
  mem : s₁.mem = chainMem s.mem (S s₀ + BitVec.ofNat 64 2048) (St s₀) (Dp s₀ + BitVec.ofNat 64 (16 * k))
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

theorem bodyA_wp {s₀ : State} {Z X : Region} (hp : UPre s₀ Z) {k : Nat} (hk : k < N s₀) {s : State}
    (h : LInv s₀ X k s) : WP isa (.block (chainIn ++ updArgs)) s (BodyA s₀ k s) := by
  have hRegs : s.rd ++ s.wr = [schR s₀, dataR s₀, stR s₀, Z] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have hW : s.wr = [stR s₀, Z] := by rw [h.wr, hp.wr]
  have h16k : 16 * k + 16 ≤ 16 * N s₀ := by omega_using [hk]
  have hdw := hp.data_wrap
  have cSt0 : (stR s₀).Contains (St s₀) 8 := by
    simpa using Offset.contains_base (St s₀) (d := 0) (n := 8) (k := 16) (by decide) (by decide)
  have cSt8 : (stR s₀).Contains (St s₀ + BitVec.ofNat 64 8) 8 := Offset.contains_base _ (by decide) (by decide)
  have cQ0 : (dataR s₀).Contains (Dp s₀ + BitVec.ofNat 64 (16 * k)) 8 :=
    Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk, hdw])
  have cQ8 : (dataR s₀).Contains (Dp s₀ + BitVec.ofNat 64 (16 * k) + BitVec.ofNat 64 8) 8 := by
    rw [Offset.add_add]; exact Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk, hdw])
  have cC0 : Z.Contains (S s₀ + BitVec.ofNat 64 2048) 8 := hp.cIn (by decide) (by decide)
  have cC8 : Z.Contains (S s₀ + BitVec.ofNat 64 2048 + BitVec.ofNat 64 8) 8 := by
    rw [Offset.add_add]; exact hp.cIn (by decide) (by decide)
  obtain ⟨s₁, run₁, rdi₁, rsi₁, rdx₁, rcx₁, r8₁, r9₁, cs₁, mem₁, rd₁, wr₁⟩ :=
    chainIn_ok s (C := S s₀ + BitVec.ofNat 64 2048) (P := St s₀) (Q := Dp s₀ + BitVec.ofNat 64 (16 * k))
      (by rw [h.r15]) h.r12 h.r13
      (by rw [hRegs]; exact in_rw (by simp) cSt0) (by rw [hRegs]; exact in_rw (by simp) cSt8)
      (by rw [hRegs]; exact in_rw (by simp) cQ0) (by rw [hRegs]; exact in_rw (by simp) cQ8)
      (by rw [hW]; exact in_rw (by simp) cC0) (by rw [hW]; exact in_rw (by simp) cC8)
      (by rw [hW]; exact in_rw (by simp) cSt0) (by rw [hW]; exact in_rw (by simp) cSt8)
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := by rw [cs₁ .rsp (by simp [calleeSaved]), h.rsp]
  have hR : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega_using [h]
  have cZ : Region.Sub ⟨S s₀ + BitVec.ofNat 64 2048, 16⟩ Z := hp.cSub (by decide) (by decide)
  have pre : CallPreF s₁ (W s₀) (S s₀ + BitVec.ofNat 64 2048) (St s₀) (S s₀) (R s₀) :=
    { rdi := by rw [rdi₁, h.rbx]
      rsi := by rw [rsi₁, h.rbp, rsi_ofNat]
      rdx := rdx₁
      rcx := rcx₁
      r8 := r8₁
      r9 := by rw [r9₁, h.r15]
      rounds := hp.rounds
      wc := hp.sch_scr.sub_right cZ
      wd := hp.sch_st
      cd := hp.st_scr.symm.sub_left cZ
      stkW := by rw [rsp₁]; exact hp.stk_sch
      stkC := by rw [rsp₁]; exact hp.stk_scr.sub_right cZ
      stkD := by rw [rsp₁]; exact hp.stk_st
      wrap := hp.st_wrap
      reads := by
        rw [rd₁, wr₁, hRegs]
        exact Covers.cons (Covers.of_mem fun r hr => by simp only [List.mem_singleton] at hr; simp [hr])
          (Covers.cons (Covers.one ⟨Z, by simp, hp.cIn (by decide) (by decide)⟩)
            (Covers.cons (Covers.of_mem fun r hr => by simp only [List.mem_singleton] at hr; simp [hr])
              Covers.nil))
      writes := by
        rw [wr₁, hW]
        exact Covers.cons (Covers.one ⟨Z, by simp, hp.cIn (by decide) (by decide)⟩)
          (Covers.cons (Covers.of_mem fun r hr => by simp only [List.mem_singleton] at hr; simp [hr])
            Covers.nil)
      zero := by rw [mem₁]; exact chainMem_state _ _ _ _ }
  exact ⟨pre, cs₁, mem₁, rd₁, wr₁⟩

theorem body_ok {c : Impl.Aes.X86_64.Ctr32} {Z X : Addr → Region} (T : AesCall c Z X) {s₀ : State}
    (hp : UPre s₀ (Z (S s₀))) {k : Nat} (hk : k < N s₀) {s : State} (h : LInv s₀ (X (S s₀)) k s) :
    WP isa (body c) s fun s' =>
      LInv s₀ (X (S s₀)) (k + 1) s' ∧ s'.zf = some (decide (N s₀ - (k + 1) = 0)) := by
  have h16k : 16 * k + 16 ≤ 16 * N s₀ := by omega_using [hk]
  have hdw := hp.data_wrap
  refine WP.seq (WP.mono (bodyA_wp hp hk h) fun s₁ ⟨pre, cs₁, mem₁, rd₁, wr₁⟩ => ?_)
  have rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := by rw [cs₁ .rsp (by simp [calleeSaved]), h.rsp]
  refine WP.seq (WP.mono (T.ok pre (hp.scrPre rsp₁ (by rw [wr₁, h.wr]))) fun s₂ h₂ => ?_)
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
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega_using [hk])]; rfl
  -- Memory.
  have cZ : Region.Sub ⟨S s₀ + BitVec.ofNat 64 2048, 16⟩ (Z (S s₀)) := hp.cSub (by decide) (by decide)
  have bigS := hp.big_of (T.sub _) h.frame
  have f₁ : Frame [⟨S s₀ + BitVec.ofNat 64 2048, 16⟩, ⟨St s₀, 16⟩] s.mem s₁.mem := by
    rw [mem₁]; exact chainMem_frame _ _ _ _
  have big₁ : Frame (Big s₀ (Z (S s₀))) s₀.mem s₁.mem := bigS.trans (f₁.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨Z (S s₀), by simp, cZ⟩
    · exact ⟨stR s₀, by simp, fun _ h => h⟩)
  have cst : (⟨S s₀ + BitVec.ofNat 64 2048, 16⟩ : Region).Disjoint (stR s₀) :=
    hp.st_scr.symm.sub_left cZ
  have cq : (⟨S s₀ + BitVec.ofNat 64 2048, 16⟩ : Region).Disjoint ⟨Dp s₀ + BitVec.ofNat 64 (16 * k), 16⟩ :=
    (hp.data_scr.symm.sub_left cZ).sub_right (UPre.data_sub hk)
  have out := h₂.out
  rw [UPre.sched_bytes hp big₁, mem₁, chainMem_counter _ cst cq, h.state,
    UPre.block_bytes hp bigS hk] at out
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [g .rbx (by simp [calleeSaved]) (by decide) (by decide), h.rbx]
  · rw [g .rbp (by simp [calleeSaved]) (by decide) (by decide), h.rbp]
  · rw [g .r12 (by simp [calleeSaved]) (by decide) (by decide), h.r12]
  · rw [r13₃, r13₂, Offset.add_add_eq _ (c := 16 * (k + 1)) (by omega_using [])]
  · rw [r14₃, r14₂, dec]
  · rw [g .r15 (by simp [calleeSaved]) (by decide) (by decide), h.r15]
  · rw [g .rsp (by simp [calleeSaved]) (by decide) (by decide), h.rsp]
  · rw [rd₃, h₂.rd, rd₁, h.rd]
  · rw [wr₃, h₂.wr, wr₁, h.wr]
  · rw [mem₃]
    refine h.frame.trans ((f₁.sub fun r hr => ?_).trans (h₂.frame.sub fun r hr => ?_))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨stR s₀, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨S s₀ + BitVec.ofNat 64 2048, 16⟩, by simp, fun _ h => h⟩
      · exact ⟨stR s₀, by simp, fun _ h => h⟩
      · exact ⟨X (S s₀), by simp, fun _ h => h⟩
      · exact ⟨stkR s₀, by simp, by rw [rsp₁]; exact fun _ h => h⟩
  · rw [mem₃, out, take_succ_blks s₀ hk, Proof.Cmac.chain_append, Proof.Cmac.chain_single]
  · rw [zf₃, r14₂, dec]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    constructor
    · intro he
      have := congrArg BitVec.toNat he
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hdw])] at this
      simpa using this
    · intro he; rw [he]; rfl

end VG.Proof.CmacAes.X86_64

end

end

/-!
# AES-CMAC on x86-64: `vg_cmac_aes_update` is correct

For any call of `vg_aes_ctr32` and the part of the scratch buffer it leaves
writable (`AesCall`, `update_wpG`): all of the buffer, with any
implementation (`update_wp`), or all but its first 512 bytes, with one that
uses 1480 bytes of working space (`updateS_wp`).
-/

@[expose] public section

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

theorem loop_ok {c : Impl.Aes.X86_64.Ctr32} {Z X : Addr → Region} (T : AesCall c Z X) {s₀ : State}
    (hp : UPre s₀ (Z (S s₀))) {k : Nat} (hk : k < N s₀) {s : State} (h : LInv s₀ (X (S s₀)) k s) :
    WP isa (.loop (body c) .ne) s (LInv s₀ (X (S s₀)) (N s₀)) := by
  refine WP.loop (M := isa) (body := body c) (c := .ne) (Q := LInv s₀ (X (S s₀)) (N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = N s₀ - j ∧ j < N s₀ ∧ LInv s₀ (X (S s₀)) j t) ?_ (N s₀ - k) s
    ⟨k, rfl, hk, h⟩
  rintro n s ⟨k, rfl, hk, h⟩
  refine WP.mono (body_ok T hp hk h) fun s' ⟨h', zf'⟩ => ?_
  by_cases hz : N s₀ - (k + 1) = 0
  · left
    refine ⟨by simp [eval, zf', hz], ?_⟩
    rwa [show N s₀ = k + 1 by omega_using [hk, hz]]
  · right
    refine ⟨by simp [eval, zf', hz], N s₀ - (k + 1), by omega_using [hk], k + 1, rfl, by omega_using [hz], h'⟩

/-! ## Saving and restoring the registers -/

theorem readW_writeW_other (m : Mem) (b : Addr) {d e : Nat} (v : BitVec 64) (h : d + 8 ≤ e ∨ e + 8 ≤ d)
    (hd : d + 8 ≤ 2 ^ 64) (he : e + 8 ≤ 2 ^ 64) :
    (m.writeW (b + BitVec.ofNat 64 e) v).readW (b + BitVec.ofNat 64 d) 64 = m.readW (b + BitVec.ofNat 64 d) 64 :=
  Mem.readW_writeW_sep (Offset.sep b h hd he) (by decide)

/-! ## The whole function -/

theorem r8_ofNat (s₀ : State) : s₀.gpr .r8 = BitVec.ofNat 64 (N s₀) := by
  apply BitVec.eq_of_toNat_eq; simp [N]

theorem slots_disj {s₀ : State} {Z X : Region} (hp : UPre s₀ Z)
    (hX : (⟨S s₀ + BitVec.ofNat 64 2048, 128⟩ : Region).Disjoint X) :
    ∀ r ∈ [stR s₀, ⟨S s₀ + BitVec.ofNat 64 2048, 16⟩, X, stkR s₀],
      (⟨S s₀ + BitVec.ofNat 64 2064, 48⟩ : Region).Disjoint r := by
  have sl : Region.Sub ⟨S s₀ + BitVec.ofNat 64 2064, 48⟩ Z := hp.cSub (by decide) (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.st_scr.symm.sub_left sl
  · exact Offset.disjoint _ (by decide) (by decide) (by decide)
  · exact hX.sub_left (Offset.sub _ (by decide) (by decide))
  · exact hp.stk_scr.symm.sub_left sl

theorem slot_read {s₀ : State} {Z X : Region} (hp : UPre s₀ Z)
    (hX : (⟨S s₀ + BitVec.ofNat 64 2048, 128⟩ : Region).Disjoint X) {m : Mem}
    (hf : Frame [stR s₀, ⟨S s₀ + BitVec.ofNat 64 2048, 16⟩, X, stkR s₀] (savedMem s₀) m) {d : Nat}
    (h₁ : 2064 ≤ d) (h₂ : d + 8 ≤ 2112) :
    m.readW (S s₀ + BitVec.ofNat 64 d) 64 = (savedMem s₀).readW (S s₀ + BitVec.ofNat 64 d) 64 :=
  hf.readW (r := ⟨S s₀ + BitVec.ofNat 64 2064, 48⟩) (slot_contains _ h₁ h₂) (slots_disj hp hX) (by decide)

theorem prologue_wp {s₀ : State} {Z X : Region} (hp : UPre s₀ Z) :
    WP isa (.block (save ++ setup)) s₀ fun s₁ => LInv s₀ X 0 s₁ ∧ s₁.zf = some (decide (N s₀ = 0)) := by
  have hN := (s₀.gpr .r8).isLt
  obtain ⟨s₁, run₁, rbx₁, rbp₁, r12₁, r13₁, r14₁, r15₁, rsp₁, zf₁, mem₁, rd₁, wr₁⟩ :=
    prologue_ok s₀ fun d h₁ h₂ => by
      rw [hp.wr]; exact in_rw (r := Z) (by simp) (hp.cIn (by omega_using [h₁]) h₂)
  refine WP.of_runBlock ⟨s₁, run₁, ?_, ?_⟩
  · have stSaved : Spec.Aes.bytesAt (savedMem s₀) (St s₀) 16 = Spec.Aes.bytesAt s₀.mem (St s₀) 16 :=
      bytesAt_frame' (savedMem_frame s₀) fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.st_scr.sub_right (hp.cSub (by decide) (by decide))
    exact { rbx := rbx₁, rbp := rbp₁, r12 := r12₁
            r13 := by rw [r13₁]; simp
            r14 := by rw [r14₁, r8_ofNat]; rfl
            r15 := r15₁, rsp := rsp₁, rd := rd₁, wr := wr₁
            frame := by rw [mem₁]; exact Frame.refl _ _
            state := by rw [mem₁, stSaved]; rfl }
  · rw [zf₁, r8_ofNat, beq_zero hN]

theorem mid_wp {c : Impl.Aes.X86_64.Ctr32} {Z X : Addr → Region} (T : AesCall c Z X) {s₀ : State}
    (hp : UPre s₀ (Z (S s₀))) {s₁ : State} (h : LInv s₀ (X (S s₀)) 0 s₁)
    (hz : s₁.zf = some (decide (N s₀ = 0))) :
    WP isa (.ite .e (.block []) (.loop (body c) .ne)) s₁ (LInv s₀ (X (S s₀)) (N s₀)) := by
  have ev : isa.eval .e s₁ = some (decide (N s₀ = 0)) := hz
  by_cases hn : N s₀ = 0
  · refine WP.ite true (by rw [ev, hn]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    rw [hn]; exact h
  · refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
    exact loop_ok T hp (by omega_using [hn]) h

theorem epilogue_wp {s₀ : State} {Z X : Region} (hp : UPre s₀ Z) (hX : Region.Sub X Z)
    (hXd : (⟨S s₀ + BitVec.ofNat 64 2048, 128⟩ : Region).Disjoint X) {s₂ : State}
    (h₂ : LInv s₀ X (N s₀) s₂) :
    WP isa (.block restore) s₂ fun s' => gprPreserved s₀ s' ∧ updateX86_64.post s₀ s' := by
  have rdwr : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [h₂.rd, h₂.wr]
  have hsv : Spill.Saved s₂.mem (s₂.gpr .r15) s₀.gpr saved := fun p hp' => by
    have := saved_bound p hp'
    rw [h₂.r15, slot_read hp hXd h₂.frame this.1 this.2]
    exact Spill.saveMem_saved _ _ _ _ (by decide) p hp'
  refine WP.mono (Spill.restore_ok .r15 saved s₀.gpr s₂ (by decide) (fun p hp' => ?_) hsv)
    fun s₃ ⟨g₁, g₂, mem₃, _⟩ => ⟨⟨Spill.calleeSaved_ok g₁ g₂ (by decide) h₂.rsp, ?_⟩, ?_⟩
  · have := saved_bound p hp'
    rw [rdwr, hp.rd, hp.wr, h₂.r15]
    exact in_rw (r := Z) (by simp) (hp.cIn (by omega_using [this]) this.2)
  · rw [mem₃]
    refine (hp.big_of hX h₂.frame).readW (r := ⟨s₀.gpr .rsp, 8⟩) (Region.contains_self _ _)
      (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.ret_st
    · exact hp.ret_scr
    · exact Offset.base_disjoint_below _ (by decide)
  · show Spec.Aes.bytesAt s₃.mem (St s₀) 16 = Spec.Cmac.chain (ciph s₀) _ (blks s₀)
    rw [mem₃, h₂.state, List.take_of_length_le (by simp [Spec.Cmac.blocksAt])]

/-- `update` over the call `T` of `vg_aes_ctr32`, with the part `Z` of the
scratch buffer writable. -/
theorem update_wpG {c : Impl.Aes.X86_64.Ctr32} {Z X : Addr → Region} (T : AesCall c Z X) {s₀ : State}
    (hp : UPre s₀ (Z (S s₀))) :
    WP isa (update c) s₀ fun s' => gprPreserved s₀ s' ∧ updateX86_64.post s₀ s' :=
  WP.seq (WP.mono (prologue_wp hp) fun _ ⟨h₁, z₁⟩ =>
    WP.seq (WP.mono (mid_wp T hp h₁ z₁) fun _ h₂ => epilogue_wp hp (T.sub _) (T.disj _) h₂))

theorem update_wp (v : Ctr32Impl) {s₀ : State} (h0 : updateX86_64.pre s₀) :
    WP isa (update v.callee) s₀ fun s' => gprPreserved s₀ s' ∧ updateX86_64.post s₀ s' :=
  update_wpG (AesCall.base v) (UPre.of h0)

/-- `update_wp`, over an implementation of `vg_aes_ctr32` that uses 1480
bytes of working space: the first 512 bytes of the scratch buffer are not
written. -/
theorem updateS_wp (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Small v.callee) {s₀ : State}
    (h0 : updateX86_64S.pre s₀) :
    WP isa (update v.callee) s₀ fun s' => gprPreserved s₀ s' ∧ updateX86_64S.post s₀ s' :=
  update_wpG (AesCall.small v f) (UPre.ofS h0)

end VG.Proof.CmacAes.X86_64
