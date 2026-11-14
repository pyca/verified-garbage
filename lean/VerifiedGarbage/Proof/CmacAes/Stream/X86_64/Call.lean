module

import VerifiedGarbage.Proof.Framework.OffsetBelow
public import VerifiedGarbage.Proof.CmacAes.X86_64.Variant
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Aes.X86_64.AesNi.ExpandKey

@[expose] public section

section

/-!
# Streaming AES-CMAC on x86-64: the contracts the proofs are written against

The artifacts' contracts are the shared ones of `Spec/Cmac/Contract.lean`,
which imply these (`Verified.lean`). Each function calls functions that call
`vg_aes_ctr32`: the two return addresses are in the 16 bytes below the stack
pointer, which may not overlap any buffer.
-/

namespace VG.Proof.CmacAes.Stream.X86_64

open VG VG.X86_64

/-- `vg_cmac_aes_init(state = rdi, key = rsi, key_len = rdx, scratch = rcx)`. -/
def initX86_64 : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 304⟩
    let key : Region := ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩
    let scr : Region := ⟨s.gpr .rcx, 2304⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack := below (s.gpr .rsp) 16
    16 ≤ (s.gpr .rsp).toNat ∧ s.rd = [key] ∧ s.wr = [state, scr] ∧
      state.Disjoint key ∧ state.Disjoint scr ∧ key.Disjoint scr ∧
      ret.Disjoint state ∧ ret.Disjoint key ∧ ret.Disjoint scr ∧
      stack.Disjoint state ∧ stack.Disjoint key ∧ stack.Disjoint scr ∧
      (s.gpr .rdi).toNat + 304 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + (s.gpr .rdx).toNat ≤ 2 ^ 64 ∧
      (s.gpr .rcx).toNat + 2304 ≤ 2 ^ 64 ∧
      ((s.gpr .rdx).toNat = 16 ∨ (s.gpr .rdx).toNat = 24 ∨ (s.gpr .rdx).toNat = 32)
  post s s' :=
    Spec.Cmac.Repr s'.mem (s.gpr .rdi) (Spec.Aes.bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat) []
  pub s₁ s₂ :=
    s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
      s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx

/-- `vg_cmac_aes_absorb(state = rdi, rounds = rsi, count = rdx, data = rcx, len = r8, scratch = r9)`. -/
def absorbX86_64 : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 304⟩
    let data : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
    let scr : Region := ⟨s.gpr .r9, 2304⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack := below (s.gpr .rsp) 16
    16 ≤ (s.gpr .rsp).toNat ∧ s.rd = [data] ∧ s.wr = [state, scr] ∧
      state.Disjoint data ∧ state.Disjoint scr ∧ data.Disjoint scr ∧
      ret.Disjoint state ∧ ret.Disjoint data ∧ ret.Disjoint scr ∧
      stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scr ∧
      (s.gpr .rdi).toNat + 304 ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r9).toNat + 2304 ≤ 2 ^ 64 ∧
      ((s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14)
  post s s' :=
    ∀ key msg, Spec.Cmac.Repr s.mem (s.gpr .rdi) key msg →
      (s.gpr .rsi).toNat = Spec.Aes.rounds (key.length / 4) →
      s.gpr .rdx = BitVec.ofNat 64 msg.length → msg.length + (s.gpr .r8).toNat < 2 ^ 64 →
      Spec.Cmac.Repr s'.mem (s.gpr .rdi) key
        (msg ++ Spec.Aes.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
      s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
      s₁.gpr .r9 = s₂.gpr .r9

/-- `vg_cmac_aes_finish(state = rdi, rounds = rsi, count = rdx, out = rcx, scratch = r8)`. -/
def finishX86_64 : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 304⟩
    let out : Region := ⟨s.gpr .rcx, 16⟩
    let scr : Region := ⟨s.gpr .r8, 2304⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack := below (s.gpr .rsp) 16
    16 ≤ (s.gpr .rsp).toNat ∧ s.rd = [] ∧ s.wr = [state, out, scr] ∧
      state.Disjoint out ∧ state.Disjoint scr ∧ out.Disjoint scr ∧
      ret.Disjoint state ∧ ret.Disjoint out ∧ ret.Disjoint scr ∧
      stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scr ∧
      (s.gpr .rdi).toNat + 304 ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + 16 ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + 2304 ≤ 2 ^ 64 ∧
      ((s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14)
  post s s' :=
    ∀ key msg, Spec.Cmac.Repr s.mem (s.gpr .rdi) key msg →
      (s.gpr .rsi).toNat = Spec.Aes.rounds (key.length / 4) →
      s.gpr .rdx = BitVec.ofNat 64 msg.length → msg.length < 2 ^ 64 →
      Spec.Aes.bytesAt s'.mem (s.gpr .rcx) 16 = Spec.Cmac.aesCmac key 16 msg
  pub s₁ s₂ :=
    s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
      s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8


/-- `finishX86_64` over an implementation of `vg_aes_ctr32` that needs no
working space: `scratch` is the 16 bytes of `vg_cmac_aes_finalize`'s counter
block (`finishF`). -/
def finishX86_64F : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 304⟩
    let out : Region := ⟨s.gpr .rcx, 16⟩
    let scr : Region := ⟨s.gpr .r8, 16⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack := below (s.gpr .rsp) 16
    16 ≤ (s.gpr .rsp).toNat ∧ s.rd = [] ∧ s.wr = [state, out, scr] ∧
      state.Disjoint out ∧ state.Disjoint scr ∧ out.Disjoint scr ∧
      ret.Disjoint state ∧ ret.Disjoint out ∧ ret.Disjoint scr ∧
      stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scr ∧
      (s.gpr .rdi).toNat + 304 ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + 16 ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + 16 ≤ 2 ^ 64 ∧
      ((s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14)
  post := finishX86_64.post
  pub := finishX86_64.pub
end VG.Proof.CmacAes.Stream.X86_64

end

/-!
# Streaming AES-CMAC on x86-64: the calls

A call of each function the streaming functions call (`vg_aes_expand_key_scratch`,
`vg_cmac_aes_subkeys` and `vg_cmac_aes_finalize`, for any implementation of
AES, and `vg_cmac_aes_update`, for any of its implementations, `UpdateImpl`),
from its contract (with `WP.call`): what it needs (`…Args`), what it leaves
(`…Post`, in terms of the memory before the call), and that two calls with
the same arguments leak the same (`…_rel`). Each callee's stack is in the 16
bytes below the stack pointer (`below sp 16`): its return address, and that
of the call of `vg_aes_ctr32` it makes, if it makes one.
-/

namespace VG.Proof.CmacAes.Stream.X86_64

open VG VG.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.CmacAes.X86_64 (UpdateImpl UpdateFree updateX86_64 updateX86_64F subkeysX86_64 subkeysX86_64F subkeysF_correct subkeysF_ct
  finalizeX86_64 finalizeX86_64F finalizeF_correct finalizeF_ct subkeys_correct
  finalize_correct subkeys_ct finalize_ct callEntry_frame bytesAt_frame toNat_rounds)

/-! ## The stack -/

theorem ret_sub (sp : Addr) : Region.Sub ⟨sp - 8, 8⟩ (below sp 16) :=
  Offset.sub_below sp (a := 8) (b := 16) (by decide) (by decide)

theorem stk_sub (sp : Addr) : Region.Sub (below (sp - 8) 8) (below sp 16) := by
  show Region.Sub ⟨sp - BitVec.ofNat 64 8 - BitVec.ofNat 64 8, 8⟩ _
  rw [Offset.sub_sub_ofNat]
  exact Offset.sub_below sp (a := 16) (b := 16) (by decide) (by decide)

theorem below8_sub (sp : Addr) : Region.Sub (below sp 8) (below sp 16) :=
  Offset.sub_below sp (a := 8) (b := 16) (by decide) (by decide)

/-- The bytes of a region the stack does not overlap, once a call has
stored its return address. -/
theorem callEntry_bytes (s : State) {p : Addr} {n : Nat} (h : (below (s.gpr .rsp) 16).Disjoint ⟨p, n⟩)
    (hn : n ≤ 2 ^ 64) : Spec.Aes.bytesAt s.callEntry.mem p n = Spec.Aes.bytesAt s.mem p n :=
  bytesAt_frame (callEntry_frame s) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (h.sub_left (below8_sub _)).symm) hn

theorem toNat_ofNat {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-- An offset from `p - a`, from `p`. -/
theorem sub_add_ofNat (p : Addr) {a d : Nat} (h : a ≤ d) :
    p - BitVec.ofNat 64 a + BitVec.ofNat 64 d = p + BitVec.ofNat 64 (d - a) := by
  rw [show BitVec.ofNat 64 d = BitVec.ofNat 64 a + BitVec.ofNat 64 (d - a) by
    rw [BitVec.ofNat_add_ofNat, Nat.add_sub_cancel' h], ← BitVec.add_assoc, BitVec.sub_add_cancel]

/-! ## No writes of `rsp` -/

theorem nosp_of_all {c : Prog isa} (h : c.allInstrs (fun i => !Taint.clobbers i .rsp) = true) : NoSp c := by
  rw [Code.allInstrs_eq] at h
  exact fun i hi => by simpa using List.all_eq_true.mp h i hi

theorem all_of_nosp {c : Prog isa} (h : NoSp c) : c.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by
  rw [Code.allInstrs_eq, List.all_eq_true]
  exact fun i hi => by simp [h i hi]

/-! ## `vg_cmac_aes_update` -/

/-- What a call of `vg_cmac_aes_update` needs: the key schedule `W`, the
chaining value `C`, `n` blocks at `D`, the working space `S` and the rounds
`R`. -/
structure UArgs (s : State) (W C D S : Addr) (R n : Nat) : Prop where
  rdi : s.gpr .rdi = W
  rsi : s.gpr .rsi = BitVec.ofNat 64 R
  rdx : s.gpr .rdx = C
  rcx : s.gpr .rcx = D
  r8 : s.gpr .r8 = BitVec.ofNat 64 n
  r9 : s.gpr .r9 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  hn : 16 * n < 2 ^ 64
  wc : (⟨W, 240⟩ : Region).Disjoint ⟨C, 16⟩
  ws : (⟨W, 240⟩ : Region).Disjoint ⟨S, 2176⟩
  dc : (⟨D, 16 * n⟩ : Region).Disjoint ⟨C, 16⟩
  ds : (⟨D, 16 * n⟩ : Region).Disjoint ⟨S, 2176⟩
  cs : (⟨C, 16⟩ : Region).Disjoint ⟨S, 2176⟩
  stkW : (below (s.gpr .rsp) 16).Disjoint ⟨W, 240⟩
  stkD : (below (s.gpr .rsp) 16).Disjoint ⟨D, 16 * n⟩
  stkC : (below (s.gpr .rsp) 16).Disjoint ⟨C, 16⟩
  stkS : (below (s.gpr .rsp) 16).Disjoint ⟨S, 2176⟩
  wrapC : C.toNat + 16 ≤ 2 ^ 64
  wrapD : D.toNat + 16 * n ≤ 2 ^ 64
  wrapS : S.toNat + 2176 ≤ 2 ^ 64
  reads : Covers ([⟨W, 240⟩, ⟨D, 16 * n⟩] ++ [⟨C, 16⟩, ⟨S, 2176⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨C, 16⟩, ⟨S, 2176⟩] s.wr

/-- What a call of `vg_cmac_aes_update` leaves. -/
structure UPost (s : State) (W C D S : Addr) (R n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨C, 16⟩, ⟨S, 2176⟩, below (s.gpr .rsp) 16] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem C 16 =
    Spec.Cmac.chain (Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem W (16 * (R + 1))))
      (Spec.Aes.bytesAt s.mem C 16) (Spec.Cmac.blocksAt s.mem D 16 n)

theorem UArgs.pre {s : State} {W C D S : Addr} {R n : Nat} (h : UArgs s W C D S R n) :
    updateX86_64.pre (s.callEntry.withRegions [⟨W, 240⟩, ⟨D, 16 * n⟩] [⟨C, 16⟩, ⟨S, 2176⟩]) := by
  have hR := toNat_rounds h.rounds
  have hN := toNat_ofNat (n := n) (by have := h.hn; omega_arith)
  simp only [updateX86_64, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.callEntry_rsp, State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.r9 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, hR, hN]
  exact ⟨trivial, trivial, h.wc, h.ws, h.dc, h.ds, h.cs, h.stkC.sub_left (ret_sub _),
    h.stkS.sub_left (ret_sub _), h.stkW.sub_left (stk_sub _), h.stkD.sub_left (stk_sub _),
    h.stkC.sub_left (stk_sub _), h.stkS.sub_left (stk_sub _), h.wrapC, h.wrapD, h.wrapS, h.rounds⟩

theorem upd_call (v : UpdateImpl) {s : State} {W C D S : Addr} {R n : Nat}
    (h : UArgs s W C D S R n) :
    WP isa (.call v.callee.name v.callee.code) s (UPost s W C D S R n) := by
  have hR := toNat_rounds h.rounds
  have hN := toNat_ofNat (n := n) (by have := h.hn; omega_arith)
  have hd := v.depth
  refine WP.call (k := updateX86_64) v.ok v.nosp (by omega_arith) h.pre h.reads h.writes ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  refine ⟨hrd, hwr, hcs, by simpa using Frame.below_mono hf (b := 16) (by omega_arith) (by decide), ?_⟩
  simp only [updateX86_64, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, h.r8, hR, hN] at hpost
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h | h | h <;> omega_arith
  rw [← hm₂, hpost, X86_64.ciphAt, Proof.Cmac.Stream.blocksAt_eq, Proof.Cmac.Stream.blocksAt_eq,
    callEntry_bytes s (h.stkW.sub_right (Region.sub_prefix hRb)) (by omega_arith),
    callEntry_bytes s h.stkC (by decide), callEntry_bytes s h.stkD (by have := h.hn; omega_arith)]

theorem upd_rel (v : UpdateImpl) {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ W C D S : Addr, ∃ R n : Nat,
      UArgs s₁ W C D S R n ∧ UArgs s₂ W C D S R n ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (.call v.callee.name v.callee.code) fun _ _ => True := by
  refine RelCT.callEx v.ok v.ct fun s₁ s₂ hp => ?_
  obtain ⟨W, C, D, S, R, n, h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨_, _, _, _, h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes, hsp⟩
  simp only [updateX86_64, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.r9 ≠ .rsp),
    h₁.rdi, h₁.rsi, h₁.rdx, h₁.rcx, h₁.r8, h₁.r9, h₂.rdi, h₂.rsi, h₂.rdx, h₂.rcx, h₂.r8, h₂.r9, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## `vg_cmac_aes_update`, for any working space

A caller generic over what its calls of `vg_cmac_aes_update` need of its
working space: its writable part `Z` (in the writable regions), and the part
`X` of it a call may write. Over an implementation that needs working space,
`Z` is the whole of it and `X` the call's (`ACall.base`); over one that needs
none (`UpdateFree`), `Z` is only what the caller writes itself and `X` is
empty (`ACall.free`). -/

/-- What a call of `vg_cmac_aes_update` needs, with `S` its scratch pointer
and `Z` the caller's writable working space. -/
structure UArgsZ (s : State) (W C D S : Addr) (Z : Region) (R n : Nat) : Prop where
  rdi : s.gpr .rdi = W
  rsi : s.gpr .rsi = BitVec.ofNat 64 R
  rdx : s.gpr .rdx = C
  rcx : s.gpr .rcx = D
  r8 : s.gpr .r8 = BitVec.ofNat 64 n
  r9 : s.gpr .r9 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  hn : 16 * n < 2 ^ 64
  wc : (⟨W, 240⟩ : Region).Disjoint ⟨C, 16⟩
  wz : (⟨W, 240⟩ : Region).Disjoint Z
  dc : (⟨D, 16 * n⟩ : Region).Disjoint ⟨C, 16⟩
  dz : (⟨D, 16 * n⟩ : Region).Disjoint Z
  cz : (⟨C, 16⟩ : Region).Disjoint Z
  stkW : (below (s.gpr .rsp) 16).Disjoint ⟨W, 240⟩
  stkD : (below (s.gpr .rsp) 16).Disjoint ⟨D, 16 * n⟩
  stkC : (below (s.gpr .rsp) 16).Disjoint ⟨C, 16⟩
  stkZ : (below (s.gpr .rsp) 16).Disjoint Z
  wrapC : C.toNat + 16 ≤ 2 ^ 64
  wrapD : D.toNat + 16 * n ≤ 2 ^ 64
  wrapZ : Z.base.toNat + Z.len ≤ 2 ^ 64
  reads : Covers ([⟨W, 240⟩, ⟨D, 16 * n⟩] ++ [⟨C, 16⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨C, 16⟩] s.wr
  zw : Covers [Z] s.wr

/-- What a call of `vg_cmac_aes_update` leaves, having written at most `X`
of the working space. -/
structure UPostZ (s : State) (W C D : Addr) (X : Region) (R n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨C, 16⟩, X, below (s.gpr .rsp) 16] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem C 16 =
    Spec.Cmac.chain (Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem W (16 * (R + 1))))
      (Spec.Aes.bytesAt s.mem C 16) (Spec.Cmac.blocksAt s.mem D 16 n)

/-- The calls of `u` from a caller whose writable working space is `Z S`
and whose registers are saved at `S + 2176`, for a scratch pointer `S`: each
writes at most `X S` of it. -/
structure ACall (u : Impl.CmacAes.X86_64.Update) (Z X : Addr → Region) : Prop where
  sub : ∀ S, Region.Sub (X S) (Z S)
  slotX : ∀ S, (⟨S + BitVec.ofNat 64 2176, 48⟩ : Region).Disjoint (X S)
  call : ∀ {s : State} {W C D S : Addr} {R n : Nat}, UArgsZ s W C D S (Z S) R n →
    WP isa (.call u.name u.code) s (UPostZ s W C D (X S) R n)
  rel : ∀ {P : State → State → Prop}, (∀ s₁ s₂, P s₁ s₂ → ∃ W C D S : Addr, ∃ R n : Nat,
      UArgsZ s₁ W C D S (Z S) R n ∧ UArgsZ s₂ W C D S (Z S) R n ∧ s₁.gpr .rsp = s₂.gpr .rsp) →
    RelCT isa P (.call u.name u.code) fun _ _ => True

theorem UArgsZ.base {s : State} {W C D S : Addr} {R n : Nat} (h : UArgsZ s W C D S ⟨S, 2304⟩ R n) :
    UArgs s W C D S R n :=
  have sb : Region.Sub ⟨S, 2176⟩ ⟨S, 2304⟩ := Region.sub_prefix (by decide)
  have zc : Covers [⟨S, 2176⟩] s.wr := Covers.trans (Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨S, 2304⟩, List.mem_singleton_self _, 0, by simp, by simp⟩) h.zw
  { rdi := h.rdi, rsi := h.rsi, rdx := h.rdx, rcx := h.rcx, r8 := h.r8, r9 := h.r9, rounds := h.rounds,
    hn := h.hn, wc := h.wc, ws := h.wz.sub_right sb, dc := h.dc, ds := h.dz.sub_right sb,
    cs := h.cz.sub_right sb, stkW := h.stkW, stkD := h.stkD, stkC := h.stkC, stkS := h.stkZ.sub_right sb,
    wrapC := h.wrapC, wrapD := h.wrapD, wrapS := by have := h.wrapZ; simp only at this; omega_arith
    reads := by
      have := Covers.append h.reads (Covers.right (rd := s.rd) zc)
      exact this.trans (Covers.append_left (Covers.refl _) (Covers.refl _))
    writes := Covers.cons h.writes zc }

/-- Over any implementation, with the whole working space. -/
theorem ACall.base (v : UpdateImpl) : ACall v.callee (fun S => ⟨S, 2304⟩) (fun S => ⟨S, 2176⟩) where
  sub _ := Region.sub_prefix (by decide)
  slotX S := Offset.disjoint_base S (by decide) (by decide)
  call h := WP.mono (upd_call v h.base) fun _ h' => ⟨h'.rd, h'.wr, h'.saved, h'.frame, h'.out⟩
  rel h := upd_rel v fun a b hab =>
    let ⟨W, C, D, S, R, n, h₁, h₂, hsp⟩ := h a b hab
    ⟨W, C, D, S, R, n, h₁.base, h₂.base, hsp⟩

theorem UArgsZ.preF {s : State} {W C D S : Addr} {Z : Region} {R n : Nat} (h : UArgsZ s W C D S Z R n) :
    updateX86_64F.pre (s.callEntry.withRegions [⟨W, 240⟩, ⟨D, 16 * n⟩] [⟨C, 16⟩]) := by
  have hR := toNat_rounds h.rounds
  have hN := toNat_ofNat (n := n) (by have := h.hn; omega_arith)
  simp only [updateX86_64F, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.callEntry_rsp, State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp),
    h.rdi, h.rsi, h.rdx, h.rcx, h.r8, hR, hN]
  exact ⟨trivial, trivial, h.wc, h.dc, h.stkC.sub_left (ret_sub _),
    h.stkW.sub_left (stk_sub _), h.stkD.sub_left (stk_sub _),
    h.stkC.sub_left (stk_sub _), h.wrapC, h.wrapD, h.rounds⟩

/-- Over an implementation that never touches its scratch buffer, with only
the caller's saved registers as its working space. -/
theorem ACall.free (v : UpdateImpl) (f : UpdateFree v.callee) :
    ACall v.callee (fun S => ⟨S + BitVec.ofNat 64 2176, 48⟩) (fun S => ⟨S + BitVec.ofNat 64 2176, 0⟩) where
  sub _ := Region.sub_prefix (by decide)
  slotX _ := fun _ _ h => by simp [Region.Contains] at h
  call {s W C D S R n} h := by
    have hR := toNat_rounds h.rounds
    have hN := toNat_ofNat (n := n) (by have := h.hn; omega_arith)
    have hd := v.depth
    refine WP.call (k := updateX86_64F) f.ok v.nosp (by omega_arith) h.preF h.reads h.writes ?_
    intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
    refine ⟨hrd, hwr, hcs, ?_, ?_⟩
    · have := Frame.below_mono hf (b := 16) (by omega_arith) (by decide)
      exact Frame.mono (by simpa using this) (by simp)
    · simp only [updateX86_64F, updateX86_64, State.withRegions_gpr, State.withRegions_mem,
        State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp),
        State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp),
        State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, h.r8, hR, hN] at hpost
      have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h | h | h <;> omega_arith
      rw [← hm₂, hpost, X86_64.ciphAt, Proof.Cmac.Stream.blocksAt_eq, Proof.Cmac.Stream.blocksAt_eq,
        callEntry_bytes s (h.stkW.sub_right (Region.sub_prefix hRb)) (by omega_arith),
        callEntry_bytes s h.stkC (by decide), callEntry_bytes s h.stkD (by have := h.hn; omega_arith)]
  rel {P} h := by
    refine RelCT.callEx f.ok f.ct fun s₁ s₂ hp => ?_
    obtain ⟨W, C, D, S, R, n, h₁, h₂, hsp⟩ := h s₁ s₂ hp
    refine ⟨_, _, _, _, h₁.preF, h₂.preF, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes, hsp⟩
    simp only [updateX86_64F, updateX86_64, State.withRegions_gpr, State.callEntry_rsp,
      State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
      State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
      State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.r9 ≠ .rsp),
      h₁.rdi, h₁.rsi, h₁.rdx, h₁.rcx, h₁.r8, h₁.r9, h₂.rdi, h₂.rsi, h₂.rdx, h₂.rcx, h₂.r8, h₂.r9, hsp]
    exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## `vg_cmac_aes_subkeys` -/

theorem subkeys_nosp (v : Ctr32Impl) : NoSp (Impl.CmacAes.X86_64.subkeys v.callee) :=
  nosp_of_all (by
    simp only [Impl.CmacAes.X86_64.subkeys, Code.allInstrs, all_of_nosp v.nosp]
    decide +kernel)

theorem subkeys_depth (v : Ctr32Impl) : (Impl.CmacAes.X86_64.subkeys v.callee).depth = 1 := by
  simp [Impl.CmacAes.X86_64.subkeys, Code.depth, v.depth]

/-- What a call of `vg_cmac_aes_subkeys` needs: the key schedule `W`, the
subkeys `K`, the working space `S` and the rounds `R`. -/
structure SArgs (s : State) (W K S : Addr) (R : Nat) : Prop where
  rdi : s.gpr .rdi = W
  rsi : s.gpr .rsi = BitVec.ofNat 64 R
  rdx : s.gpr .rdx = K
  rcx : s.gpr .rcx = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  wk : (⟨W, 240⟩ : Region).Disjoint ⟨K, 32⟩
  ws : (⟨W, 240⟩ : Region).Disjoint ⟨S, 2176⟩
  ks : (⟨K, 32⟩ : Region).Disjoint ⟨S, 2176⟩
  stkW : (below (s.gpr .rsp) 16).Disjoint ⟨W, 240⟩
  stkK : (below (s.gpr .rsp) 16).Disjoint ⟨K, 32⟩
  stkS : (below (s.gpr .rsp) 16).Disjoint ⟨S, 2176⟩
  wrapK : K.toNat + 32 ≤ 2 ^ 64
  wrapS : S.toNat + 2176 ≤ 2 ^ 64
  reads : Covers ([⟨W, 240⟩] ++ [⟨K, 32⟩, ⟨S, 2176⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨K, 32⟩, ⟨S, 2176⟩] s.wr

/-- What a call of `vg_cmac_aes_subkeys` leaves. -/
structure SPost (s : State) (W K S : Addr) (R : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨K, 32⟩, ⟨S, 2176⟩, below (s.gpr .rsp) 16] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem K 32 =
    (Spec.Cmac.subkeys (Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem W (16 * (R + 1)))) 16).1 ++
      (Spec.Cmac.subkeys (Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem W (16 * (R + 1)))) 16).2

theorem SArgs.pre {s : State} {W K S : Addr} {R : Nat} (h : SArgs s W K S R) :
    subkeysX86_64.pre (s.callEntry.withRegions [⟨W, 240⟩] [⟨K, 32⟩, ⟨S, 2176⟩]) := by
  have hR := toNat_rounds h.rounds
  simp only [subkeysX86_64, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.callEntry_rsp, State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, hR]
  exact ⟨trivial, trivial, h.wk, h.ws, h.ks, h.stkK.sub_left (ret_sub _),
    h.stkS.sub_left (ret_sub _), h.stkW.sub_left (stk_sub _), h.stkK.sub_left (stk_sub _),
    h.stkS.sub_left (stk_sub _), h.wrapK, h.wrapS, h.rounds⟩

theorem sub_call (v : Ctr32Impl) (nm : String) {s : State} {W K S : Addr} {R : Nat}
    (h : SArgs s W K S R) :
    WP isa (.call nm (Impl.CmacAes.X86_64.subkeys v.callee)) s (SPost s W K S R) := by
  have hR := toNat_rounds h.rounds
  refine WP.call (k := subkeysX86_64) (subkeys_correct v) (subkeys_nosp v) (by rw [subkeys_depth]; decide)
    h.pre h.reads h.writes ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  rw [subkeys_depth] at hf
  refine ⟨hrd, hwr, hcs, by simpa using hf, ?_⟩
  simp only [subkeysX86_64, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp), h.rdi, h.rsi, h.rdx, hR] at hpost
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h | h | h <;> omega_arith
  rw [← hm₂, hpost, X86_64.ciphAt, callEntry_bytes s (h.stkW.sub_right (Region.sub_prefix hRb)) (by omega_arith)]

theorem sub_rel (v : Ctr32Impl) (nm : String) {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ W K S : Addr, ∃ R : Nat,
      SArgs s₁ W K S R ∧ SArgs s₂ W K S R ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (.call nm (Impl.CmacAes.X86_64.subkeys v.callee)) fun _ _ => True := by
  refine RelCT.callEx (subkeys_correct v) (subkeys_ct v) fun s₁ s₂ hp => ?_
  obtain ⟨W, K, S, R, h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨_, _, _, _, h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes, hsp⟩
  simp only [subkeysX86_64, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
    h₁.rdi, h₁.rsi, h₁.rdx, h₁.rcx, h₂.rdi, h₂.rsi, h₂.rdx, h₂.rcx, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

/-! ## `vg_cmac_aes_finalize` -/

theorem finalize_nosp (v : Ctr32Impl) : NoSp (Impl.CmacAes.X86_64.finalize v.callee) :=
  nosp_of_all (by
    simp only [Impl.CmacAes.X86_64.finalize, Impl.CmacAes.X86_64.finPre, Impl.CmacAes.X86_64.partialBlock,
      Impl.CmacAes.X86_64.copy, Code.allInstrs, all_of_nosp v.nosp]
    decide +kernel)

theorem finalize_depth (v : Ctr32Impl) : (Impl.CmacAes.X86_64.finalize v.callee).depth = 1 := by
  simp [Impl.CmacAes.X86_64.finalize, Impl.CmacAes.X86_64.finPre, Impl.CmacAes.X86_64.partialBlock,
    Impl.CmacAes.X86_64.copy, Code.depth, v.depth]

/-- What a call of `vg_cmac_aes_finalize` needs: the key schedule and
subkeys `K`, the state `St`, the `L` last bytes at `P`, the working space
`S` and the rounds `R`. -/
structure FArgs (s : State) (K St P S : Addr) (L R : Nat) : Prop where
  rdi : s.gpr .rdi = K
  rsi : s.gpr .rsi = BitVec.ofNat 64 R
  rdx : s.gpr .rdx = St
  rcx : s.gpr .rcx = P
  r8 : s.gpr .r8 = BitVec.ofNat 64 L
  r9 : s.gpr .r9 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  len : L ≤ 16
  kst : (⟨K, 272⟩ : Region).Disjoint ⟨St, 16⟩
  ks : (⟨K, 272⟩ : Region).Disjoint ⟨S, 2176⟩
  pst : (⟨P, L⟩ : Region).Disjoint ⟨St, 16⟩
  ps : (⟨P, L⟩ : Region).Disjoint ⟨S, 2176⟩
  sts : (⟨St, 16⟩ : Region).Disjoint ⟨S, 2176⟩
  stkK : (below (s.gpr .rsp) 16).Disjoint ⟨K, 272⟩
  stkP : (below (s.gpr .rsp) 16).Disjoint ⟨P, L⟩
  stkSt : (below (s.gpr .rsp) 16).Disjoint ⟨St, 16⟩
  stkS : (below (s.gpr .rsp) 16).Disjoint ⟨S, 2176⟩
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
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨St, 16⟩, ⟨S, 2176⟩, below (s.gpr .rsp) 16] s.mem s'.mem
  out : let ciph := Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem K (16 * (R + 1)))
    let ks := Spec.Cmac.subkeys ciph 16
    Spec.Aes.bytesAt s.mem (K + 240) 32 = ks.1 ++ ks.2 →
    ∀ msg : List Byte, msg.length % 16 = 0 → (msg = [] ∨ 0 < L) →
      Spec.Aes.bytesAt s.mem St 16 = Spec.Cmac.chain ciph (Spec.Cmac.zeros 16) (Spec.Cmac.blocks 16 msg) →
      Spec.Aes.bytesAt s'.mem St 16 = Spec.Cmac.macFull ciph 16 (msg ++ Spec.Aes.bytesAt s.mem P L)

theorem FArgs.pre {s : State} {K St P S : Addr} {L R : Nat} (h : FArgs s K St P S L R) :
    finalizeX86_64.pre (s.callEntry.withRegions [⟨K, 272⟩, ⟨P, L⟩] [⟨St, 16⟩, ⟨S, 2176⟩]) := by
  have hR := toNat_rounds h.rounds
  have hL := toNat_ofNat (n := L) (by have := h.len; omega_arith)
  simp only [finalizeX86_64, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.callEntry_rsp, State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.r9 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, hR, hL]
  exact ⟨trivial, trivial, h.kst, h.ks, h.pst, h.ps, h.sts, h.stkSt.sub_left (ret_sub _),
    h.stkS.sub_left (ret_sub _), h.stkK.sub_left (stk_sub _), h.stkP.sub_left (stk_sub _),
    h.stkSt.sub_left (stk_sub _), h.stkS.sub_left (stk_sub _), h.wrapK, h.wrapSt, h.wrapP, h.wrapS,
    h.rounds, h.len⟩

theorem fin_call (v : Ctr32Impl) (nm : String) {s : State} {K St P S : Addr} {L R : Nat}
    (h : FArgs s K St P S L R) :
    WP isa (.call nm (Impl.CmacAes.X86_64.finalize v.callee)) s (FPost s K St P S L R) := by
  have hR := toNat_rounds h.rounds
  have hL := toNat_ofNat (n := L) (by have := h.len; omega_arith)
  refine WP.call (k := finalizeX86_64) (finalize_correct v) (finalize_nosp v)
    (by rw [finalize_depth]; decide) h.pre h.reads h.writes ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  rw [finalize_depth] at hf
  refine ⟨hrd, hwr, hcs, by simpa using hf, ?_⟩
  simp only [finalizeX86_64, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, h.r8, hR, hL] at hpost
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h | h | h <;> omega_arith
  have eK : Spec.Aes.bytesAt s.callEntry.mem K (16 * (R + 1)) = Spec.Aes.bytesAt s.mem K (16 * (R + 1)) :=
    callEntry_bytes s (h.stkK.sub_right (Region.sub_prefix (by omega_arith))) (by omega_arith)
  have eK2 : Spec.Aes.bytesAt s.callEntry.mem (K + 240) 32 = Spec.Aes.bytesAt s.mem (K + 240) 32 :=
    callEntry_bytes s (h.stkK.sub_right (Offset.sub_base K (d := 240) (n := 32) (by decide))) (by decide)
  have eSt := callEntry_bytes s h.stkSt (by decide)
  have eP := callEntry_bytes s h.stkP (by omega_arith)
  intro _ _ hk msg hm hne hst
  simp only [X86_64.ciphAt, eK, eK2, eSt, eP] at hpost
  rw [← hm₂]
  exact hpost hk msg hm hne hst

theorem fin_rel (v : Ctr32Impl) (nm : String) {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ K St Q S : Addr, ∃ L R : Nat,
      FArgs s₁ K St Q S L R ∧ FArgs s₂ K St Q S L R ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (.call nm (Impl.CmacAes.X86_64.finalize v.callee)) fun _ _ => True := by
  refine RelCT.callEx (finalize_correct v) (finalize_ct v) fun s₁ s₂ hp => ?_
  obtain ⟨K, St, Q, S, L, R, h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨_, _, _, _, h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes, hsp⟩
  simp only [finalizeX86_64, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.r9 ≠ .rsp),
    h₁.rdi, h₁.rsi, h₁.rdx, h₁.rcx, h₁.r8, h₁.r9, h₂.rdi, h₂.rsi, h₂.rdx, h₂.rcx, h₂.r8, h₂.r9, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## `vg_cmac_aes_finalize` without working space for `vg_aes_ctr32` -/

/-- `FArgs`, when `vg_aes_ctr32` needs no working space: of the scratch
buffer, only the counter block at `S + 2048` is given. -/
structure FArgsF (s : State) (K St P S : Addr) (L R : Nat) : Prop where
  rdi : s.gpr .rdi = K
  rsi : s.gpr .rsi = BitVec.ofNat 64 R
  rdx : s.gpr .rdx = St
  rcx : s.gpr .rcx = P
  r8 : s.gpr .r8 = BitVec.ofNat 64 L
  r9 : s.gpr .r9 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  len : L ≤ 16
  kst : (⟨K, 272⟩ : Region).Disjoint ⟨St, 16⟩
  ks : (⟨K, 272⟩ : Region).Disjoint ⟨S + BitVec.ofNat 64 2048, 16⟩
  pst : (⟨P, L⟩ : Region).Disjoint ⟨St, 16⟩
  ps : (⟨P, L⟩ : Region).Disjoint ⟨S + BitVec.ofNat 64 2048, 16⟩
  sts : (⟨St, 16⟩ : Region).Disjoint ⟨S + BitVec.ofNat 64 2048, 16⟩
  stkK : (below (s.gpr .rsp) 16).Disjoint ⟨K, 272⟩
  stkP : (below (s.gpr .rsp) 16).Disjoint ⟨P, L⟩
  stkSt : (below (s.gpr .rsp) 16).Disjoint ⟨St, 16⟩
  stkS : (below (s.gpr .rsp) 16).Disjoint ⟨S + BitVec.ofNat 64 2048, 16⟩
  wrapK : K.toNat + 272 ≤ 2 ^ 64
  wrapSt : St.toNat + 16 ≤ 2 ^ 64
  wrapP : P.toNat + L ≤ 2 ^ 64
  wrapS : (S + BitVec.ofNat 64 2048).toNat + 16 ≤ 2 ^ 64
  reads : Covers ([⟨K, 272⟩, ⟨P, L⟩] ++ [⟨St, 16⟩, ⟨S + BitVec.ofNat 64 2048, 16⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨St, 16⟩, ⟨S + BitVec.ofNat 64 2048, 16⟩] s.wr

/-- What a call of `vg_cmac_aes_finalize` leaves. -/
structure FPostF (s : State) (K St P S : Addr) (L R : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨St, 16⟩, ⟨S + BitVec.ofNat 64 2048, 16⟩, below (s.gpr .rsp) 16] s.mem s'.mem
  out : let ciph := Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem K (16 * (R + 1)))
    let ks := Spec.Cmac.subkeys ciph 16
    Spec.Aes.bytesAt s.mem (K + 240) 32 = ks.1 ++ ks.2 →
    ∀ msg : List Byte, msg.length % 16 = 0 → (msg = [] ∨ 0 < L) →
      Spec.Aes.bytesAt s.mem St 16 = Spec.Cmac.chain ciph (Spec.Cmac.zeros 16) (Spec.Cmac.blocks 16 msg) →
      Spec.Aes.bytesAt s'.mem St 16 = Spec.Cmac.macFull ciph 16 (msg ++ Spec.Aes.bytesAt s.mem P L)

theorem FArgsF.pre {s : State} {K St P S : Addr} {L R : Nat} (h : FArgsF s K St P S L R) :
    finalizeX86_64F.pre (s.callEntry.withRegions [⟨K, 272⟩, ⟨P, L⟩] [⟨St, 16⟩, ⟨S + BitVec.ofNat 64 2048, 16⟩]) := by
  have hR := toNat_rounds h.rounds
  have hL := toNat_ofNat (n := L) (by have := h.len; omega_arith)
  simp only [finalizeX86_64F, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.callEntry_rsp, State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.r9 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, hR, hL]
  exact ⟨trivial, trivial, h.kst, h.ks, h.pst, h.ps, h.sts, h.stkSt.sub_left (ret_sub _),
    h.stkS.sub_left (ret_sub _), h.stkK.sub_left (stk_sub _), h.stkP.sub_left (stk_sub _),
    h.stkSt.sub_left (stk_sub _), h.stkS.sub_left (stk_sub _), h.wrapK, h.wrapSt, h.wrapP, h.wrapS,
    h.rounds, h.len⟩

theorem fin_callF (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Free v.callee) (nm : String) {s : State}
    {K St P S : Addr} {L R : Nat} (h : FArgsF s K St P S L R) :
    WP isa (.call nm (Impl.CmacAes.X86_64.finalize v.callee)) s (FPostF s K St P S L R) := by
  have hR := toNat_rounds h.rounds
  have hL := toNat_ofNat (n := L) (by have := h.len; omega_arith)
  refine WP.call (k := finalizeX86_64F) (finalizeF_correct v f) (finalize_nosp v)
    (by rw [finalize_depth]; decide) h.pre h.reads h.writes ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  rw [finalize_depth] at hf
  refine ⟨hrd, hwr, hcs, by simpa using hf, ?_⟩
  simp only [finalizeX86_64F, finalizeX86_64, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, h.r8, hR, hL] at hpost
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h | h | h <;> omega_arith
  have eK : Spec.Aes.bytesAt s.callEntry.mem K (16 * (R + 1)) = Spec.Aes.bytesAt s.mem K (16 * (R + 1)) :=
    callEntry_bytes s (h.stkK.sub_right (Region.sub_prefix (by omega_arith))) (by omega_arith)
  have eK2 : Spec.Aes.bytesAt s.callEntry.mem (K + 240) 32 = Spec.Aes.bytesAt s.mem (K + 240) 32 :=
    callEntry_bytes s (h.stkK.sub_right (Offset.sub_base K (d := 240) (n := 32) (by decide))) (by decide)
  have eSt := callEntry_bytes s h.stkSt (by decide)
  have eP := callEntry_bytes s h.stkP (by omega_arith)
  intro _ _ hk msg hm hne hst
  simp only [X86_64.ciphAt, eK, eK2, eSt, eP] at hpost
  rw [← hm₂]
  exact hpost hk msg hm hne hst

theorem fin_relF (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Free v.callee) (nm : String) {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ K St Q S : Addr, ∃ L R : Nat,
      FArgsF s₁ K St Q S L R ∧ FArgsF s₂ K St Q S L R ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (.call nm (Impl.CmacAes.X86_64.finalize v.callee)) fun _ _ => True := by
  refine RelCT.callEx (finalizeF_correct v f) (finalizeF_ct v f) fun s₁ s₂ hp => ?_
  obtain ⟨K, St, Q, S, L, R, h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨_, _, _, _, h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes, hsp⟩
  simp only [finalizeX86_64F, finalizeX86_64, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.r9 ≠ .rsp),
    h₁.rdi, h₁.rsi, h₁.rdx, h₁.rcx, h₁.r8, h₁.r9, h₂.rdi, h₂.rsi, h₂.rdx, h₂.rcx, h₂.r8, h₂.r9, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## `vg_aes_expand_key_scratch` -/

/-- What a call of `vg_aes_expand_key_scratch` needs: the key `Kp` of `KL` bytes,
the schedule `W` and the working space `S`. -/
structure EArgs (s : State) (Kp W S : Addr) (KL : Nat) : Prop where
  rdi : s.gpr .rdi = Kp
  rsi : s.gpr .rsi = BitVec.ofNat 64 KL
  rdx : s.gpr .rdx = W
  rcx : s.gpr .rcx = S
  klen : KL = 16 ∨ KL = 24 ∨ KL = 32
  kw : (⟨Kp, KL⟩ : Region).Disjoint ⟨W, 240⟩
  ks : (⟨Kp, KL⟩ : Region).Disjoint ⟨S, 512⟩
  ws : (⟨W, 240⟩ : Region).Disjoint ⟨S, 512⟩
  stkK : (below (s.gpr .rsp) 16).Disjoint ⟨Kp, KL⟩
  stkW : (below (s.gpr .rsp) 16).Disjoint ⟨W, 240⟩
  stkS : (below (s.gpr .rsp) 16).Disjoint ⟨S, 512⟩
  reads : Covers ([⟨Kp, KL⟩] ++ [⟨W, 240⟩, ⟨S, 512⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨W, 240⟩, ⟨S, 512⟩] s.wr

/-- What a call of `vg_aes_expand_key_scratch` leaves. -/
structure EPost (s : State) (Kp W S : Addr) (KL : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨W, 240⟩, ⟨S, 512⟩, below (s.gpr .rsp) 16] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem W (16 * (Spec.Aes.rounds (KL / 4) + 1)) =
    Spec.Aes.expandKey (Spec.Aes.bytesAt s.mem Kp KL)

theorem EArgs.pre {s : State} {Kp W S : Addr} {KL : Nat} (h : EArgs s Kp W S KL) :
    Proof.Aes.expandKeyX86_64.pre (s.callEntry.withRegions [⟨Kp, KL⟩] [⟨W, 240⟩, ⟨S, 512⟩]) := by
  have hK := toNat_ofNat (n := KL) (by rcases h.klen with h | h | h <;> omega_arith)
  simp only [Proof.Aes.expandKeyX86_64, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.callEntry_rsp, State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, hK]
  exact ⟨trivial, trivial, h.kw, h.ks, h.ws, h.stkW.sub_left (ret_sub _),
    h.stkS.sub_left (ret_sub _), h.klen⟩

theorem ek_call (v : Ctr32Impl) {s : State} {Kp W S : Addr} {KL : Nat} (h : EArgs s Kp W S KL) :
    WP isa (.call v.expand.name v.expand.code) s (EPost s Kp W S KL) := by
  have hK := toNat_ofNat (n := KL) (by rcases h.klen with h | h | h <;> omega_arith)
  refine WP.call (k := Proof.Aes.expandKeyX86_64) v.expandOk v.expandNosp
    (by rw [v.expandDepth]; decide) h.pre h.reads h.writes ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  rw [v.expandDepth] at hf
  refine ⟨hrd, hwr, hcs, by simpa using Frame.below_mono hf (b := 16) (by decide) (by decide), ?_⟩
  simp only [Proof.Aes.expandKeyX86_64, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp), h.rdi, h.rsi, h.rdx, hK] at hpost
  rw [← hm₂, hpost, callEntry_bytes s h.stkK (by rcases h.klen with h | h | h <;> omega_arith)]

theorem ek_rel (v : Ctr32Impl) {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ Kp W S : Addr, ∃ KL : Nat,
      EArgs s₁ Kp W S KL ∧ EArgs s₂ Kp W S KL ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (.call v.expand.name v.expand.code) fun _ _ => True := by
  refine RelCT.callEx v.expandOk v.expandCt fun s₁ s₂ hp => ?_
  obtain ⟨Kp, W, S, KL, h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨_, _, _, _, h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes, hsp⟩
  simp only [Proof.Aes.expandKeyX86_64, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
    h₁.rdi, h₁.rsi, h₁.rdx, h₁.rcx, h₂.rdi, h₂.rsi, h₂.rdx, h₂.rcx, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

/-! ## Calls that write no more than a given part of the working space

`vg_aes_expand_key_scratch` and `vg_cmac_aes_subkeys` over implementations of
AES that need no working space (`Aes.X86_64.Ctr32Free`) write less of it:
none of it, and only the 32 bytes at `S + 2048` (`subkeysX86_64F`). What
the callers need of either call is its arguments without the working space
(`EArgsF`, `SArgsF`), and that it writes no more of it than some region `X`
(`EPostX`, `SPostX`). -/

/-- What a call of `vg_aes_expand_key_scratch` needs, but its working space. -/
structure EArgsF (s : State) (Kp W : Addr) (KL : Nat) : Prop where
  rdi : s.gpr .rdi = Kp
  rsi : s.gpr .rsi = BitVec.ofNat 64 KL
  rdx : s.gpr .rdx = W
  klen : KL = 16 ∨ KL = 24 ∨ KL = 32
  kw : (⟨Kp, KL⟩ : Region).Disjoint ⟨W, 240⟩
  stkK : (below (s.gpr .rsp) 16).Disjoint ⟨Kp, KL⟩
  stkW : (below (s.gpr .rsp) 16).Disjoint ⟨W, 240⟩
  reads : Covers ([⟨Kp, KL⟩] ++ [⟨W, 240⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨W, 240⟩] s.wr

/-- What a call of `vg_aes_expand_key_scratch` leaves, writing no more than
`X` of its working space. -/
structure EPostX (s : State) (Kp W : Addr) (KL : Nat) (X : Region) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨W, 240⟩, X, below (s.gpr .rsp) 16] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem W (16 * (Spec.Aes.rounds (KL / 4) + 1)) =
    Spec.Aes.expandKey (Spec.Aes.bytesAt s.mem Kp KL)

theorem EArgsF.full {s : State} {Kp W S : Addr} {KL : Nat} (h : EArgsF s Kp W KL) (rcx : s.gpr .rcx = S)
    (ks : (⟨Kp, KL⟩ : Region).Disjoint ⟨S, 512⟩) (ws : (⟨W, 240⟩ : Region).Disjoint ⟨S, 512⟩)
    (stkS : (below (s.gpr .rsp) 16).Disjoint ⟨S, 512⟩) (cs : Covers [⟨S, 512⟩] s.wr) : EArgs s Kp W S KL :=
  ⟨h.rdi, h.rsi, h.rdx, rcx, h.klen, h.kw, ks, ws, h.stkK, h.stkW, stkS, by
    intro a n ⟨r, hr, hc⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.reads a n ⟨_, by simp, hc⟩
    · exact h.reads a n ⟨_, by simp, hc⟩
    · exact Covers.right cs a n ⟨_, by simp, hc⟩, Covers.cons h.writes cs⟩

theorem EPost.x {s s' : State} {Kp W S : Addr} {KL : Nat} {X : Region} (h : EPost s Kp W S KL s')
    (hX : Region.Sub ⟨S, 512⟩ X) : EPostX s Kp W KL X s' :=
  ⟨h.rd, h.wr, h.saved, h.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨X, by simp, hX⟩
    · exact ⟨_, by simp, fun _ h => h⟩, h.out⟩

/-- `vg_aes_expand_key_scratch_aesni`, which writes none of its working space. -/
abbrev ekF : Impl.Aes.X86_64.ExpandKey := .aesni

theorem EArgsF.pre {s : State} {Kp W : Addr} {KL : Nat} (h : EArgsF s Kp W KL) :
    Proof.Aes.X86_64.AesNi.Key.expandKey3X86_64.pre (s.callEntry.withRegions [⟨Kp, KL⟩] [⟨W, 240⟩]) := by
  have hK := toNat_ofNat (n := KL) (by rcases h.klen with h | h | h <;> omega_arith)
  simp only [Proof.Aes.X86_64.AesNi.Key.expandKey3X86_64, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.callEntry_rsp, State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp),
    h.rdi, h.rsi, h.rdx, hK]
  exact ⟨trivial, trivial, h.stkW.sub_left (ret_sub _), h.klen⟩

theorem ek_callF {s : State} {Kp W : Addr} {KL : Nat} {X : Region} (h : EArgsF s Kp W KL) :
    WP isa (.call ekF.name ekF.code) s (EPostX s Kp W KL X) := by
  have hK := toNat_ofNat (n := KL) (by rcases h.klen with h | h | h <;> omega_arith)
  have hd : Code.depth Impl.Aes.X86_64.AesNi.expandKey = 0 := Ctr32Impl.aesni.expandDepth
  refine WP.call (k := Proof.Aes.X86_64.AesNi.Key.expandKey3X86_64)
    Proof.Aes.X86_64.AesNi.Key.expandKey3_correct Ctr32Impl.aesni.expandNosp
    (by rw [hd]; decide) (rd := [⟨Kp, KL⟩]) (wr := [⟨W, 240⟩]) h.pre h.reads h.writes ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  rw [hd] at hf
  refine ⟨hrd, hwr, hcs, (Frame.below_mono hf (b := 16) (by decide) (by decide)).mono fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl <;> simp, ?_⟩
  simp only [Proof.Aes.X86_64.AesNi.Key.expandKey3X86_64, Proof.Aes.X86_64.AesNi.expandKeyX86_64,
    State.withRegions_gpr,
    State.withRegions_mem, State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp),
    h.rdi, h.rsi, h.rdx, hK] at hpost
  rw [← hm₂, hpost, callEntry_bytes s h.stkK (by rcases h.klen with h | h | h <;> omega_arith)]

theorem ek_relF {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ Kp W : Addr, ∃ KL : Nat,
      EArgsF s₁ Kp W KL ∧ EArgsF s₂ Kp W KL ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (.call ekF.name ekF.code) fun _ _ => True := by
  refine RelCT.callEx Proof.Aes.X86_64.AesNi.Key.expandKey3_correct Proof.Aes.X86_64.AesNi.Key.expandKey3_ct
    fun s₁ s₂ hp => ?_
  obtain ⟨Kp, W, KL, h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨_, _, _, _, h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes, hsp⟩
  simp only [Proof.Aes.X86_64.AesNi.Key.expandKey3X86_64, State.withRegions_gpr,
    State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), h₁.rdi, h₁.rsi, h₁.rdx, h₂.rdi, h₂.rsi, h₂.rdx]
  exact ⟨trivial, trivial, trivial⟩

/-- What a call of `vg_cmac_aes_subkeys` needs, of its working space only the
32 bytes at `S + 2048`. -/
structure SArgsF (s : State) (W K S : Addr) (R : Nat) : Prop where
  rdi : s.gpr .rdi = W
  rsi : s.gpr .rsi = BitVec.ofNat 64 R
  rdx : s.gpr .rdx = K
  rcx : s.gpr .rcx = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  wk : (⟨W, 240⟩ : Region).Disjoint ⟨K, 32⟩
  ws : (⟨W, 240⟩ : Region).Disjoint ⟨S + BitVec.ofNat 64 2048, 32⟩
  ks : (⟨K, 32⟩ : Region).Disjoint ⟨S + BitVec.ofNat 64 2048, 32⟩
  stkW : (below (s.gpr .rsp) 16).Disjoint ⟨W, 240⟩
  stkK : (below (s.gpr .rsp) 16).Disjoint ⟨K, 32⟩
  stkS : (below (s.gpr .rsp) 16).Disjoint ⟨S + BitVec.ofNat 64 2048, 32⟩
  wrapK : K.toNat + 32 ≤ 2 ^ 64
  wrapS : (S + BitVec.ofNat 64 2048).toNat + 32 ≤ 2 ^ 64
  reads : Covers ([⟨W, 240⟩] ++ [⟨K, 32⟩, ⟨S + BitVec.ofNat 64 2048, 32⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨K, 32⟩, ⟨S + BitVec.ofNat 64 2048, 32⟩] s.wr

/-- What a call of `vg_cmac_aes_subkeys` leaves, writing no more than `X` of
its working space. -/
structure SPostX (s : State) (W K : Addr) (R : Nat) (X : Region) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨K, 32⟩, X, below (s.gpr .rsp) 16] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem K 32 =
    (Spec.Cmac.subkeys (Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem W (16 * (R + 1)))) 16).1 ++
      (Spec.Cmac.subkeys (Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem W (16 * (R + 1)))) 16).2

theorem SArgsF.full {s : State} {W K S : Addr} {R : Nat} (h : SArgsF s W K S R)
    (ws : (⟨W, 240⟩ : Region).Disjoint ⟨S, 2176⟩) (ks : (⟨K, 32⟩ : Region).Disjoint ⟨S, 2176⟩)
    (stkS : (below (s.gpr .rsp) 16).Disjoint ⟨S, 2176⟩) (wrapS : S.toNat + 2176 ≤ 2 ^ 64)
    (cs : Covers [⟨S, 2176⟩] s.wr) : SArgs s W K S R where
  rdi := h.rdi
  rsi := h.rsi
  rdx := h.rdx
  rcx := h.rcx
  rounds := h.rounds
  wk := h.wk
  ws := ws
  ks := ks
  stkW := h.stkW
  stkK := h.stkK
  stkS := stkS
  wrapK := h.wrapK
  wrapS := wrapS
  reads := by
    intro a n ⟨r, hr, hc⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.reads a n ⟨_, by simp, hc⟩
    · exact h.reads a n ⟨_, by simp, hc⟩
    · exact Covers.right cs a n ⟨_, by simp, hc⟩
  writes := by
    intro a n ⟨r, hr, hc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.writes a n ⟨_, by simp, hc⟩
    · exact cs a n ⟨_, by simp, hc⟩

theorem SPost.x {s s' : State} {W K S : Addr} {R : Nat} {X : Region} (h : SPost s W K S R s')
    (hX : Region.Sub ⟨S, 2176⟩ X) : SPostX s W K R X s' :=
  ⟨h.rd, h.wr, h.saved, h.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨X, by simp, hX⟩
    · exact ⟨_, by simp, fun _ h => h⟩, h.out⟩

theorem SArgsF.pre {s : State} {W K S : Addr} {R : Nat} (h : SArgsF s W K S R) :
    subkeysX86_64F.pre (s.callEntry.withRegions [⟨W, 240⟩] [⟨K, 32⟩, ⟨S + BitVec.ofNat 64 2048, 32⟩]) := by
  have hR := toNat_rounds h.rounds
  simp only [subkeysX86_64F, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.callEntry_rsp, State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, hR]
  exact ⟨trivial, trivial, h.wk, h.ws, h.ks, h.stkK.sub_left (ret_sub _),
    h.stkS.sub_left (ret_sub _), h.stkW.sub_left (stk_sub _), h.stkK.sub_left (stk_sub _),
    h.stkS.sub_left (stk_sub _), h.wrapK, h.wrapS, h.rounds⟩

theorem sub_callF (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Free v.callee) (nm : String) {s : State}
    {W K S : Addr} {R : Nat} (h : SArgsF s W K S R) :
    WP isa (.call nm (Impl.CmacAes.X86_64.subkeys v.callee)) s
      (SPostX s W K R ⟨S + BitVec.ofNat 64 2048, 32⟩) := by
  have hR := toNat_rounds h.rounds
  refine WP.call (k := subkeysX86_64F) (subkeysF_correct v f) (subkeys_nosp v) (by rw [subkeys_depth]; decide)
    h.pre h.reads h.writes ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  rw [subkeys_depth] at hf
  refine ⟨hrd, hwr, hcs, by simpa using hf, ?_⟩
  simp only [subkeysX86_64F, subkeysX86_64, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp), h.rdi, h.rsi, h.rdx, hR] at hpost
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h | h | h <;> omega_arith
  rw [← hm₂, hpost, X86_64.ciphAt, callEntry_bytes s (h.stkW.sub_right (Region.sub_prefix hRb)) (by omega_arith)]

theorem sub_relF (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Free v.callee) (nm : String)
    {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ W K S : Addr, ∃ R : Nat,
      SArgsF s₁ W K S R ∧ SArgsF s₂ W K S R ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (.call nm (Impl.CmacAes.X86_64.subkeys v.callee)) fun _ _ => True := by
  refine RelCT.callEx (subkeysF_correct v f) (subkeysF_ct v f) fun s₁ s₂ hp => ?_
  obtain ⟨W, K, S, R, h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨_, _, _, _, h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes, hsp⟩
  simp only [subkeysX86_64F, subkeysX86_64, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
    h₁.rdi, h₁.rsi, h₁.rdx, h₁.rcx, h₂.rdi, h₂.rsi, h₂.rdx, h₂.rcx, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

end VG.Proof.CmacAes.Stream.X86_64
