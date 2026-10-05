import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.CmacAes.X86_64.Verified
import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Impl.CmacAes.Stream.X86_64
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Cmac.Contract
import VerifiedGarbage.Proof.CmacAes.Stream.Scratch

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Call`. -/
section

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

end VG.Proof.CmacAes.Stream.X86_64

end

/-!
# Streaming AES-CMAC on x86-64: the calls

A call of each function the streaming functions call (`vg_aes_expand_key_scratch`,
`vg_cmac_aes_subkeys`, `vg_cmac_aes_update` and `vg_cmac_aes_finalize`, for
any implementation of AES), from its contract (with `WP.call`): what it needs
(`…Args`), what it leaves (`…Post`, in terms of the memory before the call),
and that two calls with the same arguments leak the same (`…_rel`). Each
callee's stack is in the 16 bytes below the stack pointer (`below sp 16`): its
return address, and that of the call of `vg_aes_ctr32` it makes.
-/

namespace VG.Proof.CmacAes.Stream.X86_64

open VG VG.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.CmacAes.X86_64 (updateX86_64 subkeysX86_64 finalizeX86_64 update_correct subkeys_correct
  finalize_correct update_ct subkeys_ct finalize_ct callEntry_frame bytesAt_frame toNat_rounds)

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
  VG.Proof.CmacAes.X86_64.bytesAt_frame (callEntry_frame s) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (h.sub_left (VG.Proof.CmacAes.Stream.X86_64.below8_sub _)).symm) hn

theorem toNat_ofNat {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-! ## No writes of `rsp` -/

theorem nosp_of_all {c : Prog isa} (h : c.allInstrs (fun i => !Taint.clobbers i .rsp) = true) : NoSp c := by
  rw [Code.allInstrs_eq] at h
  exact fun i hi => by simpa using List.all_eq_true.mp h i hi

theorem all_of_nosp {c : Prog isa} (h : NoSp c) : c.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by
  rw [Code.allInstrs_eq, List.all_eq_true]
  exact fun i hi => by simp [h i hi]

theorem update_nosp (v : Ctr32Impl) : NoSp (Impl.CmacAes.X86_64.update v.callee) :=
  VG.Proof.CmacAes.Stream.X86_64.nosp_of_all (by
    simp only [Impl.CmacAes.X86_64.update, Impl.CmacAes.X86_64.body, Code.allInstrs, VG.Proof.CmacAes.Stream.X86_64.all_of_nosp v.nosp]
    decide +kernel)

theorem update_depth (v : Ctr32Impl) : (Impl.CmacAes.X86_64.update v.callee).depth = 1 := by
  simp [Impl.CmacAes.X86_64.update, Impl.CmacAes.X86_64.body, Code.depth, v.depth]

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

theorem UArgs.pre {s : State} {W C D S : Addr} {R n : Nat} (h : VG.Proof.CmacAes.Stream.X86_64.UArgs s W C D S R n) :
    updateX86_64.pre (s.callEntry.withRegions [⟨W, 240⟩, ⟨D, 16 * n⟩] [⟨C, 16⟩, ⟨S, 2176⟩]) := by
  have hR := toNat_rounds h.rounds
  have hN := VG.Proof.CmacAes.Stream.X86_64.toNat_ofNat (n := n) (by have := h.hn; omega)
  simp only [updateX86_64, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.callEntry_rsp, State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.r9 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, hR, hN]
  exact ⟨trivial, trivial, h.wc, h.ws, h.dc, h.ds, h.cs, h.stkC.sub_left (VG.Proof.CmacAes.Stream.X86_64.ret_sub _),
    h.stkS.sub_left (VG.Proof.CmacAes.Stream.X86_64.ret_sub _), h.stkW.sub_left (VG.Proof.CmacAes.Stream.X86_64.stk_sub _), h.stkD.sub_left (VG.Proof.CmacAes.Stream.X86_64.stk_sub _),
    h.stkC.sub_left (VG.Proof.CmacAes.Stream.X86_64.stk_sub _), h.stkS.sub_left (VG.Proof.CmacAes.Stream.X86_64.stk_sub _), h.wrapC, h.wrapD, h.wrapS, h.rounds⟩

theorem upd_call (v : Ctr32Impl) (nm : String) {s : State} {W C D S : Addr} {R n : Nat}
    (h : VG.Proof.CmacAes.Stream.X86_64.UArgs s W C D S R n) :
    WP isa (.call nm (Impl.CmacAes.X86_64.update v.callee)) s (VG.Proof.CmacAes.Stream.X86_64.UPost s W C D S R n) := by
  have hR := toNat_rounds h.rounds
  have hN := VG.Proof.CmacAes.Stream.X86_64.toNat_ofNat (n := n) (by have := h.hn; omega)
  refine WP.call (k := updateX86_64) (update_correct v) (VG.Proof.CmacAes.Stream.X86_64.update_nosp v) (by rw [VG.Proof.CmacAes.Stream.X86_64.update_depth]; decide)
    h.pre h.reads h.writes ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  rw [VG.Proof.CmacAes.Stream.X86_64.update_depth] at hf
  refine ⟨hrd, hwr, hcs, by simpa using hf, ?_⟩
  simp only [updateX86_64, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, h.r8, hR, hN] at hpost
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h | h | h <;> omega
  rw [← hm₂, hpost, X86_64.ciphAt, Proof.Cmac.Stream.blocksAt_eq, Proof.Cmac.Stream.blocksAt_eq,
    VG.Proof.CmacAes.Stream.X86_64.callEntry_bytes s (h.stkW.sub_right (Region.sub_prefix hRb)) (by omega),
    VG.Proof.CmacAes.Stream.X86_64.callEntry_bytes s h.stkC (by decide), VG.Proof.CmacAes.Stream.X86_64.callEntry_bytes s h.stkD (by have := h.hn; omega)]

theorem upd_rel (v : Ctr32Impl) (nm : String) {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ W C D S : Addr, ∃ R n : Nat,
      VG.Proof.CmacAes.Stream.X86_64.UArgs s₁ W C D S R n ∧ VG.Proof.CmacAes.Stream.X86_64.UArgs s₂ W C D S R n ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (.call nm (Impl.CmacAes.X86_64.update v.callee)) fun _ _ => True := by
  refine RelCT.callEx (update_correct v) (update_ct v) fun s₁ s₂ hp => ?_
  obtain ⟨W, C, D, S, R, n, h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨_, _, _, _, h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes, hsp⟩
  simp only [updateX86_64, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.r9 ≠ .rsp),
    h₁.rdi, h₁.rsi, h₁.rdx, h₁.rcx, h₁.r8, h₁.r9, h₂.rdi, h₂.rsi, h₂.rdx, h₂.rcx, h₂.r8, h₂.r9, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## `vg_cmac_aes_subkeys` -/

theorem subkeys_nosp (v : Ctr32Impl) : NoSp (Impl.CmacAes.X86_64.subkeys v.callee) :=
  VG.Proof.CmacAes.Stream.X86_64.nosp_of_all (by
    simp only [Impl.CmacAes.X86_64.subkeys, Code.allInstrs, VG.Proof.CmacAes.Stream.X86_64.all_of_nosp v.nosp]
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

theorem SArgs.pre {s : State} {W K S : Addr} {R : Nat} (h : VG.Proof.CmacAes.Stream.X86_64.SArgs s W K S R) :
    subkeysX86_64.pre (s.callEntry.withRegions [⟨W, 240⟩] [⟨K, 32⟩, ⟨S, 2176⟩]) := by
  have hR := toNat_rounds h.rounds
  simp only [subkeysX86_64, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.callEntry_rsp, State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, hR]
  exact ⟨trivial, trivial, h.wk, h.ws, h.ks, h.stkK.sub_left (VG.Proof.CmacAes.Stream.X86_64.ret_sub _),
    h.stkS.sub_left (VG.Proof.CmacAes.Stream.X86_64.ret_sub _), h.stkW.sub_left (VG.Proof.CmacAes.Stream.X86_64.stk_sub _), h.stkK.sub_left (VG.Proof.CmacAes.Stream.X86_64.stk_sub _),
    h.stkS.sub_left (VG.Proof.CmacAes.Stream.X86_64.stk_sub _), h.wrapK, h.wrapS, h.rounds⟩

theorem sub_call (v : Ctr32Impl) (nm : String) {s : State} {W K S : Addr} {R : Nat}
    (h : VG.Proof.CmacAes.Stream.X86_64.SArgs s W K S R) :
    WP isa (.call nm (Impl.CmacAes.X86_64.subkeys v.callee)) s (VG.Proof.CmacAes.Stream.X86_64.SPost s W K S R) := by
  have hR := toNat_rounds h.rounds
  refine WP.call (k := subkeysX86_64) (subkeys_correct v) (VG.Proof.CmacAes.Stream.X86_64.subkeys_nosp v) (by rw [VG.Proof.CmacAes.Stream.X86_64.subkeys_depth]; decide)
    h.pre h.reads h.writes ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  rw [VG.Proof.CmacAes.Stream.X86_64.subkeys_depth] at hf
  refine ⟨hrd, hwr, hcs, by simpa using hf, ?_⟩
  simp only [subkeysX86_64, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp), h.rdi, h.rsi, h.rdx, hR] at hpost
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h | h | h <;> omega
  rw [← hm₂, hpost, X86_64.ciphAt, VG.Proof.CmacAes.Stream.X86_64.callEntry_bytes s (h.stkW.sub_right (Region.sub_prefix hRb)) (by omega)]

theorem sub_rel (v : Ctr32Impl) (nm : String) {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ W K S : Addr, ∃ R : Nat,
      VG.Proof.CmacAes.Stream.X86_64.SArgs s₁ W K S R ∧ VG.Proof.CmacAes.Stream.X86_64.SArgs s₂ W K S R ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
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
  VG.Proof.CmacAes.Stream.X86_64.nosp_of_all (by
    simp only [Impl.CmacAes.X86_64.finalize, Impl.CmacAes.X86_64.finPre, Impl.CmacAes.X86_64.partialBlock,
      Impl.CmacAes.X86_64.copy, Code.allInstrs, VG.Proof.CmacAes.Stream.X86_64.all_of_nosp v.nosp]
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

theorem FArgs.pre {s : State} {K St P S : Addr} {L R : Nat} (h : VG.Proof.CmacAes.Stream.X86_64.FArgs s K St P S L R) :
    finalizeX86_64.pre (s.callEntry.withRegions [⟨K, 272⟩, ⟨P, L⟩] [⟨St, 16⟩, ⟨S, 2176⟩]) := by
  have hR := toNat_rounds h.rounds
  have hL := VG.Proof.CmacAes.Stream.X86_64.toNat_ofNat (n := L) (by have := h.len; omega)
  simp only [finalizeX86_64, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.callEntry_rsp, State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.r9 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, hR, hL]
  exact ⟨trivial, trivial, h.kst, h.ks, h.pst, h.ps, h.sts, h.stkSt.sub_left (VG.Proof.CmacAes.Stream.X86_64.ret_sub _),
    h.stkS.sub_left (VG.Proof.CmacAes.Stream.X86_64.ret_sub _), h.stkK.sub_left (VG.Proof.CmacAes.Stream.X86_64.stk_sub _), h.stkP.sub_left (VG.Proof.CmacAes.Stream.X86_64.stk_sub _),
    h.stkSt.sub_left (VG.Proof.CmacAes.Stream.X86_64.stk_sub _), h.stkS.sub_left (VG.Proof.CmacAes.Stream.X86_64.stk_sub _), h.wrapK, h.wrapSt, h.wrapP, h.wrapS,
    h.rounds, h.len⟩

theorem fin_call (v : Ctr32Impl) (nm : String) {s : State} {K St P S : Addr} {L R : Nat}
    (h : VG.Proof.CmacAes.Stream.X86_64.FArgs s K St P S L R) :
    WP isa (.call nm (Impl.CmacAes.X86_64.finalize v.callee)) s (VG.Proof.CmacAes.Stream.X86_64.FPost s K St P S L R) := by
  have hR := toNat_rounds h.rounds
  have hL := VG.Proof.CmacAes.Stream.X86_64.toNat_ofNat (n := L) (by have := h.len; omega)
  refine WP.call (k := finalizeX86_64) (finalize_correct v) (VG.Proof.CmacAes.Stream.X86_64.finalize_nosp v)
    (by rw [VG.Proof.CmacAes.Stream.X86_64.finalize_depth]; decide) h.pre h.reads h.writes ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  rw [VG.Proof.CmacAes.Stream.X86_64.finalize_depth] at hf
  refine ⟨hrd, hwr, hcs, by simpa using hf, ?_⟩
  simp only [finalizeX86_64, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, h.r8, hR, hL] at hpost
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h | h | h <;> omega
  have eK : Spec.Aes.bytesAt s.callEntry.mem K (16 * (R + 1)) = Spec.Aes.bytesAt s.mem K (16 * (R + 1)) :=
    VG.Proof.CmacAes.Stream.X86_64.callEntry_bytes s (h.stkK.sub_right (Region.sub_prefix (by omega))) (by omega)
  have eK2 : Spec.Aes.bytesAt s.callEntry.mem (K + 240) 32 = Spec.Aes.bytesAt s.mem (K + 240) 32 :=
    VG.Proof.CmacAes.Stream.X86_64.callEntry_bytes s (h.stkK.sub_right (Offset.sub_base K (d := 240) (n := 32) (by decide))) (by decide)
  have eSt := VG.Proof.CmacAes.Stream.X86_64.callEntry_bytes s h.stkSt (by decide)
  have eP := VG.Proof.CmacAes.Stream.X86_64.callEntry_bytes s h.stkP (by omega)
  intro _ _ hk msg hm hne hst
  simp only [X86_64.ciphAt, eK, eK2, eSt, eP] at hpost
  rw [← hm₂]
  exact hpost hk msg hm hne hst

theorem fin_rel (v : Ctr32Impl) (nm : String) {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ K St Q S : Addr, ∃ L R : Nat,
      VG.Proof.CmacAes.Stream.X86_64.FArgs s₁ K St Q S L R ∧ VG.Proof.CmacAes.Stream.X86_64.FArgs s₂ K St Q S L R ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
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

theorem EArgs.pre {s : State} {Kp W S : Addr} {KL : Nat} (h : VG.Proof.CmacAes.Stream.X86_64.EArgs s Kp W S KL) :
    Proof.Aes.expandKeyX86_64.pre (s.callEntry.withRegions [⟨Kp, KL⟩] [⟨W, 240⟩, ⟨S, 512⟩]) := by
  have hK := VG.Proof.CmacAes.Stream.X86_64.toNat_ofNat (n := KL) (by rcases h.klen with h | h | h <;> omega)
  simp only [Proof.Aes.expandKeyX86_64, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.callEntry_rsp, State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, hK]
  exact ⟨trivial, trivial, h.kw, h.ks, h.ws, h.stkW.sub_left (VG.Proof.CmacAes.Stream.X86_64.ret_sub _),
    h.stkS.sub_left (VG.Proof.CmacAes.Stream.X86_64.ret_sub _), h.klen⟩

theorem ek_call (v : Ctr32Impl) {s : State} {Kp W S : Addr} {KL : Nat} (h : VG.Proof.CmacAes.Stream.X86_64.EArgs s Kp W S KL) :
    WP isa (.call v.expand.name v.expand.code) s (VG.Proof.CmacAes.Stream.X86_64.EPost s Kp W S KL) := by
  have hK := VG.Proof.CmacAes.Stream.X86_64.toNat_ofNat (n := KL) (by rcases h.klen with h | h | h <;> omega)
  refine WP.call (k := Proof.Aes.expandKeyX86_64) v.expandOk v.expandNosp
    (by rw [v.expandDepth]; decide) h.pre h.reads h.writes ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩
  rw [v.expandDepth] at hf
  refine ⟨hrd, hwr, hcs, by simpa using Frame.below_mono hf (b := 16) (by decide) (by decide), ?_⟩
  simp only [Proof.Aes.expandKeyX86_64, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp), h.rdi, h.rsi, h.rdx, hK] at hpost
  rw [← hm₂, hpost, VG.Proof.CmacAes.Stream.X86_64.callEntry_bytes s h.stkK (by rcases h.klen with h | h | h <;> omega)]

theorem ek_rel (v : Ctr32Impl) {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ Kp W S : Addr, ∃ KL : Nat,
      VG.Proof.CmacAes.Stream.X86_64.EArgs s₁ Kp W S KL ∧ VG.Proof.CmacAes.Stream.X86_64.EArgs s₂ Kp W S KL ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (.call v.expand.name v.expand.code) fun _ _ => True := by
  refine RelCT.callEx v.expandOk v.expandCt fun s₁ s₂ hp => ?_
  obtain ⟨Kp, W, S, KL, h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨_, _, _, _, h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes, hsp⟩
  simp only [Proof.Aes.expandKeyX86_64, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
    h₁.rdi, h₁.rsi, h₁.rdx, h₁.rcx, h₂.rdi, h₂.rsi, h₂.rdx, h₂.rcx, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

end VG.Proof.CmacAes.Stream.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Common`. -/
section

/-!
# Streaming AES-CMAC on x86-64: arithmetic and memory

The number of bytes held back, as the code computes it from `count`
(`held_bv`); immediates; the copy of a block a word at a time (`copyMem`).
-/

namespace VG.Proof.CmacAes.Stream.X86_64

open VG VG.X86_64
open VG.Proof.Cmac.Stream (held held_pos held_zero)

/-! ## Arithmetic -/

theorem sx1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
theorem sx15 : BitVec.signExtend 64 (15 : BitVec 32) = 15 := by decide
theorem sx240 : BitVec.signExtend 64 (240 : BitVec 32) = BitVec.ofNat 64 240 := by decide
theorem sx272 : BitVec.signExtend 64 (272 : BitVec 32) = BitVec.ofNat 64 272 := by decide
theorem sx288 : BitVec.signExtend 64 (288 : BitVec 32) = BitVec.ofNat 64 288 := by decide

theorem and15 (x : BitVec 64) : (x &&& 15).toNat = x.toNat % 16 := by
  rw [BitVec.toNat_and, show (15 : BitVec 64).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- The number of bytes held back for a nonzero `count`, as `sub 1; and 15; add 1` computes it. -/
theorem held_bv (c : BitVec 64) (h : c ≠ 0) :
    ((c - 1) &&& 15) + 1 = BitVec.ofNat 64 (held c.toNat) := by
  have hc : c.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
  rw [held_pos (by omega)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, VG.Proof.CmacAes.Stream.X86_64.and15, BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
  have := c.isLt
  omega

theorem beq_zero_iff (c : BitVec 64) : (c == 0) = decide (c.toNat = 0) := by
  by_cases h : c = 0
  · subst h; rfl
  · have : c.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
    simpa [this] using h

theorem toNat_add_lt (p : Addr) {d k : Nat} (h : p.toNat + k ≤ 2 ^ 64) (hd : d < k) :
    (p + BitVec.ofNat 64 d).toNat = p.toNat + d := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : d < 2 ^ 64)]
  exact Nat.mod_eq_of_lt (by omega)

theorem rsi_ofNat {s₀ : State} {R : Nat} (h : (s₀.gpr .rsi).toNat = R) (_hR : R = 10 ∨ R = 12 ∨ R = 14) :
    s₀.gpr .rsi = BitVec.ofNat 64 R :=
  BitVec.eq_of_toNat_eq (by rw [h, VG.Proof.CmacAes.Stream.X86_64.toNat_ofNat (by omega)])

/-! ## Copying a block a word at a time -/

/-- The memory after copying the block at `p` to `o`, a word at a time. -/
def copyMem (m : Mem) (o p : Addr) : Mem :=
  let m₁ := m.writeW o (m.readW p 64)
  m₁.writeW (o + BitVec.ofNat 64 8) (m₁.readW (p + BitVec.ofNat 64 8) 64)

theorem copyMem_frame (m : Mem) (o p : Addr) : Frame [⟨o, 16⟩] m (VG.Proof.CmacAes.Stream.X86_64.copyMem m o p) :=
  Proof.CmacAes.X86_64.frame_store2 _ _ _

theorem copyMem_bytes (m : Mem) {o p : Addr} (h : (⟨o, 16⟩ : Region).Disjoint ⟨p, 16⟩) :
    Spec.Aes.bytesAt (VG.Proof.CmacAes.Stream.X86_64.copyMem m o p) o 16 = Spec.Aes.bytesAt m p 16 := by
  have g : Frame [⟨o, 8⟩] m (m.writeW o (m.readW p 64)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  rw [VG.Proof.CmacAes.Stream.X86_64.copyMem, Proof.Cmac.bytesAt_store2,
    g.readW (r := ⟨p + BitVec.ofNat 64 8, 8⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (h.sub_left (Region.sub_prefix (by decide))).sub_right
          (Offset.sub_base p (d := 8) (n := 8) (k := 16) (by decide)) |>.symm) (by decide),
    Proof.Cmac.le8_readW, Proof.Cmac.le8_readW, ← Proof.Cmac.bytesAt_split]

/-! ## Bytes written -/

section
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
  simp only [Spec.Aes.bytesAt, List.getElem_map, List.getElem_range, VG.Proof.CmacAes.Stream.X86_64.writeBytes_at m q xs (by omega : i < 2 ^ 64),
    h1, ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some]

/-- Bytes `[0, r)` from `p` stay, and the bytes `xs` follow them. -/
theorem bytesAt_writeBytes (m : Mem) (p : Addr) (r : Nat) (xs : List Byte) (h : r + xs.length < 2 ^ 64) :
    Spec.Aes.bytesAt (writeBytes m (p + BitVec.ofNat 64 r) xs) p (r + xs.length) =
      Spec.Aes.bytesAt m p r ++ xs := by
  rw [Proof.Cmac.Stream.bytesAt_append, VG.Proof.CmacAes.Stream.X86_64.bytesAt_writeBytes_self _ _ (by omega)]
  congr 1
  simp only [Spec.Aes.bytesAt]
  apply List.map_congr_left
  intro i hi
  exact writeBytes_before m p xs (List.mem_range.mp hi) (by omega)

end

end VG.Proof.CmacAes.Stream.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Copy`. -/
section

/-!
# Streaming AES-CMAC on x86-64: copying bytes

`copy` copies the `rcx` bytes at `r13` to `rdx`, a byte at a time (none if
`rcx` is 0), changing only `rax`, `r10` and the flags.
-/

namespace VG.Proof.CmacAes.Stream.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.CmacAes.Stream.X86_64 VG.WriteBytes
open VG.Proof.CmacAes.X86_64 (succ_ofNat bytesAt_succ)

theorem copyStep_ok (s : State) {P C : Addr} {i L : Nat} (hc : s.gpr .r13 = P) (hd : s.gpr .rdx = C)
    (hi : s.gpr .r10 = BitVec.ofNat 64 i) (h8 : s.gpr .rcx = BitVec.ofNat 64 L)
    (r : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) 1) (w : InRegions s.wr (C + BitVec.ofNat 64 i) 1) :
    ∃ s', runBlock isa copyBody s = some s' ∧
      s'.mem = s.mem.writeW (C + BitVec.ofNat 64 i) (s.mem (P + BitVec.ofNat 64 i)) ∧
      s'.gpr .r10 = BitVec.ofNat 64 i + 1 ∧
      s'.zf = some (BitVec.ofNat 64 i + 1 - BitVec.ofNat 64 L == 0) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ea₁ : s.gpr .r13 + s.gpr .r10 * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 = P + BitVec.ofNat 64 i := by
    rw [hc, hi, BitVec.mul_one]; simp
  have ea₂ : s.gpr .rdx + s.gpr .r10 * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 = C + BitVec.ofNat 64 i := by
    rw [hd, hi, BitVec.mul_one]; simp
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, BitVec.reduceSignExtend, copyBody, srcByte, dstByte, runBlock_cons, runStep_some,
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

/-- What `copy` leaves. -/
structure Copied (s : State) (C : Addr) (xs : List Byte) (s' : State) : Prop where
  mem : s'.mem = writeBytes s.mem C xs
  other : ∀ r, r ≠ .rax → r ≠ .r10 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem copy_ok (s : State) {P C : Addr} {L : Nat} (hL : L < 2 ^ 64) (hc : s.gpr .r13 = P)
    (hd : s.gpr .rdx = C) (h8 : s.gpr .rcx = BitVec.ofNat 64 L)
    (hr : ∀ i < L, InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < L, InRegions s.wr (C + BitVec.ofNat 64 i) 1)
    (hdis : (⟨P, L⟩ : Region).Disjoint ⟨C, L⟩) :
    WP isa copy s (VG.Proof.CmacAes.Stream.X86_64.Copied s C (Spec.Aes.bytesAt s.mem P L)) := by
  obtain ⟨s₁, run₁, r10₁, zf₁, g₁, m₁, rd₁, wr₁⟩ : ∃ s₁,
      runBlock isa [.mov32 .r10 (.imm 0), .alu .test .rcx (.reg .rcx)] s = some s₁ ∧
      s₁.gpr .r10 = BitVec.ofNat 64 0 ∧ s₁.zf = some (decide (L = 0)) ∧
      (∀ r, r ≠ .r10 → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu,
        State.setReg32, Option.map_some, Option.bind_some]
      rfl, ?_⟩
    simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags, zf_arithFlags, mem_setReg,
      mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, ite_true, ite_false,
      BitVec.and_self, h8, VG.Proof.CmacAes.Stream.X86_64.beq_zero_iff, VG.Proof.CmacAes.Stream.X86_64.toNat_ofNat hL]
    exact ⟨trivial, trivial, fun r h => by simp [h], trivial⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  by_cases hL0 : L = 0
  · subst hL0
    refine WP.ite true (by show s₁.zf = _; rw [zf₁]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    exact ⟨by rw [m₁]; simp [Spec.Aes.bytesAt, writeBytes_nil], fun r _ h => g₁ r h, rd₁, wr₁⟩
  refine WP.ite false (by show s₁.zf = _; rw [zf₁]; simp [hL0]) (fun h => by cases h) fun _ => ?_
  refine WP.loop (M := isa) (body := .block copyBody) (c := .ne)
    (fun (n : Nat) (t : State) => ∃ i, n = L - i ∧ i < L ∧ t.gpr .r10 = BitVec.ofNat 64 i ∧
      t.mem = writeBytes s.mem C (Spec.Aes.bytesAt s.mem P i) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (L - 0) _
    ⟨0, rfl, by omega, r10₁, by rw [m₁]; simp [Spec.Aes.bytesAt, writeBytes_nil],
      fun r _ h₂ => g₁ r h₂, rd₁, wr₁⟩
  rintro n t ⟨i, rfl, hi, r10, mem, g, rd, wr⟩
  obtain ⟨t', run', mem', r10', zf', g', rd', wr'⟩ := VG.Proof.CmacAes.Stream.X86_64.copyStep_ok t
    (by rw [g _ (by decide) (by decide), hc]) (by rw [g _ (by decide) (by decide), hd]) r10
    (by rw [g _ (by decide) (by decide), h8])
    (by rw [rd, wr]; exact hr i hi) (by rw [wr]; exact hw i hi)
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hlen : (Spec.Aes.bytesAt s.mem P i).length = i := by simp [Spec.Aes.bytesAt]
  have hx : writeBytes s.mem C (Spec.Aes.bytesAt s.mem P i) (P + BitVec.ofNat 64 i) = s.mem (P + BitVec.ofNat 64 i) :=
    (writeBytes_frame s.mem C _ (R := ⟨C, i⟩) (by rw [hlen]; exact Region.contains_self _ _)) _
      fun r hr hcon => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hdis _ (Offset.contains_base P (by omega) (by omega)) (Region.sub_prefix (by omega) _ hcon)
  have hmem : t'.mem = writeBytes s.mem C (Spec.Aes.bytesAt s.mem P (i + 1)) := by
    rw [mem', mem, hx, VG.Proof.CmacAes.X86_64.bytesAt_succ, writeBytes_snoc s.mem C (Spec.Aes.bytesAt s.mem P i)
      (s.mem (P + BitVec.ofNat 64 i)) (by rw [hlen]; omega), hlen]
  have hz : t'.zf = some (decide (i + 1 = L)) := by
    rw [zf', succ_ofNat, Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
  have gg : ∀ r, r ≠ .rax → r ≠ .r10 → t'.gpr r = s.gpr r := fun r h₁ h₂ => by rw [g' r h₁ h₂, g r h₁ h₂]
  by_cases he : i + 1 = L
  · left
    exact ⟨by simp [eval, hz, he], by rw [hmem, he], gg, by rw [rd', rd], by rw [wr', wr]⟩
  · right
    refine ⟨by simp [eval, hz, he], L - (i + 1), by omega, i + 1, rfl, by omega, by rw [r10', succ_ofNat], hmem, gg,
      by rw [rd', rd], by rw [wr', wr]⟩

end VG.Proof.CmacAes.Stream.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.Stream.X86_64.AbsorbBlocks`. -/
section

section

/-!
# Streaming AES-CMAC on x86-64: `vg_cmac_aes_absorb`'s saved registers

`absorb` saves the six callee-saved registers it uses at `scratch + 2176`,
where the functions it calls do not write, and restores them at the end.
-/

namespace VG.Proof.CmacAes.Stream.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.CmacAes.Stream.X86_64
open VG.Impl.CmacAes.X86_64 (at_)
open VG.Proof.CmacAes.X86_64 (offset_nat readW_writeW_other)

/-- The memory after saving the registers at `S + 2176`. -/
def absSavedMem (s : State) (S : Addr) : Mem :=
  saved.foldl (fun m (r, d) => m.writeW (S + BitVec.ofNat 64 d) (s.gpr r)) s.mem

theorem absSaved_read (s : State) (S : Addr) :
    (VG.Proof.CmacAes.Stream.X86_64.absSavedMem s S).readW (S + BitVec.ofNat 64 2176) 64 = s.gpr .rbx ∧
    (VG.Proof.CmacAes.Stream.X86_64.absSavedMem s S).readW (S + BitVec.ofNat 64 2184) 64 = s.gpr .rbp ∧
    (VG.Proof.CmacAes.Stream.X86_64.absSavedMem s S).readW (S + BitVec.ofNat 64 2192) 64 = s.gpr .r12 ∧
    (VG.Proof.CmacAes.Stream.X86_64.absSavedMem s S).readW (S + BitVec.ofNat 64 2200) 64 = s.gpr .r13 ∧
    (VG.Proof.CmacAes.Stream.X86_64.absSavedMem s S).readW (S + BitVec.ofNat 64 2208) 64 = s.gpr .r14 ∧
    (VG.Proof.CmacAes.Stream.X86_64.absSavedMem s S).readW (S + BitVec.ofNat 64 2216) 64 = s.gpr .r15 := by
  simp only [VG.Proof.CmacAes.Stream.X86_64.absSavedMem, saved, sOff, List.foldl, Nat.reduceAdd]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [readW_writeW_other _ _ _ (by decide) (by decide) (by decide),
      readW_writeW_other _ _ _ (by decide) (by decide) (by decide),
      readW_writeW_other _ _ _ (by decide) (by decide) (by decide),
      readW_writeW_other _ _ _ (by decide) (by decide) (by decide),
      readW_writeW_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
  · rw [readW_writeW_other _ _ _ (by decide) (by decide) (by decide),
      readW_writeW_other _ _ _ (by decide) (by decide) (by decide),
      readW_writeW_other _ _ _ (by decide) (by decide) (by decide),
      readW_writeW_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
  · rw [readW_writeW_other _ _ _ (by decide) (by decide) (by decide),
      readW_writeW_other _ _ _ (by decide) (by decide) (by decide),
      readW_writeW_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
  · rw [readW_writeW_other _ _ _ (by decide) (by decide) (by decide),
      readW_writeW_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
  · rw [readW_writeW_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
  · rw [Mem.readW_writeW_self64]

theorem slot_contains (b : Addr) {d : Nat} (h₁ : 2176 ≤ d) (h₂ : d + 8 ≤ 2224) :
    (⟨b + BitVec.ofNat 64 2176, 48⟩ : Region).Contains (b + BitVec.ofNat 64 d) 8 := by
  rw [show b + BitVec.ofNat 64 d = (b + BitVec.ofNat 64 2176) + BitVec.ofNat 64 (d - 2176) from
    (Offset.add_add_eq b (by omega)).symm]
  exact Offset.contains_base _ (by omega) (by omega)

/-- Saving the registers changes only their slots. -/
theorem absSavedMem_frame (s : State) (S : Addr) :
    Frame [⟨S + BitVec.ofNat 64 2176, 48⟩] s.mem (VG.Proof.CmacAes.Stream.X86_64.absSavedMem s S) := by
  simp only [VG.Proof.CmacAes.Stream.X86_64.absSavedMem, saved, sOff, List.foldl, Nat.reduceAdd]
  exact (((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (VG.Proof.CmacAes.Stream.X86_64.slot_contains _ (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (VG.Proof.CmacAes.Stream.X86_64.slot_contains _ (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (VG.Proof.CmacAes.Stream.X86_64.slot_contains _ (by decide) (by decide))).writeW (List.mem_singleton_self _) _
    (VG.Proof.CmacAes.Stream.X86_64.slot_contains _ (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (VG.Proof.CmacAes.Stream.X86_64.slot_contains _ (by decide) (by decide))).writeW (List.mem_singleton_self _) _
    (VG.Proof.CmacAes.Stream.X86_64.slot_contains _ (by decide) (by decide)))

theorem save_ok (s : State) {S : Addr} (hS : s.gpr .r9 = S)
    (hw : ∀ d, 2176 ≤ d → d + 8 ≤ 2224 → InRegions s.wr (S + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa save s = some s' ∧
      s'.gpr .rbx = s.gpr .rdi ∧ s'.gpr .rbp = s.gpr .rsi ∧ s'.gpr .r13 = s.gpr .rcx ∧
      s'.gpr .r14 = s.gpr .r8 ∧ s'.gpr .r15 = S ∧ s'.gpr .rdx = s.gpr .rdx ∧
      s'.gpr .rsp = s.gpr .rsp ∧ s'.zf = some (s.gpr .rdx == 0) ∧
      s'.mem = VG.Proof.CmacAes.Stream.X86_64.absSavedMem s S ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [save, saved, sOff, List.map, List.cons_append, List.nil_append, runBlock_cons,
      runStep_some, runBlock_nil, at_, exec, readSrc, State.store64, State.ea, offset_nat, hS, Nat.reduceAdd,
      hw 2176 (by decide) (by decide), hw 2184 (by decide) (by decide), hw 2192 (by decide) (by decide),
      hw 2200 (by decide) (by decide), hw 2208 (by decide) (by decide), hw 2216 (by decide) (by decide),
      ite_true, Option.map_some, execAlu, Option.bind_some]
    rfl, ?_⟩
  simp only [reduceCtorEq, ↓reduceIte, and_self, gpr_setReg, gpr_arithFlags, zf_arithFlags, mem_setReg,
    mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags,
    BitVec.and_self, hS]
  refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, ?_, trivial⟩
  simp only [VG.Proof.CmacAes.Stream.X86_64.absSavedMem, saved, sOff, List.foldl, Nat.reduceAdd]

theorem restore_ok (s : State) {B : Addr} (hb : s.gpr .r15 = B)
    (hr : ∀ d, 2176 ≤ d → d + 8 ≤ 2224 → InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa restore s = some s' ∧
      s'.gpr .rbx = s.mem.readW (B + BitVec.ofNat 64 2176) 64 ∧
      s'.gpr .rbp = s.mem.readW (B + BitVec.ofNat 64 2184) 64 ∧
      s'.gpr .r12 = s.mem.readW (B + BitVec.ofNat 64 2192) 64 ∧
      s'.gpr .r13 = s.mem.readW (B + BitVec.ofNat 64 2200) 64 ∧
      s'.gpr .r14 = s.mem.readW (B + BitVec.ofNat 64 2208) 64 ∧
      s'.gpr .r15 = s.mem.readW (B + BitVec.ofNat 64 2216) 64 ∧
      s'.gpr .rsp = s.gpr .rsp ∧ s'.mem = s.mem := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, restore, saved, sOff, List.map, runBlock_cons, runStep_some,
      runBlock_nil, at_, exec, readSrc, State.load64, State.ea, offset_nat, gpr_setReg, mem_setReg,
      rd_setReg, wr_setReg, Option.map_some, hb, Nat.reduceAdd,
      hr 2176 (by decide) (by decide), hr 2184 (by decide) (by decide), hr 2192 (by decide) (by decide),
      hr 2200 (by decide) (by decide), hr 2208 (by decide) (by decide), hr 2216 (by decide) (by decide)]
    rfl, ?_⟩
  simp only [reduceCtorEq, ↓reduceIte, and_self, gpr_setReg, mem_setReg]

end VG.Proof.CmacAes.Stream.X86_64

end

/-!
# Streaming AES-CMAC on x86-64: `vg_cmac_aes_absorb`'s straight-line code

What each piece of code between the copies and calls computes, in terms of
`count` (`c`) and `len` (`L`): the bytes held back `h = held c`, the bytes
copied after them `f = min L (16 - h)`, the data left `L - f`, whether to
chain the block held back (`b1`), the blocks chained after it (`nb`), and the
rest (`rest`).
-/

namespace VG.Proof.CmacAes.Stream.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.CmacAes.Stream.X86_64
open VG.Proof.Cmac.Stream (held held_le)

/-! ## The numbers -/

/-- The bytes copied after the `held c` held back. -/
def fOf (c L : Nat) : Nat := min L (16 - held c)

/-- The data left after them. -/
def leftOf (c L : Nat) : Nat := L - VG.Proof.CmacAes.Stream.X86_64.fOf c L

/-- The number of blocks the first call chains: the block held back, if data is left. -/
def b1Of (c L : Nat) : Nat := if VG.Proof.CmacAes.Stream.X86_64.leftOf c L = 0 then 0 else 1

/-- The number of blocks the second call chains: those of the data left but its
last 1 to 16 bytes. -/
def nbOf (c L : Nat) : Nat := if VG.Proof.CmacAes.Stream.X86_64.leftOf c L = 0 then 0 else (VG.Proof.CmacAes.Stream.X86_64.leftOf c L - 1) / 16

/-- The bytes copied to the start of the bytes held back at the end. -/
def restOf (c L : Nat) : Nat := VG.Proof.CmacAes.Stream.X86_64.leftOf c L - 16 * VG.Proof.CmacAes.Stream.X86_64.nbOf c L

theorem f_le (c L : Nat) : VG.Proof.CmacAes.Stream.X86_64.fOf c L ≤ L ∧ VG.Proof.CmacAes.Stream.X86_64.fOf c L + held c ≤ 16 := by
  have := held_le c; unfold VG.Proof.CmacAes.Stream.X86_64.fOf; omega

theorem nb_le (c L : Nat) : VG.Proof.CmacAes.Stream.X86_64.fOf c L + 16 * VG.Proof.CmacAes.Stream.X86_64.nbOf c L + VG.Proof.CmacAes.Stream.X86_64.restOf c L = L := by
  have := VG.Proof.CmacAes.Stream.X86_64.f_le c L; unfold VG.Proof.CmacAes.Stream.X86_64.restOf VG.Proof.CmacAes.Stream.X86_64.nbOf VG.Proof.CmacAes.Stream.X86_64.leftOf; split <;> omega

/-! ## Arithmetic on registers -/

theorem sub16 {h : Nat} (hh : h ≤ 16) :
    BitVec.setWidth 64 (16 : BitVec 32) - BitVec.ofNat 64 h = BitVec.ofNat 64 (16 - h) :=
  Offset.ofNat_sub_ofNat hh

/-- `16 nb` for the data left `x > 0`, as `sub 1; mov; and 15; sub` computes it. -/
theorem nb16_bv {x : Nat} (hx : 0 < x) (hx' : x < 2 ^ 64) :
    BitVec.ofNat 64 x - 1 - ((BitVec.ofNat 64 x - 1) &&& 15) = BitVec.ofNat 64 (16 * ((x - 1) / 16)) := by
  apply BitVec.eq_of_toNat_eq
  have e : (BitVec.ofNat 64 x - 1).toNat = x - 1 := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]; omega
  rw [BitVec.toNat_sub, VG.Proof.CmacAes.Stream.X86_64.and15, e, BitVec.toNat_ofNat]
  omega

theorem shr4 {n : Nat} (hn : 16 * n < 2 ^ 64) :
    BitVec.ofNat 64 (16 * n) >>> 4 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

/-! ## `held`: the bytes held back -/

theorem held_wp {s : State} {c : Nat} (hc : c < 2 ^ 64) (hd : s.gpr .rdx = BitVec.ofNat 64 c)
    (hz : s.zf = some (s.gpr .rdx == 0)) :
    WP isa held s fun s' => s'.gpr .rax = BitVec.ofNat 64 (held c) ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  by_cases h0 : c = 0
  · subst h0
    refine WP.ite true (by show s.zf = _; rw [hz, hd]; rfl) (fun _ => ?_) (fun h => by cases h)
    refine WP.of_runBlock ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32, Option.map_some]
      rfl, ?_⟩
    simp only [gpr_setReg, mem_setReg, rd_setReg, wr_setReg, ite_true]
    exact ⟨rfl, fun r h => by simp [h], trivial, trivial, trivial⟩
  · have hne : BitVec.ofNat 64 c ≠ 0 := fun e => h0 (by
      have := congrArg BitVec.toNat e; rwa [VG.Proof.CmacAes.Stream.X86_64.toNat_ofNat hc] at this)
    refine WP.ite false (by show s.zf = _; rw [hz, hd, beq_eq_false_iff_ne.mpr hne]) (fun h => by cases h)
      fun _ => ?_
    refine WP.of_runBlock ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some,
        Option.map_some]
      rfl, ?_⟩
    simp only [gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg,
      wr_arithFlags, ite_true, hd, VG.Proof.CmacAes.Stream.X86_64.sx1, VG.Proof.CmacAes.Stream.X86_64.sx15]
    refine ⟨by rw [VG.Proof.CmacAes.Stream.X86_64.held_bv _ hne, VG.Proof.CmacAes.Stream.X86_64.toNat_ofNat hc], fun r h => by simp [h], trivial, trivial, trivial⟩

/-! ## `fill`: how many bytes to copy, and where -/

theorem fill_wp {s : State} {St : Addr} {c L : Nat} (hL : L < 2 ^ 64) (hax : s.gpr .rax = BitVec.ofNat 64 (held c))
    (h14 : s.gpr .r14 = BitVec.ofNat 64 L) (hbx : s.gpr .rbx = St) :
    WP isa fill s fun s' => s'.gpr .rcx = BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.X86_64.fOf c L) ∧
      s'.gpr .rdx = St + BitVec.ofNat 64 (288 + held c) ∧
      (∀ r, r ≠ .rcx → r ≠ .rdx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hh := held_le c
  obtain ⟨s₁, run₁, rcx₁, cf₁, g₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [.mov32 .rcx (.imm 16),
      .alu .sub .rcx (.reg .rax), .alu .cmp .r14 (.reg .rcx)] s = some s₁ ∧
      s₁.gpr .rcx = BitVec.ofNat 64 (16 - held c) ∧ s₁.cf = some (decide (L < 16 - held c)) ∧
      (∀ r, r ≠ .rcx → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu,
        State.setReg32, Option.map_some, Option.bind_some]
      rfl, ?_⟩
    simp only [gpr_setReg, gpr_arithFlags, cf_arithFlags, mem_setReg, mem_arithFlags, rd_setReg,
      rd_arithFlags, wr_setReg, wr_arithFlags, ite_true, reduceCtorEq, ite_false, hax, h14, VG.Proof.CmacAes.Stream.X86_64.sub16 hh,
      VG.Proof.CmacAes.Stream.X86_64.toNat_ofNat hL, VG.Proof.CmacAes.Stream.X86_64.toNat_ofNat (show 16 - held c < 2 ^ 64 by omega)]
    exact ⟨trivial, trivial, fun r h => by simp [h], trivial, trivial, trivial⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (Q := fun (s₂ : State) => s₂.gpr .rcx = BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.X86_64.fOf c L) ∧
    (∀ r, r ≠ .rcx → s₂.gpr r = s.gpr r) ∧ s₂.mem = s.mem ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr) ?_ fun s₂ h₂ => ?_)
  · by_cases hl : L < 16 - held c
    · refine WP.ite true (by show s₁.cf = _; rw [cf₁]; simp [hl]) (fun _ => ?_) (fun h => by cases h)
      refine WP.of_runBlock ⟨_, by
        simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some]
        rfl, ?_⟩
      simp only [gpr_setReg, mem_setReg, rd_setReg, wr_setReg, ite_true]
      refine ⟨by rw [g₁ _ (by decide), h14, VG.Proof.CmacAes.Stream.X86_64.fOf, Nat.min_eq_left (by omega)],
        fun r h => by simp [h, g₁ r h], m₁, rd₁, wr₁⟩
    · refine WP.ite false (by show s₁.cf = _; rw [cf₁]; simp [hl]) (fun h => by cases h) fun _ => ?_
      refine WP.block_nil ⟨by rw [rcx₁, VG.Proof.CmacAes.Stream.X86_64.fOf, Nat.min_eq_right (by omega)], g₁, m₁, rd₁, wr₁⟩
  · obtain ⟨rcx₂, g₂, m₂, rd₂, wr₂⟩ := h₂
    refine WP.of_runBlock ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.map_some,
        Option.bind_some]
      rfl, ?_⟩
    simp only [gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg,
      wr_arithFlags, ite_true, reduceCtorEq, ite_false, g₂ _ (by decide : Reg.rbx ≠ .rcx),
      g₂ _ (by decide : Reg.rax ≠ .rcx), hbx, hax, VG.Proof.CmacAes.Stream.X86_64.sx288, rcx₂]
    refine ⟨trivial, by rw [BitVec.add_assoc, ← BitVec.ofNat_add], fun r h₁ h₂ => by simp [h₂, g₂ r h₁],
      m₂, rd₂, wr₂⟩

/-! ## `chain1`: the arguments of the first call -/

theorem chain1_wp {s : State} {St D S : Addr} {f L : Nat} (hf : f ≤ L) (hL : L < 2 ^ 64)
    (h13 : s.gpr .r13 = D) (hcx : s.gpr .rcx = BitVec.ofNat 64 f) (h14 : s.gpr .r14 = BitVec.ofNat 64 L)
    (hbx : s.gpr .rbx = St) (h15 : s.gpr .r15 = S) :
    WP isa chain1 s fun s' => s'.gpr .r13 = D + BitVec.ofNat 64 f ∧ s'.gpr .r14 = BitVec.ofNat 64 (L - f) ∧
      s'.gpr .r8 = BitVec.ofNat 64 (if L - f = 0 then 0 else 1) ∧ s'.gpr .rdi = St ∧
      s'.gpr .rsi = s.gpr .rbp ∧ s'.gpr .rdx = St + BitVec.ofNat 64 272 ∧
      s'.gpr .rcx = St + BitVec.ofNat 64 288 ∧ s'.gpr .r9 = S ∧
      (∀ r ∈ calleeSaved, r ≠ .r13 → r ≠ .r14 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, r13₁, r14₁, r8₁, zf₁, g₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [.alu .add .r13 (.reg .rcx),
      .mov32 .r8 (.imm 0), .alu .sub .r14 (.reg .rcx)] s = some s₁ ∧
      s₁.gpr .r13 = D + BitVec.ofNat 64 f ∧ s₁.gpr .r14 = BitVec.ofNat 64 (L - f) ∧
      s₁.gpr .r8 = BitVec.ofNat 64 0 ∧ s₁.zf = some (decide (L - f = 0)) ∧
      (∀ r, r ≠ .r13 → r ≠ .r14 → r ≠ .r8 → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr := by
    refine ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu,
        State.setReg32, Option.map_some, Option.bind_some]
      rfl, ?_⟩
    simp only [gpr_setReg, gpr_arithFlags, zf_setReg, zf_arithFlags, mem_setReg, mem_arithFlags, rd_setReg,
      rd_arithFlags, wr_setReg, wr_arithFlags, ite_true, reduceCtorEq, ite_false, h13, h14, hcx,
      Offset.ofNat_sub_ofNat hf, VG.Proof.CmacAes.Stream.X86_64.beq_zero_iff, VG.Proof.CmacAes.Stream.X86_64.toNat_ofNat (show L - f < 2 ^ 64 by omega)]
    exact ⟨trivial, trivial, rfl, trivial, fun r a b c => by simp [a, b, c], trivial, trivial, trivial⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (Q := fun (s₂ : State) => s₂.gpr .r8 = BitVec.ofNat 64 (if L - f = 0 then 0 else 1) ∧
    (∀ r, r ≠ .r8 → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr) ?_ fun s₂ h₂ => ?_)
  · by_cases h0 : L - f = 0
    · refine WP.ite true (by show s₁.zf = _; rw [zf₁]; simp [h0]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      exact ⟨by rw [r8₁]; simp [h0], fun _ _ => rfl, rfl, rfl, rfl⟩
    · refine WP.ite false (by show s₁.zf = _; rw [zf₁]; simp [h0]) (fun h => by cases h) fun _ => ?_
      refine WP.of_runBlock ⟨_, by
        simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32, Option.map_some]
        rfl, ?_⟩
      simp only [gpr_setReg, mem_setReg, rd_setReg, wr_setReg, h0, ↓reduceIte]
      exact ⟨rfl, fun r h => by simp [h], trivial, trivial, trivial⟩
  · obtain ⟨r8₂, g₂, m₂, rd₂, wr₂⟩ := h₂
    have g (r : Reg) (a : r ≠ .r13) (b : r ≠ .r14) (c : r ≠ .r8) : s₂.gpr r = s.gpr r := by
      rw [g₂ r c, g₁ r a b c]
    refine WP.of_runBlock ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.map_some,
        Option.bind_some]
      rfl, ?_⟩
    simp only [gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg,
      wr_arithFlags, ite_true, reduceCtorEq, ite_false, g _ (by decide : Reg.rbx ≠ .r13) (by decide) (by decide),
      g _ (by decide : Reg.rbp ≠ .r13) (by decide) (by decide),
      g _ (by decide : Reg.r15 ≠ .r13) (by decide) (by decide), hbx, h15, VG.Proof.CmacAes.Stream.X86_64.sx272, VG.Proof.CmacAes.Stream.X86_64.sx288,
      g₂ _ (by decide : Reg.r13 ≠ .r8), g₂ _ (by decide : Reg.r14 ≠ .r8), r13₁, r14₁, r8₂]
    refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, fun r hr a b => ?_,
      by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all

/-! ## `chain2`: the arguments of the second call -/

theorem chain2_wp {s : State} {x : Nat} (hx : x < 2 ^ 64) (h14 : s.gpr .r14 = BitVec.ofNat 64 x) :
    WP isa chain2 s fun s' =>
      s'.gpr .r12 = BitVec.ofNat 64 (16 * (if x = 0 then 0 else (x - 1) / 16)) ∧
      s'.gpr .r8 = BitVec.ofNat 64 (if x = 0 then 0 else (x - 1) / 16) ∧ s'.gpr .rdi = s.gpr .rbx ∧
      s'.gpr .rsi = s.gpr .rbp ∧ s'.gpr .rdx = s.gpr .rbx + BitVec.ofNat 64 272 ∧
      s'.gpr .rcx = s.gpr .r13 ∧ s'.gpr .r9 = s.gpr .r15 ∧
      (∀ r ∈ calleeSaved, r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, r12₁, zf₁, g₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [.mov32 .r12 (.imm 0),
      .alu .test .r14 (.reg .r14)] s = some s₁ ∧ s₁.gpr .r12 = BitVec.ofNat 64 0 ∧
      s₁.zf = some (decide (x = 0)) ∧ (∀ r, r ≠ .r12 → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu,
        State.setReg32, Option.map_some, Option.bind_some]
      rfl, ?_⟩
    simp only [gpr_setReg, gpr_arithFlags, zf_arithFlags, mem_setReg, mem_arithFlags, rd_setReg,
      rd_arithFlags, wr_setReg, wr_arithFlags, ite_true, reduceCtorEq, ite_false, h14, BitVec.and_self,
      VG.Proof.CmacAes.Stream.X86_64.beq_zero_iff, VG.Proof.CmacAes.Stream.X86_64.toNat_ofNat hx]
    exact ⟨rfl, trivial, fun r h => by simp [h], trivial, trivial, trivial⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (Q := fun (s₂ : State) =>
    s₂.gpr .r12 = BitVec.ofNat 64 (16 * (if x = 0 then 0 else (x - 1) / 16)) ∧
    (∀ r, r ≠ .r12 → r ≠ .rax → s₂.gpr r = s.gpr r) ∧ s₂.mem = s.mem ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr) ?_
    fun s₂ h₂ => ?_)
  · by_cases h0 : x = 0
    · refine WP.ite true (by show s₁.zf = _; rw [zf₁]; simp [h0]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      exact ⟨by rw [r12₁]; simp [h0], fun r h _ => g₁ r h, m₁, rd₁, wr₁⟩
    · refine WP.ite false (by show s₁.zf = _; rw [zf₁]; simp [h0]) (fun h => by cases h) fun _ => ?_
      refine WP.of_runBlock ⟨_, by
        simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.map_some,
          Option.bind_some]
        rfl, ?_⟩
      simp only [gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg,
        wr_arithFlags, reduceCtorEq, h0, ↓reduceIte, g₁ _ (by decide : Reg.r14 ≠ .r12), h14,
        VG.Proof.CmacAes.Stream.X86_64.sx1, VG.Proof.CmacAes.Stream.X86_64.sx15]
      exact ⟨VG.Proof.CmacAes.Stream.X86_64.nb16_bv (by omega) hx, fun r a b => by simp [a, b, g₁ r a], m₁, rd₁, wr₁⟩
  · obtain ⟨r12₂, g₂, m₂, rd₂, wr₂⟩ := h₂
    refine WP.of_runBlock ⟨_, by
      simp only [↓reduceIte, Nat.reduceLeDiff, Nat.reduceEqDiff, Nat.reduceSub, Nat.reducePow, and_self, BitVec.reduceSignExtend, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
        execAlu, execShift, Option.map_some, Option.bind_some]
      rfl, ?_⟩
    simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, mem_setReg, mem_arithFlags, mem_setFlags, rd_setReg,
      rd_arithFlags, rd_setFlags, wr_setReg, wr_arithFlags, wr_setFlags, ite_true, reduceCtorEq, ite_false,
      g₂ _ (by decide : Reg.rbx ≠ .r12) (by decide), g₂ _ (by decide : Reg.rbp ≠ .r12) (by decide),
      g₂ _ (by decide : Reg.r13 ≠ .r12) (by decide), g₂ _ (by decide : Reg.r15 ≠ .r12) (by decide), r12₂]
    refine ⟨trivial, VG.Proof.CmacAes.Stream.X86_64.shr4 (by split <;> omega), trivial, trivial, trivial, trivial, trivial,
      fun r hr a => ?_, m₂, rd₂, wr₂⟩
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all

/-! ## `rest`: the arguments of the last copy -/

theorem rest_ok {s : State} {D : Addr} {a x n : Nat} (hn : 16 * n ≤ x)
    (h13 : s.gpr .r13 = D + BitVec.ofNat 64 a) (h12 : s.gpr .r12 = BitVec.ofNat 64 (16 * n))
    (h14 : s.gpr .r14 = BitVec.ofNat 64 x) :
    ∃ s', runBlock isa rest s = some s' ∧ s'.gpr .r13 = D + BitVec.ofNat 64 (a + 16 * n) ∧
      s'.gpr .r14 = BitVec.ofNat 64 (x - 16 * n) ∧ s'.gpr .rdx = s.gpr .rbx + BitVec.ofNat 64 288 ∧
      s'.gpr .rcx = BitVec.ofNat 64 (x - 16 * n) ∧
      (∀ r ∈ calleeSaved, r ≠ .r13 → r ≠ .r14 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [rest, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.map_some,
      Option.bind_some]
    rfl, ?_⟩
  simp only [gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg,
    wr_arithFlags, ite_true, reduceCtorEq, ite_false, h13, h12, h14, VG.Proof.CmacAes.Stream.X86_64.sx288, Offset.ofNat_sub_ofNat hn]
  refine ⟨by rw [BitVec.add_assoc, ← BitVec.ofNat_add], trivial, trivial, trivial, fun r hr a b => ?_,
    trivial, trivial, trivial⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all

end VG.Proof.CmacAes.Stream.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.Stream.X86_64.AbsorbCorrect`. -/
section

section

/-!
# Streaming AES-CMAC on x86-64: `vg_cmac_aes_absorb` up to the first call

The code saves the registers, computes the bytes held back `h`, copies `f =
min(len, 16 - h)` bytes after them, and sets up the first call of
`vg_cmac_aes_update`, which chains the block held back if data is left
(`AMid₁`).
-/

namespace VG.Proof.CmacAes.Stream.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.CmacAes.Stream.X86_64 VG.WriteBytes
open VG.Proof.Cmac.Stream (held held_le)

/-- The precondition, by name: the state `St`, the `L` bytes of data at `D`,
the scratch buffer `S` and the rounds `R`. -/
structure APre (s₀ : State) (St D S : Addr) (L R : Nat) : Prop where
  rdi : s₀.gpr .rdi = St
  rcx : s₀.gpr .rcx = D
  r8 : (s₀.gpr .r8).toNat = L
  r9 : s₀.gpr .r9 = S
  rsi : (s₀.gpr .rsi).toNat = R
  sp : 16 ≤ (s₀.gpr .rsp).toNat
  rd : s₀.rd = [⟨D, L⟩]
  wr : s₀.wr = [⟨St, 304⟩, ⟨S, 2304⟩]
  st_d : (⟨St, 304⟩ : Region).Disjoint ⟨D, L⟩
  st_s : (⟨St, 304⟩ : Region).Disjoint ⟨S, 2304⟩
  d_s : (⟨D, L⟩ : Region).Disjoint ⟨S, 2304⟩
  ret_st : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨St, 304⟩
  ret_d : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨D, L⟩
  ret_s : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨S, 2304⟩
  stk_st : (below (s₀.gpr .rsp) 16).Disjoint ⟨St, 304⟩
  stk_d : (below (s₀.gpr .rsp) 16).Disjoint ⟨D, L⟩
  stk_s : (below (s₀.gpr .rsp) 16).Disjoint ⟨S, 2304⟩
  wSt : St.toNat + 304 ≤ 2 ^ 64
  wD : D.toNat + L ≤ 2 ^ 64
  wS : S.toNat + 2304 ≤ 2 ^ 64
  rounds : R = 10 ∨ R = 12 ∨ R = 14

theorem APre.of {s₀ : State} (h : absorbX86_64.pre s₀) :
    VG.Proof.CmacAes.Stream.X86_64.APre s₀ (s₀.gpr .rdi) (s₀.gpr .rcx) (s₀.gpr .r9) (s₀.gpr .r8).toNat (s₀.gpr .rsi).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p⟩ := h
  ⟨rfl, rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p⟩

section
variable {s₀ : State} {St D S : Addr} {L R : Nat} (hp : VG.Proof.CmacAes.Stream.X86_64.APre s₀ St D S L R)
include hp

theorem APre.lt : L < 2 ^ 64 := by rw [← hp.r8]; exact BitVec.isLt _

theorem APre.r8' : s₀.gpr .r8 = BitVec.ofNat 64 L :=
  BitVec.eq_of_toNat_eq (by rw [hp.r8, VG.Proof.CmacAes.Stream.X86_64.toNat_ofNat hp.lt])

theorem APre.rsi' : s₀.gpr .rsi = BitVec.ofNat 64 R := VG.Proof.CmacAes.Stream.X86_64.rsi_ofNat hp.rsi hp.rounds

theorem APre.inSt {d n : Nat} (h : d + n ≤ 304) : InRegions s₀.wr (St + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact ⟨⟨St, 304⟩, by simp, Offset.contains_base _ h (by have := hp.wSt; omega)⟩

theorem APre.inS {d n : Nat} (h : d + n ≤ 2304) : InRegions s₀.wr (S + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact ⟨⟨S, 2304⟩, by simp, Offset.contains_base _ h (by have := hp.wS; omega)⟩

theorem APre.inD {d n : Nat} (h : d + n ≤ L) : InRegions (s₀.rd ++ s₀.wr) (D + BitVec.ofNat 64 d) n := by
  rw [hp.rd]; exact ⟨⟨D, L⟩, by simp, Offset.contains_base _ h (by have := hp.lt; omega)⟩

/-- The arguments of a call of `vg_cmac_aes_update` on `n` blocks at `Dd`,
from a state with the permissions and stack of `s₀`. -/
theorem APre.uargs {s : State} {Dd : Addr} {n : Nat} (hrdi : s.gpr .rdi = St)
    (hrsi : s.gpr .rsi = s₀.gpr .rsi) (hrdx : s.gpr .rdx = St + BitVec.ofNat 64 272) (hrcx : s.gpr .rcx = Dd)
    (hr8 : s.gpr .r8 = BitVec.ofNat 64 n) (hr9 : s.gpr .r9 = S) (hsp : s.gpr .rsp = s₀.gpr .rsp)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hn : 16 * n < 2 ^ 64)
    (hdc : (⟨Dd, 16 * n⟩ : Region).Disjoint ⟨St + BitVec.ofNat 64 272, 16⟩)
    (hds : (⟨Dd, 16 * n⟩ : Region).Disjoint ⟨S, 2176⟩)
    (hstk : (below (s₀.gpr .rsp) 16).Disjoint ⟨Dd, 16 * n⟩) (hwrap : Dd.toNat + 16 * n ≤ 2 ^ 64)
    (hcov : ∃ r' ∈ ([⟨D, L⟩, ⟨St, 304⟩, ⟨S, 2304⟩] : List Region), ∃ off, Dd = r'.base + BitVec.ofNat 64 off ∧
      off + 16 * n ≤ r'.len) :
    VG.Proof.CmacAes.Stream.X86_64.UArgs s St (St + BitVec.ofNat 64 272) Dd S R n := by
  have hw := hp.wSt
  have c272 : Region.Sub ⟨St + BitVec.ofNat 64 272, 16⟩ ⟨St, 304⟩ := Offset.sub_base St (by decide)
  exact
  { rdi := hrdi, rdx := hrdx, rcx := hrcx, r8 := hr8, r9 := hr9, rounds := hp.rounds, hn := hn
    rsi := by rw [hrsi]; exact hp.rsi'
    wc := Offset.base_disjoint St (by decide) (by omega)
    ws := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    dc := hdc, ds := hds
    cs := (hp.st_s.sub_left c272).sub_right (Region.sub_prefix (by decide))
    stkW := by rw [hsp]; exact hp.stk_st.sub_right (Region.sub_prefix (by decide))
    stkD := by rw [hsp]; exact hstk
    stkC := by rw [hsp]; exact hp.stk_st.sub_right c272
    stkS := by rw [hsp]; exact hp.stk_s.sub_right (Region.sub_prefix (by decide))
    wrapC := by rw [VG.Proof.CmacAes.Stream.X86_64.toNat_add_lt St hw (by decide)]; omega
    wrapD := hwrap
    wrapS := by have := hp.wS; omega
    reads := by
      rw [hrd, hwr, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨St, 304⟩, by simp, 0, by simp, by simp⟩
      · exact hcov
      · exact ⟨⟨St, 304⟩, by simp, 272, rfl, by simp⟩
      · exact ⟨⟨S, 2304⟩, by simp, 0, by simp, by simp⟩
    writes := by
      rw [hwr, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨St, 304⟩, by simp, 272, rfl, by simp⟩
      · exact ⟨⟨S, 2304⟩, by simp, 0, by simp, by simp⟩ }

end

/-- The memory after the saves and the first copy. -/
def m4 (s₀ : State) (St D S : Addr) (c L : Nat) : Mem :=
  writeBytes (VG.Proof.CmacAes.Stream.X86_64.absSavedMem s₀ S) (St + BitVec.ofNat 64 (288 + held c))
    (Spec.Aes.bytesAt (VG.Proof.CmacAes.Stream.X86_64.absSavedMem s₀ S) D (VG.Proof.CmacAes.Stream.X86_64.fOf c L))

/-- What the code before the first call leaves. -/
structure AMid₁ (s₀ : State) (St D S : Addr) (L R : Nat) (s : State) : Prop where
  args : VG.Proof.CmacAes.Stream.X86_64.UArgs s St (St + BitVec.ofNat 64 272) (St + BitVec.ofNat 64 288) S R (VG.Proof.CmacAes.Stream.X86_64.b1Of (s₀.gpr .rdx).toNat L)
  rbx : s.gpr .rbx = St
  rbp : s.gpr .rbp = s₀.gpr .rsi
  r13 : s.gpr .r13 = D + BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.X86_64.fOf (s₀.gpr .rdx).toNat L)
  r14 : s.gpr .r14 = BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.X86_64.leftOf (s₀.gpr .rdx).toNat L)
  r15 : s.gpr .r15 = S
  rsp : s.gpr .rsp = s₀.gpr .rsp
  mem : s.mem = VG.Proof.CmacAes.Stream.X86_64.m4 s₀ St D S (s₀.gpr .rdx).toNat L
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem absorbPre_wp {s₀ : State} {St D S : Addr} {L R : Nat} (hp : VG.Proof.CmacAes.Stream.X86_64.APre s₀ St D S L R) :
    WP isa absorbPre s₀ (VG.Proof.CmacAes.Stream.X86_64.AMid₁ s₀ St D S L R) := by
  generalize hc : (s₀.gpr .rdx).toNat = c
  have hcl : c < 2 ^ 64 := by rw [← hc]; exact BitVec.isLt _
  have hdx : s₀.gpr .rdx = BitVec.ofNat 64 c := BitVec.eq_of_toNat_eq (by rw [hc, VG.Proof.CmacAes.Stream.X86_64.toNat_ofNat hcl])
  have hL := hp.lt
  have hw := hp.wSt
  have ⟨hfL, hfh⟩ := VG.Proof.CmacAes.Stream.X86_64.f_le c L
  have hh := held_le c
  obtain ⟨s₁, run₁, rbx₁, rbp₁, r13₁, r14₁, r15₁, rdx₁, rsp₁, zf₁, m₁, rd₁, wr₁⟩ :=
    VG.Proof.CmacAes.Stream.X86_64.save_ok s₀ hp.r9 fun d _ h => hp.inS (by omega)
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.X86_64.held_wp hcl (by rw [rdx₁, hdx]) (by rw [zf₁, rdx₁])) fun s₂ ⟨ax₂, g₂, m₂, rd₂, wr₂⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.X86_64.fill_wp (St := St) hL ax₂ (by rw [g₂ _ (by decide), r14₁, hp.r8'])
    (by rw [g₂ _ (by decide), rbx₁, hp.rdi])) fun s₃ ⟨cx₃, dx₃, g₃, m₃, rd₃, wr₃⟩ => ?_)
  have g (r : Reg) (a : r ≠ .rax) (b : r ≠ .rcx) (c : r ≠ .rdx) : s₃.gpr r = s₁.gpr r := by
    rw [g₃ r b c, g₂ r a]
  have dCp : Region.Sub ⟨St + BitVec.ofNat 64 (288 + held c), VG.Proof.CmacAes.Stream.X86_64.fOf c L⟩ ⟨St, 304⟩ := Offset.sub_base St (by omega)
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.X86_64.copy_ok s₃ (P := D) (L := VG.Proof.CmacAes.Stream.X86_64.fOf c L) (by omega)
    (by rw [g _ (by decide) (by decide) (by decide), r13₁, hp.rcx]) dx₃ cx₃
    (fun i hi => by rw [rd₃, wr₃, rd₂, wr₂, rd₁, wr₁]; exact hp.inD (by omega))
    (fun i hi => by
      rw [wr₃, wr₂, wr₁, Offset.add_add]; exact hp.inSt (by omega))
    ((hp.st_d.sub_left dCp).symm.sub_left (Region.sub_prefix hfL))) fun s₄ h₄ => ?_)
  have g' (r : Reg) (a : r ≠ .rax) (b : r ≠ .rcx) (c : r ≠ .rdx) (d : r ≠ .r10) : s₄.gpr r = s₁.gpr r := by
    rw [h₄.other r a d, g r a b c]
  refine WP.mono (VG.Proof.CmacAes.Stream.X86_64.chain1_wp hfL hL (by rw [g' _ (by decide) (by decide) (by decide) (by decide), r13₁, hp.rcx])
    (by rw [h₄.other _ (by decide) (by decide), cx₃])
    (by rw [g' _ (by decide) (by decide) (by decide) (by decide), r14₁, hp.r8'])
    (by rw [g' _ (by decide) (by decide) (by decide) (by decide), rbx₁, hp.rdi])
    (by rw [g' _ (by decide) (by decide) (by decide) (by decide), r15₁])) fun s₅ h₅ => ?_
  obtain ⟨r13₅, r14₅, r8₅, rdi₅, rsi₅, rdx₅, rcx₅, r9₅, sv₅, m₅, rd₅, wr₅⟩ := h₅
  have k (r : Reg) (hr : r ∈ calleeSaved) (a : r ≠ .r13) (b : r ≠ .r14) : s₅.gpr r = s₁.gpr r := by
    rw [sv₅ r hr a b, g' r (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)
      (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)]
  have hrd : s₅.rd = s₀.rd := by rw [rd₅, h₄.rd, rd₃, rd₂, rd₁]
  have hwr : s₅.wr = s₀.wr := by rw [wr₅, h₄.wr, wr₃, wr₂, wr₁]
  have hsp : s₅.gpr .rsp = s₀.gpr .rsp := by rw [k _ (by simp [calleeSaved]) (by decide) (by decide), rsp₁]
  have hb1 : 16 * VG.Proof.CmacAes.Stream.X86_64.b1Of c L ≤ 16 := by unfold VG.Proof.CmacAes.Stream.X86_64.b1Of; split <;> omega
  have c288 : Region.Sub ⟨St + BitVec.ofNat 64 288, 16 * VG.Proof.CmacAes.Stream.X86_64.b1Of c L⟩ ⟨St, 304⟩ := Offset.sub_base St (by omega)
  have m₀ : s₅.mem = VG.Proof.CmacAes.Stream.X86_64.m4 s₀ St D S c L := by rw [m₅, h₄.mem, m₃, m₂, m₁, VG.Proof.CmacAes.Stream.X86_64.m4]
  subst hc
  refine ⟨hp.uargs rdi₅ (by rw [rsi₅, g' _ (by decide) (by decide) (by decide) (by decide), rbp₁]) rdx₅ rcx₅
      (by rw [r8₅, VG.Proof.CmacAes.Stream.X86_64.b1Of, VG.Proof.CmacAes.Stream.X86_64.leftOf]) r9₅ hsp hrd hwr (by omega)
      (Offset.disjoint St (by omega) (by omega) (by omega))
      ((hp.st_s.sub_left c288).sub_right (Region.sub_prefix (by decide)))
      (hp.stk_st.sub_right c288) (by rw [VG.Proof.CmacAes.Stream.X86_64.toNat_add_lt St hw (by decide)]; omega)
      ⟨⟨St, 304⟩, by simp, 288, rfl, by simp; omega⟩,
    by rw [k _ (by simp [calleeSaved]) (by decide) (by decide), rbx₁, hp.rdi],
    by rw [k _ (by simp [calleeSaved]) (by decide) (by decide), rbp₁],
    r13₅, by rw [r14₅]; rfl, by rw [k _ (by simp [calleeSaved]) (by decide) (by decide), r15₁], hsp, m₀, hrd,
    hwr⟩

end VG.Proof.CmacAes.Stream.X86_64

end

/-!
# Streaming AES-CMAC on x86-64: `vg_cmac_aes_absorb` is correct

After `absorbPre`, the first call chains the block held back if data is left
(`b1`), the second the whole blocks of the data left but its last 1 to 16
bytes (`nb`), and the last copy holds those back. If no data is left (`len ≤
16 - h`), the calls chain nothing and the copy copies nothing, and the data is
appended to the bytes held back (`repr_fill`); otherwise `repr_chain`.
-/

namespace VG.Proof.CmacAes.Stream.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.CmacAes.Stream.X86_64 VG.WriteBytes
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.CmacAes.X86_64 (bytesAt_frame)
open VG.Proof.Cmac.Stream (held held_le)

/-- A region disjoint from every region of a frame is unchanged. -/
theorem frame_bytes {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) :
    Spec.Aes.bytesAt m' p n = Spec.Aes.bytesAt m p n := VG.Proof.CmacAes.X86_64.bytesAt_frame hf hd hn

theorem frame_at {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hp : p.toNat + n ≤ 2 ^ 64) {i : Nat} (hi : i < n) :
    m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i) :=
  hf _ fun r hr hc => hd r hr _ (Offset.contains_base p (by omega) (by omega)) hc

theorem blocksAt_zero (m : Mem) (p : Addr) : Spec.Cmac.blocksAt m p 16 0 = [] := rfl

theorem blocksAt_one (m : Mem) (p : Addr) :
    Spec.Cmac.blocksAt m p 16 1 = [Spec.Aes.bytesAt m p 16] := by
  simp [Spec.Cmac.blocksAt, k0]
where k0 : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

theorem absorb_wp (v : Ctr32Impl) {s₀ : State} (h0 : absorbX86_64.pre s₀) :
    WP isa (absorb v.callee v.suffix) s₀ fun s' => gprPreserved s₀ s' ∧ absorbX86_64.post s₀ s' := by
  have hp := APre.of h0
  generalize s₀.gpr .rdi = St at hp
  generalize s₀.gpr .rcx = D at hp
  generalize s₀.gpr .r9 = S at hp
  generalize (s₀.gpr .r8).toNat = L at hp
  generalize (s₀.gpr .rsi).toNat = R at hp
  obtain ⟨c, hc⟩ : ∃ c, (s₀.gpr .rdx).toNat = c := ⟨_, rfl⟩
  have hL := hp.lt
  have hw := hp.wSt
  have hsw := hp.wS
  have ⟨hfL, hfh⟩ := VG.Proof.CmacAes.Stream.X86_64.f_le c L
  have hsum := VG.Proof.CmacAes.Stream.X86_64.nb_le c L
  have hh := held_le c
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.X86_64.absorbPre_wp hp) fun s₅ h₅ => ?_)
  obtain ⟨args₅, rbx₅, rbp₅, r13₅, r14₅, r15₅, rsp₅, m₅, rd₅, wr₅⟩ := h₅
  rw [hc] at args₅ r13₅ r14₅ m₅
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.X86_64.upd_call v _ args₅) fun s₆ h₆ => ?_)
  have k₆ (r : Reg) (hr : r ∈ calleeSaved) : s₆.gpr r = s₅.gpr r := h₆.saved r hr
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.X86_64.chain2_wp (x := VG.Proof.CmacAes.Stream.X86_64.leftOf c L) (by unfold VG.Proof.CmacAes.Stream.X86_64.leftOf; omega)
    (by rw [k₆ _ (by simp [calleeSaved]), r14₅])) fun s₇ h₇ => ?_)
  obtain ⟨r12₇, r8₇, rdi₇, rsi₇, rdx₇, rcx₇, r9₇, sv₇, m₇, rd₇, wr₇⟩ := h₇
  have hnb : (if VG.Proof.CmacAes.Stream.X86_64.leftOf c L = 0 then 0 else (VG.Proof.CmacAes.Stream.X86_64.leftOf c L - 1) / 16) = VG.Proof.CmacAes.Stream.X86_64.nbOf c L := rfl
  rw [hnb] at r12₇ r8₇
  have k₇ (r : Reg) (hr : r ∈ calleeSaved) (a : r ≠ .r12) : s₇.gpr r = s₅.gpr r := by rw [sv₇ r hr a, k₆ r hr]
  have hsp₇ : s₇.gpr .rsp = s₀.gpr .rsp := by rw [k₇ _ (by simp [calleeSaved]) (by decide), rsp₅]
  have dD : Region.Sub ⟨D + BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.X86_64.fOf c L), 16 * VG.Proof.CmacAes.Stream.X86_64.nbOf c L⟩ ⟨D, L⟩ := Offset.sub_base D (by omega)
  have c272 : Region.Sub ⟨St + BitVec.ofNat 64 272, 16⟩ ⟨St, 304⟩ := Offset.sub_base St (by decide)
  have args₇ := hp.uargs (s := s₇) (Dd := D + BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.X86_64.fOf c L)) (n := VG.Proof.CmacAes.Stream.X86_64.nbOf c L)
    (by rw [rdi₇, k₆ _ (by simp [calleeSaved]), rbx₅]) (by rw [rsi₇, k₆ _ (by simp [calleeSaved]), rbp₅])
    (by rw [rdx₇, k₆ _ (by simp [calleeSaved]), rbx₅]) (by rw [rcx₇, k₆ _ (by simp [calleeSaved]), r13₅]) r8₇
    (by rw [r9₇, k₆ _ (by simp [calleeSaved]), r15₅]) hsp₇ (by rw [rd₇, h₆.rd, rd₅])
    (by rw [wr₇, h₆.wr, wr₅]) (by omega) ((hp.st_d.sub_left c272).symm.sub_left dD)
    ((hp.d_s.sub_left dD).sub_right (Region.sub_prefix (by decide))) (hp.stk_d.sub_right dD)
    (by
      by_cases h0 : VG.Proof.CmacAes.Stream.X86_64.nbOf c L = 0
      · rw [h0]; have := (D + BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.X86_64.fOf c L)).isLt; omega
      · have := hp.wD; rw [VG.Proof.CmacAes.Stream.X86_64.toNat_add_lt D hp.wD (by omega)]; omega)
    ⟨⟨D, L⟩, by simp, VG.Proof.CmacAes.Stream.X86_64.fOf c L, rfl, by simp; omega⟩
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.X86_64.upd_call v _ args₇) fun s₈ h₈ => ?_)
  have k₈ (r : Reg) (hr : r ∈ calleeSaved) : s₈.gpr r = s₇.gpr r := h₈.saved r hr
  obtain ⟨s₉, run₉, r13₉, r14₉, rdx₉, rcx₉, sv₉, m₉, rd₉, wr₉⟩ := VG.Proof.CmacAes.Stream.X86_64.rest_ok (s := s₈) (D := D) (a := VG.Proof.CmacAes.Stream.X86_64.fOf c L)
    (x := VG.Proof.CmacAes.Stream.X86_64.leftOf c L) (n := VG.Proof.CmacAes.Stream.X86_64.nbOf c L) (by unfold VG.Proof.CmacAes.Stream.X86_64.leftOf; omega)
    (by rw [k₈ _ (by simp [calleeSaved]), k₇ _ (by simp [calleeSaved]) (by decide), r13₅])
    (by rw [k₈ _ (by simp [calleeSaved]), r12₇])
    (by rw [k₈ _ (by simp [calleeSaved]), k₇ _ (by simp [calleeSaved]) (by decide), r14₅])
  refine WP.seq (WP.of_runBlock ⟨s₉, run₉, ?_⟩)
  have rd₉' : s₉.rd = s₀.rd := by rw [rd₉, h₈.rd, rd₇, h₆.rd, rd₅]
  have wr₉' : s₉.wr = s₀.wr := by rw [wr₉, h₈.wr, wr₇, h₆.wr, wr₅]
  have dR : Region.Sub ⟨D + BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.X86_64.fOf c L + 16 * VG.Proof.CmacAes.Stream.X86_64.nbOf c L), VG.Proof.CmacAes.Stream.X86_64.restOf c L⟩ ⟨D, L⟩ :=
    Offset.sub_base D (by omega)
  have sR : Region.Sub ⟨St + BitVec.ofNat 64 288, VG.Proof.CmacAes.Stream.X86_64.restOf c L⟩ ⟨St, 304⟩ := Offset.sub_base St (by unfold VG.Proof.CmacAes.Stream.X86_64.restOf VG.Proof.CmacAes.Stream.X86_64.nbOf VG.Proof.CmacAes.Stream.X86_64.leftOf; split <;> omega)
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.X86_64.copy_ok s₉ (P := D + BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.X86_64.fOf c L + 16 * VG.Proof.CmacAes.Stream.X86_64.nbOf c L))
    (C := St + BitVec.ofNat 64 288) (L := VG.Proof.CmacAes.Stream.X86_64.restOf c L) (by omega) r13₉
    (by rw [rdx₉, k₈ _ (by simp [calleeSaved]), k₇ _ (by simp [calleeSaved]) (by decide), rbx₅]) rcx₉
    (fun i hi => by rw [rd₉', wr₉', Offset.add_add]; exact hp.inD (by omega))
    (fun i hi => by rw [wr₉', Offset.add_add]; exact hp.inSt (by unfold VG.Proof.CmacAes.Stream.X86_64.restOf VG.Proof.CmacAes.Stream.X86_64.nbOf VG.Proof.CmacAes.Stream.X86_64.leftOf at hi; split at hi <;> omega))
    ((hp.st_d.sub_left sR).symm.sub_left dR)) fun s₁₀ h₁₀ => ?_)
  have r15₁₀ : s₁₀.gpr .r15 = S := by
    rw [h₁₀.other _ (by decide) (by decide), sv₉ _ (by simp [calleeSaved]) (by decide) (by decide),
      k₈ _ (by simp [calleeSaved]), k₇ _ (by simp [calleeSaved]) (by decide), r15₅]
  obtain ⟨s₁₁, run₁₁, rbx₁₁, rbp₁₁, r12₁₁, r13₁₁, r14₁₁, r15₁₁, rsp₁₁, m₁₁⟩ := VG.Proof.CmacAes.Stream.X86_64.restore_ok s₁₀ r15₁₀
    (fun d _ h => by
      rw [h₁₀.rd, h₁₀.wr, rd₉', wr₉']
      obtain ⟨r, hr, hc⟩ := hp.inS (d := d) (n := 8) (by omega)
      exact ⟨r, List.mem_append_right _ hr, hc⟩)
  refine WP.of_runBlock ⟨s₁₁, run₁₁, ?_⟩
  -- The frames.
  have hlf : (Spec.Aes.bytesAt (VG.Proof.CmacAes.Stream.X86_64.absSavedMem s₀ S) D (VG.Proof.CmacAes.Stream.X86_64.fOf c L)).length = VG.Proof.CmacAes.Stream.X86_64.fOf c L := Proof.Cmac.bytesAt_length _ _ _
  have hlr : (Spec.Aes.bytesAt s₉.mem (D + BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.X86_64.fOf c L + 16 * VG.Proof.CmacAes.Stream.X86_64.nbOf c L)) (VG.Proof.CmacAes.Stream.X86_64.restOf c L)).length =
    VG.Proof.CmacAes.Stream.X86_64.restOf c L := Proof.Cmac.bytesAt_length _ _ _
  have fS : Frame [⟨S + BitVec.ofNat 64 2176, 48⟩] s₀.mem (VG.Proof.CmacAes.Stream.X86_64.absSavedMem s₀ S) := VG.Proof.CmacAes.Stream.X86_64.absSavedMem_frame _ _
  have fC1 : Frame [⟨St + BitVec.ofNat 64 (288 + held c), VG.Proof.CmacAes.Stream.X86_64.fOf c L⟩] (VG.Proof.CmacAes.Stream.X86_64.absSavedMem s₀ S) s₅.mem := by
    rw [m₅, VG.Proof.CmacAes.Stream.X86_64.m4]; exact writeBytes_frame _ _ _ (by rw [hlf]; exact Region.contains_self _ _)
  have f6 : Frame [⟨St + BitVec.ofNat 64 272, 16⟩, ⟨S, 2176⟩, below (s₀.gpr .rsp) 16] s₅.mem s₆.mem := by
    rw [← rsp₅]; exact h₆.frame
  have f8 : Frame [⟨St + BitVec.ofNat 64 272, 16⟩, ⟨S, 2176⟩, below (s₀.gpr .rsp) 16] s₆.mem s₈.mem := by
    rw [← hsp₇, ← m₇]; exact h₈.frame
  have fC2 : Frame [⟨St + BitVec.ofNat 64 288, VG.Proof.CmacAes.Stream.X86_64.restOf c L⟩] s₈.mem s₁₁.mem := by
    rw [m₁₁, h₁₀.mem, m₉]
    exact writeBytes_frame _ _ _ (by rw [← m₉, hlr]; exact Region.contains_self _ _)
  let K : List Region := [⟨S + BitVec.ofNat 64 2176, 48⟩, ⟨St + BitVec.ofNat 64 (288 + held c), VG.Proof.CmacAes.Stream.X86_64.fOf c L⟩,
    ⟨St + BitVec.ofNat 64 272, 16⟩, ⟨S, 2176⟩, below (s₀.gpr .rsp) 16, ⟨St + BitVec.ofNat 64 288, VG.Proof.CmacAes.Stream.X86_64.restOf c L⟩]
  have F5 : Frame K s₀.mem s₅.mem := (fS.mono (by simp [K])).trans (fC1.mono (by simp [K]))
  have F6 : Frame K s₀.mem s₆.mem := F5.trans (f6.mono (by simp [K]))
  have F8 : Frame K s₀.mem s₈.mem := F6.trans (f8.mono (by simp [K]))
  have F11 : Frame K s₀.mem s₁₁.mem := F8.trans (fC2.mono (by simp [K]))
  have hrr : VG.Proof.CmacAes.Stream.X86_64.restOf c L ≤ 16 := by unfold VG.Proof.CmacAes.Stream.X86_64.restOf VG.Proof.CmacAes.Stream.X86_64.nbOf VG.Proof.CmacAes.Stream.X86_64.leftOf; split <;> omega
  -- The key, the data and the return address are in none of these.
  have dK : ∀ r ∈ K, (⟨St, 272⟩ : Region).Disjoint r := by
    intro r hr
    simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base S (by decide))
    · exact Offset.base_disjoint St (by omega) (by omega)
    · exact Offset.base_disjoint St (by omega) (by omega)
    · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    · exact (hp.stk_st.sub_right (Region.sub_prefix (by decide))).symm
    · exact Offset.base_disjoint St (by omega) (by omega)
  have dDat : ∀ r ∈ K, (⟨D, L⟩ : Region).Disjoint r := by
    intro r hr
    simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hp.d_s.sub_right (Offset.sub_base S (by decide))
    · exact hp.st_d.symm.sub_right (Offset.sub_base St (by omega))
    · exact hp.st_d.symm.sub_right (Offset.sub_base St (by decide))
    · exact hp.d_s.sub_right (Region.sub_prefix (by decide))
    · exact hp.stk_d.symm
    · exact hp.st_d.symm.sub_right (Offset.sub_base St (by omega))
  have dRet : ∀ r ∈ K, (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint r := by
    intro r hr
    simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hp.ret_s.sub_right (Offset.sub_base S (by decide))
    · exact hp.ret_st.sub_right (Offset.sub_base St (by omega))
    · exact hp.ret_st.sub_right (Offset.sub_base St (by decide))
    · exact hp.ret_s.sub_right (Region.sub_prefix (by decide))
    · exact Offset.base_disjoint_below _ (by decide)
    · exact hp.ret_st.sub_right (Offset.sub_base St (by omega))
  have k0 : ∀ p : Addr, p + BitVec.ofNat 64 0 = p := fun p => BitVec.add_zero p
  refine ⟨⟨fun r hr => ?_, F11.readW (r := ⟨s₀.gpr .rsp, 8⟩) (Region.contains_self _ _) dRet (by decide)⟩, ?_⟩
  · -- The registers, restored from their slots.
    have Fp : Frame K.tail (VG.Proof.CmacAes.Stream.X86_64.absSavedMem s₀ S) s₁₁.mem :=
      ((fC1.mono (by simp [K])).trans (f6.mono (by simp [K]))).trans
        ((f8.mono (by simp [K])).trans (fC2.mono (by simp [K])))
    have slot (d : Nat) (h₁ : 2176 ≤ d) (h₂ : d + 8 ≤ 2224) :
        s₁₀.mem.readW (S + BitVec.ofNat 64 d) 64 = (VG.Proof.CmacAes.Stream.X86_64.absSavedMem s₀ S).readW (S + BitVec.ofNat 64 d) 64 := by
      rw [← m₁₁]
      have sub : Region.Sub ⟨S + BitVec.ofNat 64 d, 8⟩ ⟨S, 2304⟩ := Offset.sub_base S (by omega)
      refine Fp.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [K, List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact (hp.st_s.sub_left (Offset.sub_base St (by omega))).symm.sub_left sub
      · exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).symm.sub_left sub
      · exact Offset.disjoint_base S (by omega) (by omega)
      · exact hp.stk_s.symm.sub_left sub
      · exact (hp.st_s.sub_left (Offset.sub_base St (by omega))).symm.sub_left sub
    obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆⟩ := VG.Proof.CmacAes.Stream.X86_64.absSaved_read s₀ S
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [rbx₁₁, slot 2176 (by decide) (by decide), a₁]
    · rw [rbp₁₁, slot 2184 (by decide) (by decide), a₂]
    · rw [rsp₁₁, h₁₀.other _ (by decide) (by decide), sv₉ _ (by simp [calleeSaved]) (by decide) (by decide),
        k₈ _ (by simp [calleeSaved]), hsp₇]
    · rw [r12₁₁, slot 2192 (by decide) (by decide), a₃]
    · rw [r13₁₁, slot 2200 (by decide) (by decide), a₄]
    · rw [r14₁₁, slot 2208 (by decide) (by decide), a₅]
    · rw [r15₁₁, slot 2216 (by decide) (by decide), a₆]
  · intro key msg hr hR hcnt hlen
    rw [hp.rdi] at hr ⊢
    rw [hp.rcx, hp.r8]
    rw [hp.r8] at hlen
    have hcm : c = msg.length := by rw [← hc, hcnt, VG.Proof.CmacAes.Stream.X86_64.toNat_ofNat (by omega)]
    subst hcm
    have hRk : R = Spec.Aes.rounds (key.length / 4) := by rw [← hp.rsi]; exact hR
    have hRb : 16 * (R + 1) ≤ 272 := by rcases hp.rounds with h | h | h <;> omega
    have hsch := ((Proof.Cmac.Stream.repr_iff _ _ _ _).mp hr).1.2.1
    rw [← hRk] at hsch
    have ciph : ∀ m : Mem, Frame K s₀.mem m →
        Spec.Cmac.aesWith R (Spec.Aes.bytesAt m St (16 * (R + 1))) = Spec.Cmac.aes key := fun m hf => by
      rw [VG.Proof.CmacAes.Stream.X86_64.frame_bytes hf (fun r hr => (dK r hr).sub_left (Region.sub_prefix hRb)) (by omega), hsch,
        Spec.Cmac.aes, ← hRk]
    -- The data, wherever it is read.
    have dat : ∀ m : Mem, Frame K s₀.mem m → ∀ a b : Nat, a + b ≤ L →
        Spec.Aes.bytesAt m (D + BitVec.ofNat 64 a) b =
          ((Spec.Aes.bytesAt s₀.mem D L).drop a).take b := fun m hf a b hab => by
      rw [Proof.Cmac.Stream.bytesAt_offset m D hab, VG.Proof.CmacAes.Stream.X86_64.frame_bytes hf dDat (by omega)]
    have fS' : Frame K s₀.mem (VG.Proof.CmacAes.Stream.X86_64.absSavedMem s₀ S) := fS.mono (by simp [K])
    -- The chaining value.
    have cv5 : Spec.Aes.bytesAt s₅.mem (St + BitVec.ofNat 64 272) 16 =
        Spec.Aes.bytesAt s₀.mem (St + BitVec.ofNat 64 272) 16 := by
      rw [VG.Proof.CmacAes.Stream.X86_64.frame_bytes fC1 (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint St (by omega) (by omega) (by omega))
          (by decide),
        VG.Proof.CmacAes.Stream.X86_64.frame_bytes fS (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).sub_right (Offset.sub_base S (by decide)))
          (by decide)]
    have cv11 : Spec.Aes.bytesAt s₁₁.mem (St + BitVec.ofNat 64 272) 16 =
        Spec.Aes.bytesAt s₈.mem (St + BitVec.ofNat 64 272) 16 :=
      VG.Proof.CmacAes.Stream.X86_64.frame_bytes fC2 (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint St (by omega) (by omega) (by omega))
        (by decide)
    have out6 := h₆.out
    rw [ciph _ F5] at out6
    have out8 := h₈.out
    rw [m₇, ciph _ F6] at out8
    have hk : ∀ i < 272, s₁₁.mem (St + BitVec.ofNat 64 i) = s₀.mem (St + BitVec.ofNat 64 i) :=
      fun i hi => VG.Proof.CmacAes.Stream.X86_64.frame_at F11 dK (by omega) hi
    have hdl : (Spec.Aes.bytesAt s₀.mem D L).length = L := Proof.Cmac.bytesAt_length _ _ _
    -- The bytes held back so far, and the first `f` bytes of data after them.
    have hb5 : Spec.Aes.bytesAt s₅.mem (St + BitVec.ofNat 64 288) (held msg.length + VG.Proof.CmacAes.Stream.X86_64.fOf msg.length L) =
        Spec.Aes.bytesAt s₀.mem (St + BitVec.ofNat 64 288) (held msg.length) ++
          (Spec.Aes.bytesAt s₀.mem D L).take (VG.Proof.CmacAes.Stream.X86_64.fOf msg.length L) := by
      have e := VG.Proof.CmacAes.Stream.X86_64.bytesAt_writeBytes (VG.Proof.CmacAes.Stream.X86_64.absSavedMem s₀ S) (St + BitVec.ofNat 64 288) (held msg.length)
        (Spec.Aes.bytesAt (VG.Proof.CmacAes.Stream.X86_64.absSavedMem s₀ S) D (VG.Proof.CmacAes.Stream.X86_64.fOf msg.length L)) (by rw [hlf]; omega)
      rw [hlf] at e
      rw [m₅, VG.Proof.CmacAes.Stream.X86_64.m4, ← Offset.add_add, e,
        VG.Proof.CmacAes.Stream.X86_64.frame_bytes fS (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hp.st_s.sub_left (Offset.sub_base St (by omega))).sub_right (Offset.sub_base S (by decide)))
          (by omega)]
      refine congrArg (_ ++ ·) ?_
      have := dat _ fS' 0 (VG.Proof.CmacAes.Stream.X86_64.fOf msg.length L) (by omega)
      rwa [k0, List.drop_zero] at this
    generalize hd : Spec.Aes.bytesAt s₀.mem D L = d at hdl hb5 dat ⊢
    by_cases hx : VG.Proof.CmacAes.Stream.X86_64.leftOf msg.length L = 0
    · -- Everything fits in the block held back.
      have hfL' : VG.Proof.CmacAes.Stream.X86_64.fOf msg.length L = L := by unfold VG.Proof.CmacAes.Stream.X86_64.leftOf at hx; omega
      have hb : VG.Proof.CmacAes.Stream.X86_64.b1Of msg.length L = 0 := by simp [VG.Proof.CmacAes.Stream.X86_64.b1Of, hx]
      have hn : VG.Proof.CmacAes.Stream.X86_64.nbOf msg.length L = 0 := by simp [VG.Proof.CmacAes.Stream.X86_64.nbOf, hx]
      have hr0 : VG.Proof.CmacAes.Stream.X86_64.restOf msg.length L = 0 := by simp [VG.Proof.CmacAes.Stream.X86_64.restOf, hn, hx]
      have m118 : s₁₁.mem = s₈.mem := by
        rw [m₁₁, h₁₀.mem, m₉, hr0, show Spec.Aes.bytesAt s₈.mem
          (D + BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.X86_64.fOf msg.length L + 16 * VG.Proof.CmacAes.Stream.X86_64.nbOf msg.length L)) 0 = [] from rfl, writeBytes_nil]
      refine Proof.Cmac.Stream.repr_fill hr hk (by rw [hdl]; have := (VG.Proof.CmacAes.Stream.X86_64.f_le msg.length L).2; omega) ?_ ?_
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 272) _ = Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 272) _
        rw [cv11, out8, hn, VG.Proof.CmacAes.Stream.X86_64.blocksAt_zero, out6, hb, VG.Proof.CmacAes.Stream.X86_64.blocksAt_zero]
        exact cv5
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 288) _ = Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 288) _ ++ _
        have sub : Region.Sub ⟨St + BitVec.ofNat 64 288, held msg.length + L⟩ ⟨St, 304⟩ :=
          Offset.sub_base St (by omega)
        have dj : ∀ r ∈ [⟨St + BitVec.ofNat 64 272, 16⟩, ⟨S, 2176⟩, below (s₀.gpr .rsp) 16],
            (⟨St + BitVec.ofNat 64 288, held msg.length + L⟩ : Region).Disjoint r := by
          intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact Offset.disjoint St (by omega) (by omega) (by omega)
          · exact (hp.st_s.sub_left sub).sub_right (Region.sub_prefix (by decide))
          · exact (hp.stk_st.sub_right sub).symm
        have hb5' := hb5
        rw [hfL', List.take_of_length_le (by rw [hdl])] at hb5'
        rw [m118, hdl, VG.Proof.CmacAes.Stream.X86_64.frame_bytes f8 dj (by omega), VG.Proof.CmacAes.Stream.X86_64.frame_bytes f6 dj (by omega), hb5']
    · -- The block held back is complete, and more blocks may follow.
      have hlt : 16 - held msg.length < L := by unfold VG.Proof.CmacAes.Stream.X86_64.leftOf VG.Proof.CmacAes.Stream.X86_64.fOf at hx; omega
      have hf' : VG.Proof.CmacAes.Stream.X86_64.fOf msg.length L = 16 - held msg.length := by unfold VG.Proof.CmacAes.Stream.X86_64.fOf; omega
      have hb : VG.Proof.CmacAes.Stream.X86_64.b1Of msg.length L = 1 := by simp [VG.Proof.CmacAes.Stream.X86_64.b1Of, hx]
      have hn : VG.Proof.CmacAes.Stream.X86_64.nbOf msg.length L = Proof.Cmac.Stream.nblocks msg.length L := by
        simp only [VG.Proof.CmacAes.Stream.X86_64.nbOf, hx, ↓reduceIte]
        unfold VG.Proof.CmacAes.Stream.X86_64.leftOf Proof.Cmac.Stream.nblocks
        rw [hf']
      have hb5' := hb5
      rw [hf', Nat.add_sub_cancel' hh] at hb5'
      refine Proof.Cmac.Stream.repr_chain hr hk (by rw [hdl]; exact hlt) ?_ ?_
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 272) _ =
          Spec.Cmac.chain _ (Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 272) _)
            ([Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 288) _ ++ _] ++ _)
        rw [cv11, out8, out6, hb, VG.Proof.CmacAes.Stream.X86_64.blocksAt_one, cv5, Proof.Cmac.chain_append, Proof.Cmac.Stream.blocksAt_eq,
          dat _ F6 _ _ (by omega), hb5', hdl, hf', hn]
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 288) _ = _
        have e := VG.Proof.CmacAes.Stream.X86_64.bytesAt_writeBytes_self s₈.mem (St + BitVec.ofNat 64 288)
          (xs := Spec.Aes.bytesAt s₈.mem (D + BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.X86_64.fOf msg.length L + 16 * VG.Proof.CmacAes.Stream.X86_64.nbOf msg.length L))
            (VG.Proof.CmacAes.Stream.X86_64.restOf msg.length L)) (by rw [Proof.Cmac.bytesAt_length]; omega)
        rw [Proof.Cmac.bytesAt_length] at e
        have hr' : d.length - (16 - held msg.length) - 16 * Proof.Cmac.Stream.nblocks msg.length d.length =
            VG.Proof.CmacAes.Stream.X86_64.restOf msg.length L := by
          rw [hdl, ← hn, ← hf']; rfl
        rw [hr', m₁₁, h₁₀.mem, m₉, e, dat _ F8 _ _ (by omega),
          List.take_of_length_le (by simp only [List.length_drop, hdl]; unfold VG.Proof.CmacAes.Stream.X86_64.restOf VG.Proof.CmacAes.Stream.X86_64.leftOf; omega),
          List.drop_drop, hdl, ← hn, hf']

end VG.Proof.CmacAes.Stream.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Init`. -/
section

/-!
# Streaming AES-CMAC on x86-64: `vg_cmac_aes_init`

The code saves `rbx`, `rbp` and `r12` in the scratch buffer, expands the key
into the state, derives the subkeys after the schedule, zeroes the chaining
value and restores the registers: the state then represents the empty message.
The code between the calls is constant time by the taint analysis, and the
calls by their own proofs (`ek_rel`, `sub_rel`), their arguments pinned by
`IMid₁` and `IMid₂`.
-/

namespace VG.Proof.CmacAes.Stream.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.CmacAes.Stream.X86_64
open VG.Impl.CmacAes.X86_64 (at_)
open VG.Proof.CmacAes.X86_64 (offset_nat bytesAt_frame k0 zero2 zero2_bytes)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- The precondition, by name: the state `St`, the key `Kp` of `KL` bytes
and the scratch buffer `S`. -/
structure IPre (s₀ : State) (St Kp S : Addr) (KL : Nat) : Prop where
  rdi : s₀.gpr .rdi = St
  rsi : s₀.gpr .rsi = Kp
  rdx : (s₀.gpr .rdx).toNat = KL
  rcx : s₀.gpr .rcx = S
  sp : 16 ≤ (s₀.gpr .rsp).toNat
  rd : s₀.rd = [⟨Kp, KL⟩]
  wr : s₀.wr = [⟨St, 304⟩, ⟨S, 2304⟩]
  st_k : (⟨St, 304⟩ : Region).Disjoint ⟨Kp, KL⟩
  st_s : (⟨St, 304⟩ : Region).Disjoint ⟨S, 2304⟩
  k_s : (⟨Kp, KL⟩ : Region).Disjoint ⟨S, 2304⟩
  ret_st : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨St, 304⟩
  ret_k : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨Kp, KL⟩
  ret_s : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨S, 2304⟩
  stk_st : (below (s₀.gpr .rsp) 16).Disjoint ⟨St, 304⟩
  stk_k : (below (s₀.gpr .rsp) 16).Disjoint ⟨Kp, KL⟩
  stk_s : (below (s₀.gpr .rsp) 16).Disjoint ⟨S, 2304⟩
  wSt : St.toNat + 304 ≤ 2 ^ 64
  wK : Kp.toNat + KL ≤ 2 ^ 64
  wS : S.toNat + 2304 ≤ 2 ^ 64
  klen : KL = 16 ∨ KL = 24 ∨ KL = 32

theorem IPre.of {s₀ : State} (h : initX86_64.pre s₀) :
    VG.Proof.CmacAes.Stream.X86_64.IPre s₀ (s₀.gpr .rdi) (s₀.gpr .rsi) (s₀.gpr .rcx) (s₀.gpr .rdx).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p⟩ := h
  ⟨rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p⟩

/-- The rounds, as `shr 2; add 6` computes them from the key length. -/
theorem rounds_bv {KL : Nat} (h : KL = 16 ∨ KL = 24 ∨ KL = 32) :
    BitVec.ofNat 64 KL >>> 2 + BitVec.signExtend 64 (6 : BitVec 32) = BitVec.ofNat 64 (KL / 4 + 6) := by
  rcases h with rfl | rfl | rfl <;> decide

/-- The memory after saving the registers. -/
def initSavedMem (s : State) (S : Addr) : Mem :=
  ((s.mem.writeW (S + BitVec.ofNat 64 2176) (s.gpr .rbx)).writeW (S + BitVec.ofNat 64 2184) (s.gpr .rbp)).writeW
    (S + BitVec.ofNat 64 2192) (s.gpr .r12)

theorem initSavedMem_frame (s : State) (S : Addr) :
    Frame [⟨S + BitVec.ofNat 64 2176, 24⟩] s.mem (VG.Proof.CmacAes.Stream.X86_64.initSavedMem s S) := by
  have c (d : Nat) (hd : d + 8 ≤ 24) : (⟨S + BitVec.ofNat 64 2176, 24⟩ : Region).Contains
      (S + BitVec.ofNat 64 (2176 + d)) 8 := by
    rw [← Offset.add_add]; exact Offset.contains_base _ hd (by omega)
  exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by simpa using c 0 (by decide))).writeW
    (List.mem_singleton_self _) _ (c 8 (by decide))).writeW (List.mem_singleton_self _) _ (c 16 (by decide))

/-! ## Before the first call -/

theorem initPre_ok {s₀ : State} {St Kp S : Addr} {KL : Nat} (hp : VG.Proof.CmacAes.Stream.X86_64.IPre s₀ St Kp S KL) :
    ∃ s₁, runBlock isa initPre s₀ = some s₁ ∧ s₁.gpr .rdi = Kp ∧ s₁.gpr .rsi = BitVec.ofNat 64 KL ∧
      s₁.gpr .rdx = St ∧ s₁.gpr .rcx = S ∧ s₁.gpr .rbx = St ∧ s₁.gpr .rbp = S ∧
      s₁.gpr .r12 = BitVec.ofNat 64 (KL / 4 + 6) ∧ s₁.gpr .rsp = s₀.gpr .rsp ∧
      (∀ r, r ≠ .rbx → r ≠ .rbp → r ≠ .r12 → r ∈ calleeSaved → s₁.gpr r = s₀.gpr r) ∧
      s₁.mem = VG.Proof.CmacAes.Stream.X86_64.initSavedMem s₀ S ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr := by
  have inS (d : Nat) (hd : d + 8 ≤ 2304) : InRegions s₀.wr (S + BitVec.ofNat 64 d) 8 := by
    rw [hp.wr]; exact ⟨⟨S, 2304⟩, by simp, Offset.contains_base _ hd (by have := hp.wS; omega)⟩
  have hKL : s₀.gpr .rdx = BitVec.ofNat 64 KL :=
    BitVec.eq_of_toNat_eq (by rw [hp.rdx, VG.Proof.CmacAes.Stream.X86_64.toNat_ofNat (by rcases hp.klen with h | h | h <;> omega)])
  refine ⟨_, by
    simp (config := {decide := true}) only [initPre, initSaved, sOff, List.map, List.cons_append,
      List.nil_append, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc, execAlu, execShift,
      State.store64, State.ea, offset_nat, Option.bind_some, Option.map_some, gpr_setReg, gpr_arithFlags,
      ite_true, ite_false, hp.rcx, inS 2176 (by decide),
      inS 2184 (by decide), inS 2192 (by decide)]
    rfl, ?_⟩
  simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags, gpr_setFlags, mem_setReg,
    mem_arithFlags, mem_setFlags, rd_setReg, rd_arithFlags, rd_setFlags, wr_setReg, wr_arithFlags,
    wr_setFlags, ite_true, ite_false, hp.rdi, hp.rsi, hp.rcx, hKL, VG.Proof.CmacAes.Stream.X86_64.rounds_bv hp.klen, Nat.reduceAdd]
  refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial,
    fun r h₁ h₂ h₃ hr => ?_, rfl, trivial⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all

theorem initSaved_read (s : State) (S : Addr) :
    (VG.Proof.CmacAes.Stream.X86_64.initSavedMem s S).readW (S + BitVec.ofNat 64 2176) 64 = s.gpr .rbx ∧
      (VG.Proof.CmacAes.Stream.X86_64.initSavedMem s S).readW (S + BitVec.ofNat 64 2184) 64 = s.gpr .rbp ∧
      (VG.Proof.CmacAes.Stream.X86_64.initSavedMem s S).readW (S + BitVec.ofNat 64 2192) 64 = s.gpr .r12 := by
  have sp (a b : Nat) (h : a + 8 ≤ b ∨ b + 8 ≤ a) (ha : a + 8 ≤ 2304) (hb : b + 8 ≤ 2304) :
      Mem.Sep (S + BitVec.ofNat 64 a) (64 / 8) (S + BitVec.ofNat 64 b) (64 / 8) :=
    Offset.sep S h (by omega) (by omega)
  refine ⟨?_, ?_, ?_⟩
  · rw [VG.Proof.CmacAes.Stream.X86_64.initSavedMem, Mem.readW_writeW_sep (sp 2176 2192 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sp 2176 2184 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self64]
  · rw [VG.Proof.CmacAes.Stream.X86_64.initSavedMem, Mem.readW_writeW_sep (sp 2184 2192 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self64]
  · rw [VG.Proof.CmacAes.Stream.X86_64.initSavedMem, Mem.readW_writeW_self64]

/-! ## Between the calls, and after them -/

theorem initMid_ok {s : State} {St S : Addr} {R : Nat} (hb : s.gpr .rbx = St) (hp : s.gpr .rbp = S)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 R) :
    ∃ s', runBlock isa initMid s = some s' ∧ s'.gpr .rdi = St ∧ s'.gpr .rsi = BitVec.ofNat 64 R ∧
      s'.gpr .rdx = St + BitVec.ofNat 64 240 ∧ s'.gpr .rcx = S ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [initMid, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
      Option.bind_some, Option.map_some]
    rfl, ?_⟩
  simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, and_self, gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags,
    rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, hb, hp, h12, VG.Proof.CmacAes.Stream.X86_64.sx240]
  refine ⟨trivial, trivial, trivial, trivial, fun r hr => ?_, trivial⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- The memory after zeroing the chaining value. -/
def zeroCv (m : Mem) (St : Addr) : Mem :=
  (m.writeW (St + BitVec.ofNat 64 272) (BitVec.setWidth 64 (0 : BitVec 32))).writeW
    (St + BitVec.ofNat 64 280) (BitVec.setWidth 64 (0 : BitVec 32))

theorem zeroCv_eq (m : Mem) (St : Addr) : VG.Proof.CmacAes.Stream.X86_64.zeroCv m St = VG.Proof.CmacAes.X86_64.zero2 m (St + BitVec.ofNat 64 272) := by
  rw [VG.Proof.CmacAes.Stream.X86_64.zeroCv, VG.Proof.CmacAes.X86_64.zero2, Offset.add_add]

theorem initPost_ok {s : State} {St S : Addr} (hb : s.gpr .rbx = St) (hp : s.gpr .rbp = S)
    (w₁ : InRegions s.wr (St + BitVec.ofNat 64 272) 8) (w₂ : InRegions s.wr (St + BitVec.ofNat 64 280) 8)
    (r₁ : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 2176) 8)
    (r₂ : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 2184) 8)
    (r₃ : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 2192) 8) :
    ∃ s', runBlock isa initPost s = some s' ∧
      s'.gpr .rbx = (VG.Proof.CmacAes.Stream.X86_64.zeroCv s.mem St).readW (S + BitVec.ofNat 64 2176) 64 ∧
      s'.gpr .rbp = (VG.Proof.CmacAes.Stream.X86_64.zeroCv s.mem St).readW (S + BitVec.ofNat 64 2184) 64 ∧
      s'.gpr .r12 = (VG.Proof.CmacAes.Stream.X86_64.zeroCv s.mem St).readW (S + BitVec.ofNat 64 2192) 64 ∧
      (∀ r, r ≠ .rbx → r ≠ .rbp → r ≠ .r12 → r ∈ calleeSaved → s'.gpr r = s.gpr r) ∧
      s'.mem = VG.Proof.CmacAes.Stream.X86_64.zeroCv s.mem St := by
  refine ⟨_, by
    simp (config := {decide := true}) only [initPost, sOff, runBlock_cons, runStep_some, runBlock_nil,
      at_, exec, readSrc, readSrc32, State.load64, State.store64, State.ea, State.setReg32, offset_nat,
      Option.map_some, gpr_setReg, mem_setReg, rd_setReg, wr_setReg, ite_true,
      ite_false, hb, hp, w₁, w₂, r₁, r₂, r₃, Nat.reduceAdd]
    rfl, ?_⟩
  simp (config := {decide := true}) only [gpr_setReg, mem_setReg, ite_true, ite_false]
  refine ⟨rfl, rfl, rfl, fun r h₁ h₂ h₃ hr => ?_, rfl⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all

/-! ## The whole function -/

/-- The regions the function writes: the state, the scratch buffer and the
stack its calls use. -/
abbrev IFrame (St S sp : Addr) : List Region := [⟨St, 304⟩, ⟨S, 2304⟩, below sp 16]

theorem IPre.rounds {s₀ : State} {St Kp S : Addr} {KL : Nat} (hp : VG.Proof.CmacAes.Stream.X86_64.IPre s₀ St Kp S KL) :
    KL / 4 + 6 = 10 ∨ KL / 4 + 6 = 12 ∨ KL / 4 + 6 = 14 := by
  rcases hp.klen with h | h | h <;> subst h <;> decide

/-- What the code before the first call leaves. -/
structure IMid₁ (s₀ : State) (St Kp S : Addr) (KL : Nat) (s : State) : Prop where
  args : VG.Proof.CmacAes.Stream.X86_64.EArgs s Kp St S KL
  rbx : s.gpr .rbx = St
  rbp : s.gpr .rbp = S
  r12 : s.gpr .r12 = BitVec.ofNat 64 (KL / 4 + 6)
  rsp : s.gpr .rsp = s₀.gpr .rsp
  other : ∀ r, r ≠ .rbx → r ≠ .rbp → r ≠ .r12 → r ∈ calleeSaved → s.gpr r = s₀.gpr r
  mem : s.mem = VG.Proof.CmacAes.Stream.X86_64.initSavedMem s₀ S
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem initPre_wp {s₀ : State} {St Kp S : Addr} {KL : Nat} (hp : VG.Proof.CmacAes.Stream.X86_64.IPre s₀ St Kp S KL) :
    WP isa (.block initPre) s₀ (VG.Proof.CmacAes.Stream.X86_64.IMid₁ s₀ St Kp S KL) := by
  obtain ⟨s₁, run₁, rdi₁, rsi₁, rdx₁, rcx₁, rbx₁, rbp₁, r12₁, rsp₁, o₁, m₁, rd₁, wr₁⟩ := VG.Proof.CmacAes.Stream.X86_64.initPre_ok hp
  refine WP.of_runBlock ⟨s₁, run₁, ⟨?_, rbx₁, rbp₁, r12₁, rsp₁, o₁, m₁, rd₁, wr₁⟩⟩
  exact
  { rdi := rdi₁, rsi := rsi₁, rdx := rdx₁, rcx := rcx₁, klen := hp.klen
    kw := hp.st_k.symm.sub_right (Region.sub_prefix (by decide))
    ks := hp.k_s.sub_right (Region.sub_prefix (by decide))
    ws := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    stkK := by rw [rsp₁]; exact hp.stk_k
    stkW := by rw [rsp₁]; exact hp.stk_st.sub_right (Region.sub_prefix (by decide))
    stkS := by rw [rsp₁]; exact hp.stk_s.sub_right (Region.sub_prefix (by decide))
    reads := by
      rw [rd₁, wr₁, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨⟨Kp, KL⟩, by simp, 0, by simp, by simp⟩
      · exact ⟨⟨St, 304⟩, by simp, 0, by simp, by simp⟩
      · exact ⟨⟨S, 2304⟩, by simp, 0, by simp, by simp⟩
    writes := by
      rw [wr₁, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨St, 304⟩, by simp, 0, by simp, by simp⟩
      · exact ⟨⟨S, 2304⟩, by simp, 0, by simp, by simp⟩ }

/-- What the code between the calls leaves. -/
structure IMid₂ (s₀ : State) (St S : Addr) (KL : Nat) (m : Mem) (s : State) : Prop where
  args : VG.Proof.CmacAes.Stream.X86_64.SArgs s St (St + BitVec.ofNat 64 240) S (KL / 4 + 6)
  rbx : s.gpr .rbx = St
  rbp : s.gpr .rbp = S
  rsp : s.gpr .rsp = s₀.gpr .rsp
  keep : ∀ r, r ≠ .rbx → r ≠ .rbp → r ≠ .r12 → r ∈ calleeSaved → s.gpr r = s₀.gpr r
  mem : s.mem = m
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem initMid_wp {s₀ s : State} {St Kp S : Addr} {KL : Nat} (hp : VG.Proof.CmacAes.Stream.X86_64.IPre s₀ St Kp S KL)
    (hb : s.gpr .rbx = St) (hbp : s.gpr .rbp = S) (h12 : s.gpr .r12 = BitVec.ofNat 64 (KL / 4 + 6))
    (hsp : s.gpr .rsp = s₀.gpr .rsp) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hk : ∀ r, r ≠ .rbx → r ≠ .rbp → r ≠ .r12 → r ∈ calleeSaved → s.gpr r = s₀.gpr r) :
    WP isa (.block initMid) s (VG.Proof.CmacAes.Stream.X86_64.IMid₂ s₀ St S KL s.mem) := by
  obtain ⟨s', run, rdi, rsi, rdx, rcx, sv, mem, rd, wr⟩ := VG.Proof.CmacAes.Stream.X86_64.initMid_ok hb hbp h12
  have hw := hp.wSt
  have rsp' : s'.gpr .rsp = s₀.gpr .rsp := by rw [sv _ (by simp [calleeSaved]), hsp]
  have kSt : Region.Sub ⟨St + BitVec.ofNat 64 240, 32⟩ ⟨St, 304⟩ := Offset.sub_base St (by decide)
  refine WP.of_runBlock ⟨s', run, ⟨?_, by rw [sv _ (by simp [calleeSaved]), hb],
    by rw [sv _ (by simp [calleeSaved]), hbp], rsp', fun r h₁ h₂ h₃ hr => by rw [sv r hr, hk r h₁ h₂ h₃ hr],
    mem, by rw [rd, hrd], by rw [wr, hwr]⟩⟩
  exact
  { rdi := rdi, rsi := rsi, rdx := rdx, rcx := rcx, rounds := hp.rounds
    wk := Offset.base_disjoint St (by decide) (by omega)
    ws := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    ks := (hp.st_s.sub_left kSt).sub_right (Region.sub_prefix (by decide))
    stkW := by rw [rsp']; exact hp.stk_st.sub_right (Region.sub_prefix (by decide))
    stkK := by rw [rsp']; exact hp.stk_st.sub_right kSt
    stkS := by rw [rsp']; exact hp.stk_s.sub_right (Region.sub_prefix (by decide))
    wrapK := by rw [VG.Proof.CmacAes.Stream.X86_64.toNat_add_lt St hw (by decide)]; omega
    wrapS := by have := hp.wS; omega
    reads := by
      rw [rd, wr, hrd, hwr, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨⟨St, 304⟩, by simp, 0, by simp, by simp⟩
      · exact ⟨⟨St, 304⟩, by simp, 240, rfl, by simp⟩
      · exact ⟨⟨S, 2304⟩, by simp, 0, by simp, by simp⟩
    writes := by
      rw [wr, hwr, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨St, 304⟩, by simp, 240, rfl, by simp⟩
      · exact ⟨⟨S, 2304⟩, by simp, 0, by simp, by simp⟩ }

theorem init_wp (v : Ctr32Impl) {s₀ : State} (h0 : initX86_64.pre s₀) :
    WP isa (init v.expand v.callee v.suffix) s₀ fun s' => gprPreserved s₀ s' ∧ initX86_64.post s₀ s' := by
  have hp := IPre.of h0
  generalize s₀.gpr .rdi = St at hp
  generalize s₀.gpr .rsi = Kp at hp
  generalize s₀.gpr .rcx = S at hp
  generalize (s₀.gpr .rdx).toNat = KL at hp
  have hw := hp.wSt
  have hsw := hp.wS
  have hR := hp.rounds
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.X86_64.initPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.X86_64.ek_call v h₁.args) fun s₂ h₂ => ?_)
  have g₂ (r : Reg) (hr : r ∈ calleeSaved) : s₂.gpr r = s₁.gpr r := h₂.saved r hr
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.X86_64.initMid_wp hp (by rw [g₂ _ (by simp [calleeSaved]), h₁.rbx])
    (by rw [g₂ _ (by simp [calleeSaved]), h₁.rbp]) (by rw [g₂ _ (by simp [calleeSaved]), h₁.r12])
    (by rw [g₂ _ (by simp [calleeSaved]), h₁.rsp]) (by rw [h₂.rd, h₁.rd]) (by rw [h₂.wr, h₁.wr])
    (fun r a b c hr => by rw [g₂ r hr, h₁.other r a b c hr])) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.X86_64.sub_call v _ h₃.args) fun s₄ h₄ => ?_)
  have g₄ (r : Reg) (hr : r ∈ calleeSaved) : s₄.gpr r = s₃.gpr r := h₄.saved r hr
  have inS (d : Nat) (hd : d + 8 ≤ 2304) : InRegions s₄.wr (S + BitVec.ofNat 64 d) 8 := by
    rw [h₄.wr, h₃.wr, hp.wr]; exact ⟨⟨S, 2304⟩, by simp, Offset.contains_base _ hd (by omega)⟩
  have inSt (d : Nat) (hd : d + 8 ≤ 304) : InRegions s₄.wr (St + BitVec.ofNat 64 d) 8 := by
    rw [h₄.wr, h₃.wr, hp.wr]; exact ⟨⟨St, 304⟩, by simp, Offset.contains_base _ hd (by omega)⟩
  have inR (d : Nat) (hd : d + 8 ≤ 2304) : InRegions (s₄.rd ++ s₄.wr) (S + BitVec.ofNat 64 d) 8 := by
    obtain ⟨r, hr, hc⟩ := inS d hd; exact ⟨r, List.mem_append_right _ hr, hc⟩
  obtain ⟨s₅, run₅, rbx₅, rbp₅, r12₅, keep₅, m₅⟩ := VG.Proof.CmacAes.Stream.X86_64.initPost_ok (s := s₄) (St := St) (S := S)
    (by rw [g₄ _ (by simp [calleeSaved]), h₃.rbx]) (by rw [g₄ _ (by simp [calleeSaved]), h₃.rbp])
    (inSt 272 (by decide)) (inSt 280 (by decide)) (inR 2176 (by decide)) (inR 2184 (by decide))
    (inR 2192 (by decide))
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  -- The memory, step by step.
  have rsp₀ := hp.sp
  have fz : Frame [⟨St + BitVec.ofNat 64 272, 16⟩] s₄.mem (VG.Proof.CmacAes.Stream.X86_64.zeroCv s₄.mem St) := by
    rw [VG.Proof.CmacAes.Stream.X86_64.zeroCv_eq]; exact Proof.CmacAes.X86_64.frame_store2 _ _ _
  have f₁ : Frame [⟨S + BitVec.ofNat 64 2176, 24⟩] s₀.mem s₁.mem := by
    rw [h₁.mem]; exact VG.Proof.CmacAes.Stream.X86_64.initSavedMem_frame _ _
  have f₂ : Frame [⟨St, 240⟩, ⟨S, 512⟩, below (s₀.gpr .rsp) 16] s₁.mem s₂.mem := by
    rw [← h₁.rsp]; exact h₂.frame
  have f₄ : Frame [⟨St + BitVec.ofNat 64 240, 32⟩, ⟨S, 2176⟩, below (s₀.gpr .rsp) 16] s₃.mem s₄.mem := by
    rw [← h₃.rsp]; exact h₄.frame
  have m₃ : s₃.mem = s₂.mem := h₃.mem
  -- The saved registers.
  have dSv (r : Region) (hr : r ∈ [⟨St, 240⟩, ⟨S, 512⟩, below (s₀.gpr .rsp) 16, ⟨St + BitVec.ofNat 64 240, 32⟩,
      ⟨S, 2176⟩, ⟨St + BitVec.ofNat 64 272, 16⟩]) (d : Nat) (hd : 2176 ≤ d) (hd' : d + 8 ≤ 2304) :
      (⟨S + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
    have sub : Region.Sub ⟨S + BitVec.ofNat 64 d, 8⟩ ⟨S, 2304⟩ := Offset.sub_base S hd'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).symm.sub_left sub
    · exact Offset.disjoint_base S (by omega) (by omega)
    · exact hp.stk_s.symm.sub_left sub
    · exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).symm.sub_left sub
    · exact Offset.disjoint_base S (by omega) (by omega)
    · exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).symm.sub_left sub
  have rd' (d : Nat) (hd : 2176 ≤ d) (hd' : d + 8 ≤ 2304) :
      (VG.Proof.CmacAes.Stream.X86_64.zeroCv s₄.mem St).readW (S + BitVec.ofNat 64 d) 64 = s₁.mem.readW (S + BitVec.ofNat 64 d) 64 := by
    have c := Region.contains_self (S + BitVec.ofNat 64 d) 8
    rw [fz.readW c (fun r hr => dSv r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; simp [hr]) d hd hd') (by decide),
      f₄.readW c (fun r hr => dSv r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl | rfl <;> simp) d hd hd') (by decide), m₃,
      f₂.readW c (fun r hr => dSv r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl | rfl <;> simp) d hd hd') (by decide)]
  obtain ⟨sv₁, sv₂, sv₃⟩ := VG.Proof.CmacAes.Stream.X86_64.initSaved_read s₀ S
  have m₁ := h₁.mem
  -- The state, outside what the last block writes.
  have dSt (d n : Nat) (hd : d + n ≤ 272) (r : Region) (hr : r ∈ [⟨St + BitVec.ofNat 64 272, 16⟩]) :
      (⟨St + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r := by
    simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint St (by omega) (by omega) (by omega)
  have hRb : 16 * (Spec.Aes.rounds (KL / 4) + 1) ≤ 240 := by simp only [Spec.Aes.rounds]; omega
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [rbx₅, rd' 2176 (by decide) (by decide), m₁]; exact sv₁
    · rw [rbp₅, rd' 2184 (by decide) (by decide), m₁]; exact sv₂
    · rw [keep₅ _ (by decide) (by decide) (by decide) (by simp [calleeSaved]),
        g₄ _ (by simp [calleeSaved]), h₃.rsp]
    · rw [r12₅, rd' 2192 (by decide) (by decide), m₁]; exact sv₃
    all_goals rw [keep₅ _ (by decide) (by decide) (by decide) (by simp [calleeSaved]),
      g₄ _ (by simp [calleeSaved]), h₃.keep _ (by decide) (by decide) (by decide) (by simp [calleeSaved])]
  · have c := Region.contains_self (s₀.gpr .rsp) 8
    have stS : Region.Sub ⟨S, 2176⟩ ⟨S, 2304⟩ := Region.sub_prefix (by decide)
    rw [m₅, fz.readW c (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.ret_st.sub_right (Offset.sub_base St (by decide))) (by decide),
      f₄.readW c (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hp.ret_st.sub_right (Offset.sub_base St (by decide))
        · exact hp.ret_s.sub_right stS
        · exact Offset.base_disjoint_below _ (by decide)) (by decide), m₃,
      f₂.readW c (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hp.ret_st.sub_right (Region.sub_prefix (by decide))
        · exact hp.ret_s.sub_right (Region.sub_prefix (by decide))
        · exact Offset.base_disjoint_below _ (by decide)) (by decide),
      f₁.readW c (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.ret_s.sub_right (Offset.sub_base S (by decide))) (by decide)]
  · show Spec.Cmac.Repr s₅.mem (s₀.gpr .rdi) (Spec.Aes.bytesAt s₀.mem (s₀.gpr .rsi) (s₀.gpr .rdx).toNat) []
    rw [hp.rdi, hp.rsi, hp.rdx, Proof.Cmac.Stream.repr_iff]
    have hkey : Spec.Aes.bytesAt s₁.mem Kp KL = Spec.Aes.bytesAt s₀.mem Kp KL :=
      VG.Proof.CmacAes.X86_64.bytesAt_frame f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.k_s.sub_right (Offset.sub_base S (by decide))) (by have := hp.wK; omega)
    have hlen : (Spec.Aes.bytesAt s₀.mem Kp KL).length = KL := Proof.Cmac.bytesAt_length _ _ _
    -- The schedule, from the first call on.
    have sch : ∀ {d n : Nat}, d + n ≤ 240 → Spec.Aes.bytesAt s₅.mem (St + BitVec.ofNat 64 d) n =
        Spec.Aes.bytesAt s₂.mem (St + BitVec.ofNat 64 d) n := fun {d n} hd => by
      rw [m₅, VG.Proof.CmacAes.X86_64.bytesAt_frame fz (dSt d n (by omega)) (by omega), VG.Proof.CmacAes.X86_64.bytesAt_frame f₄ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact Offset.disjoint St (by omega) (by omega) (by omega)
        · exact (hp.st_s.sub_left (Offset.sub_base St (by omega))).sub_right (Region.sub_prefix (by decide))
        · exact (hp.stk_st.sub_right (Offset.sub_base St (by omega))).symm) (by omega), m₃]
    have hsch : Spec.Aes.bytesAt s₂.mem St (16 * (Spec.Aes.rounds (KL / 4) + 1)) =
        Spec.Aes.expandKey (Spec.Aes.bytesAt s₀.mem Kp KL) := by rw [h₂.out, hkey]
    refine ⟨⟨by rw [hlen]; exact hp.klen, ?_, ?_⟩, ?_, by simp [Proof.Cmac.Stream.held_zero, Spec.Aes.bytesAt]⟩
    · rw [hlen]
      have := sch (d := 0) (n := 16 * (Spec.Aes.rounds (KL / 4) + 1)) (by omega)
      rw [k0] at this; rw [this, hsch]
    · have e : Spec.Aes.bytesAt s₅.mem (St + 240) 32 = Spec.Aes.bytesAt s₄.mem (St + 240) 32 := by
        rw [m₅]; exact VG.Proof.CmacAes.X86_64.bytesAt_frame fz (dSt 240 32 (by decide)) (by decide)
      rw [e]
      refine h₄.out.trans ?_
      rw [m₃, show KL / 4 + 6 = Spec.Aes.rounds (KL / 4) from rfl, hsch]
      simp only [Spec.Cmac.aes, hlen]
    · rw [m₅, VG.Proof.CmacAes.Stream.X86_64.zeroCv_eq]; exact (VG.Proof.CmacAes.X86_64.zero2_bytes _ _).trans rfl

/-! ## Constant time -/

/-- What the call of `vg_aes_expand_key_scratch` leaves, for `initMid`. -/
structure IAfter (s₀ : State) (St S : Addr) (KL : Nat) (s : State) : Prop where
  rbx : s.gpr .rbx = St
  rbp : s.gpr .rbp = S
  r12 : s.gpr .r12 = BitVec.ofNat 64 (KL / 4 + 6)
  rsp : s.gpr .rsp = s₀.gpr .rsp
  keep : ∀ r, r ≠ .rbx → r ≠ .rbp → r ≠ .r12 → r ∈ calleeSaved → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem ek_after (v : Ctr32Impl) {s₀ s : State} {St Kp S : Addr} {KL : Nat} (h : VG.Proof.CmacAes.Stream.X86_64.IMid₁ s₀ St Kp S KL s) :
    WP isa (.call v.expand.name v.expand.code) s (VG.Proof.CmacAes.Stream.X86_64.IAfter s₀ St S KL) :=
  WP.mono (VG.Proof.CmacAes.Stream.X86_64.ek_call v h.args) fun _ h₂ =>
    ⟨by rw [h₂.saved _ (by simp [calleeSaved]), h.rbx], by rw [h₂.saved _ (by simp [calleeSaved]), h.rbp],
      by rw [h₂.saved _ (by simp [calleeSaved]), h.r12], by rw [h₂.saved _ (by simp [calleeSaved]), h.rsp],
      fun r a b c hr => by rw [h₂.saved r hr, h.other r a b c hr], by rw [h₂.rd, h.rd], by rw [h₂.wr, h.wr]⟩

theorem init_rel (v : Ctr32Impl) {s₀ s₀' : State} (h0 : initX86_64.pre s₀) (h0' : initX86_64.pre s₀')
    (hq : initX86_64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (init v.expand v.callee v.suffix) fun _ _ => True := by
  obtain ⟨q1, q2, q3, q4, q5⟩ := hq
  have hp := IPre.of h0
  have hp' : VG.Proof.CmacAes.Stream.X86_64.IPre s₀' (s₀.gpr .rdi) (s₀.gpr .rsi) (s₀.gpr .rcx) (s₀.gpr .rdx).toNat := by
    rw [q2, q3, q4, q5]; exact IPre.of h0'
  generalize s₀.gpr .rdi = St at hp hp'
  generalize s₀.gpr .rsi = Kp at hp hp'
  generalize s₀.gpr .rcx = S at hp hp'
  generalize (s₀.gpr .rdx).toNat = KL at hp hp'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .rsp]) (.block initPre) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .rsp]) (.block initMid) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ h, (taint.check (Taint.ofRegs [.rbx, .rbp]) (.block initPost) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption) hA).wp
    (F₁ := VG.Proof.CmacAes.Stream.X86_64.IMid₁ s₀ St Kp S KL) (F₂ := VG.Proof.CmacAes.Stream.X86_64.IMid₁ s₀' St Kp S KL) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨VG.Proof.CmacAes.Stream.X86_64.initPre_wp hp, VG.Proof.CmacAes.Stream.X86_64.initPre_wp hp'⟩
  have e := (VG.Proof.CmacAes.Stream.X86_64.ek_rel v (P := fun a b => VG.Proof.CmacAes.Stream.X86_64.IMid₁ s₀ St Kp S KL a ∧ VG.Proof.CmacAes.Stream.X86_64.IMid₁ s₀' St Kp S KL b)
    fun a b h => ⟨_, _, _, _, h.1.args, h.2.args, by rw [h.1.rsp, h.2.rsp, q1]⟩).wp
    (F₁ := VG.Proof.CmacAes.Stream.X86_64.IAfter s₀ St S KL) (F₂ := VG.Proof.CmacAes.Stream.X86_64.IAfter s₀' St S KL) fun a b h => ⟨VG.Proof.CmacAes.Stream.X86_64.ek_after v h.1, VG.Proof.CmacAes.Stream.X86_64.ek_after v h.2⟩
  have m := (RelCT.taint (A := taint) (P := fun a b => VG.Proof.CmacAes.Stream.X86_64.IAfter s₀ St S KL a ∧ VG.Proof.CmacAes.Stream.X86_64.IAfter s₀' St S KL b) _
    (fun a b h => by
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h.1.rbx, h.2.rbx]
      · rw [h.1.rbp, h.2.rbp]
      · rw [h.1.r12, h.2.r12]
      · rw [h.1.rsp, h.2.rsp, q1]) hB).wp
    (F₁ := fun (s : State) => ∃ m, VG.Proof.CmacAes.Stream.X86_64.IMid₂ s₀ St S KL m s) (F₂ := fun (s : State) => ∃ m, VG.Proof.CmacAes.Stream.X86_64.IMid₂ s₀' St S KL m s)
    fun a b h => ⟨WP.mono (VG.Proof.CmacAes.Stream.X86_64.initMid_wp hp h.1.rbx h.1.rbp h.1.r12 h.1.rsp h.1.rd h.1.wr h.1.keep)
        fun _ h => ⟨_, h⟩,
      WP.mono (VG.Proof.CmacAes.Stream.X86_64.initMid_wp hp' h.2.rbx h.2.rbp h.2.r12 h.2.rsp h.2.rd h.2.wr h.2.keep) fun _ h => ⟨_, h⟩⟩
  have sk := (VG.Proof.CmacAes.Stream.X86_64.sub_rel v ("vg_cmac_aes_subkeys" ++ v.suffix)
    (P := fun a b => (∃ m, VG.Proof.CmacAes.Stream.X86_64.IMid₂ s₀ St S KL m a) ∧ ∃ m, VG.Proof.CmacAes.Stream.X86_64.IMid₂ s₀' St S KL m b)
    fun a b ⟨⟨_, h₁⟩, ⟨_, h₂⟩⟩ => ⟨_, _, _, _, h₁.args, h₂.args, by rw [h₁.rsp, h₂.rsp, q1]⟩).wp
    (F₁ := fun (s : State) => s.gpr .rbx = St ∧ s.gpr .rbp = S)
    (F₂ := fun (s : State) => s.gpr .rbx = St ∧ s.gpr .rbp = S)
    fun a b ⟨⟨_, h₁⟩, ⟨_, h₂⟩⟩ =>
      ⟨WP.mono (VG.Proof.CmacAes.Stream.X86_64.sub_call v _ h₁.args) fun _ h => ⟨by rw [h.saved _ (by simp [calleeSaved]), h₁.rbx],
          by rw [h.saved _ (by simp [calleeSaved]), h₁.rbp]⟩,
        WP.mono (VG.Proof.CmacAes.Stream.X86_64.sub_call v _ h₂.args) fun _ h => ⟨by rw [h.saved _ (by simp [calleeSaved]), h₂.rbx],
          by rw [h.saved _ (by simp [calleeSaved]), h₂.rbp]⟩⟩
  have p := RelCT.taint (A := taint)
    (P := fun a b => (a.gpr .rbx = St ∧ a.gpr .rbp = S) ∧ b.gpr .rbx = St ∧ b.gpr .rbp = S) _
    (fun a b h => by
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.1, h.2.1]
      · rw [h.1.2, h.2.2]) hC
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((e.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((m.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((sk.mono (fun _ _ h => h) fun _ _ h => h.2).seq p)))

theorem init_ct (v : Ctr32Impl) :
    ConstantTime isa initX86_64.pre initX86_64.pub (init v.expand v.callee v.suffix) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (VG.Proof.CmacAes.Stream.X86_64.init_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.Stream.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Verified`. -/
section

section

/-!
# Streaming AES-CMAC on x86-64: `vg_cmac_aes_finish`

The code copies the chaining value to `out`, computes the number of bytes held
back, and calls `vg_cmac_aes_finalize` with the state as its key and `out` as
its state: its result is the MAC of the message the state represents
(`repr_finish`). The code before the call is constant time by the taint
analysis, and the call by its own proof (`fin_rel`), its arguments pinned by
`HMid`.
-/

namespace VG.Proof.CmacAes.Stream.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.CmacAes.Stream.X86_64
open VG.Impl.CmacAes.X86_64 (at_)
open VG.Proof.CmacAes.X86_64 (offset_nat bytesAt_frame k0)
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.Cmac.Stream (held held_le)

/-- The precondition, by name: the state `St`, `out` (`O`), the scratch
buffer `S` and the rounds `R`. -/
structure HPre (s₀ : State) (St O S : Addr) (R : Nat) : Prop where
  rdi : s₀.gpr .rdi = St
  rcx : s₀.gpr .rcx = O
  r8 : s₀.gpr .r8 = S
  rsi : (s₀.gpr .rsi).toNat = R
  sp : 16 ≤ (s₀.gpr .rsp).toNat
  rd : s₀.rd = []
  wr : s₀.wr = [⟨St, 304⟩, ⟨O, 16⟩, ⟨S, 2304⟩]
  st_o : (⟨St, 304⟩ : Region).Disjoint ⟨O, 16⟩
  st_s : (⟨St, 304⟩ : Region).Disjoint ⟨S, 2304⟩
  o_s : (⟨O, 16⟩ : Region).Disjoint ⟨S, 2304⟩
  ret_st : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨St, 304⟩
  ret_o : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨O, 16⟩
  ret_s : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨S, 2304⟩
  stk_st : (below (s₀.gpr .rsp) 16).Disjoint ⟨St, 304⟩
  stk_o : (below (s₀.gpr .rsp) 16).Disjoint ⟨O, 16⟩
  stk_s : (below (s₀.gpr .rsp) 16).Disjoint ⟨S, 2304⟩
  wSt : St.toNat + 304 ≤ 2 ^ 64
  wO : O.toNat + 16 ≤ 2 ^ 64
  wS : S.toNat + 2304 ≤ 2 ^ 64
  rounds : R = 10 ∨ R = 12 ∨ R = 14

theorem HPre.of {s₀ : State} (h : finishX86_64.pre s₀) :
    VG.Proof.CmacAes.Stream.X86_64.HPre s₀ (s₀.gpr .rdi) (s₀.gpr .rcx) (s₀.gpr .r8) (s₀.gpr .rsi).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p⟩ := h
  ⟨rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p⟩

/-! ## Before the call -/

theorem finishPre_ok {s₀ : State} {St O S : Addr} {R : Nat} (hp : VG.Proof.CmacAes.Stream.X86_64.HPre s₀ St O S R) :
    ∃ s₁, runBlock isa finishPre s₀ = some s₁ ∧ s₁.gpr .rdi = St ∧ s₁.gpr .rsi = s₀.gpr .rsi ∧
      s₁.gpr .rdx = O ∧ s₁.gpr .rcx = St + BitVec.ofNat 64 288 ∧ s₁.gpr .r8 = s₀.gpr .rdx ∧
      s₁.gpr .r9 = S ∧ (∀ r ∈ calleeSaved, s₁.gpr r = s₀.gpr r) ∧
      s₁.zf = some (s₀.gpr .rdx == 0) ∧
      s₁.mem = VG.Proof.CmacAes.Stream.X86_64.copyMem s₀.mem O (St + BitVec.ofNat 64 272) ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr := by
  have hw := hp.wSt
  have inSt (d : Nat) (hd : d + 8 ≤ 304) : InRegions (s₀.rd ++ s₀.wr) (St + BitVec.ofNat 64 d) 8 := by
    rw [hp.rd, hp.wr]; exact ⟨⟨St, 304⟩, by simp, Offset.contains_base _ hd (by omega)⟩
  have inO (d : Nat) (hd : d + 8 ≤ 16) : InRegions s₀.wr (O + BitVec.ofNat 64 d) 8 := by
    rw [hp.wr]; exact ⟨⟨O, 16⟩, by simp, Offset.contains_base _ hd (by have := hp.wO; omega)⟩
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, BitVec.reduceSignExtend, finishPre, runBlock_cons, runStep_some, runBlock_nil, at_,
      exec, readSrc, execAlu, State.load64, State.store64, State.ea, offset_nat, Option.bind_some,
      Option.map_some, gpr_setReg, gpr_arithFlags, mem_setReg, rd_setReg, wr_setReg,
      hp.rdi, hp.rcx, inSt 272 (by decide), inSt 280 (by decide), inO 0 (by decide), inO 8 (by decide)]
    rfl, ?_⟩
  simp only [reduceCtorEq, ↓reduceIte, and_self, gpr_setReg, gpr_arithFlags, zf_arithFlags, mem_setReg,
    mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags,
    BitVec.and_self, hp.rdi, hp.r8]
  refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, fun r hr => ?_, trivial, ?_, trivial⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · simp only [VG.Proof.CmacAes.Stream.X86_64.copyMem, k0, Offset.add_add]

/-- What the code before the call leaves. -/
structure HMid (s₀ : State) (St O S : Addr) (R : Nat) (s : State) : Prop where
  args : VG.Proof.CmacAes.Stream.X86_64.FArgs s St O (St + BitVec.ofNat 64 288) S (held (s₀.gpr .rdx).toNat) R
  mem : s.mem = VG.Proof.CmacAes.Stream.X86_64.copyMem s₀.mem O (St + BitVec.ofNat 64 272)
  saved : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r

theorem HPre.fargs {s₀ s : State} {St O S : Addr} {R L : Nat} (hp : VG.Proof.CmacAes.Stream.X86_64.HPre s₀ St O S R) (hL : L ≤ 16)
    (rdi : s.gpr .rdi = St) (rsi : s.gpr .rsi = s₀.gpr .rsi) (rdx : s.gpr .rdx = O)
    (rcx : s.gpr .rcx = St + BitVec.ofNat 64 288) (r8 : s.gpr .r8 = BitVec.ofNat 64 L)
    (r9 : s.gpr .r9 = S) (rsp : s.gpr .rsp = s₀.gpr .rsp) (rd : s.rd = s₀.rd) (wr : s.wr = s₀.wr) :
    VG.Proof.CmacAes.Stream.X86_64.FArgs s St O (St + BitVec.ofNat 64 288) S L R := by
  have hw := hp.wSt
  have pSt : Region.Sub ⟨St + BitVec.ofNat 64 288, L⟩ ⟨St, 304⟩ := Offset.sub_base St (by omega)
  exact
  { rdi := rdi, rdx := rdx, rcx := rcx, r8 := r8, r9 := r9
    rsi := by rw [rsi]; exact VG.Proof.CmacAes.Stream.X86_64.rsi_ofNat hp.rsi hp.rounds
    rounds := hp.rounds, len := hL
    kst := hp.st_o.sub_left (Region.sub_prefix (by decide))
    ks := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    pst := hp.st_o.sub_left pSt
    ps := (hp.st_s.sub_left pSt).sub_right (Region.sub_prefix (by decide))
    sts := hp.o_s.sub_right (Region.sub_prefix (by decide))
    stkK := by rw [rsp]; exact hp.stk_st.sub_right (Region.sub_prefix (by decide))
    stkP := by rw [rsp]; exact hp.stk_st.sub_right pSt
    stkSt := by rw [rsp]; exact hp.stk_o
    stkS := by rw [rsp]; exact hp.stk_s.sub_right (Region.sub_prefix (by decide))
    wrapK := by omega
    wrapSt := hp.wO
    wrapP := by rw [VG.Proof.CmacAes.Stream.X86_64.toNat_add_lt St hw (by decide)]; omega
    wrapS := by have := hp.wS; omega
    reads := by
      rw [rd, wr, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨St, 304⟩, by simp, 0, by simp, by simp⟩
      · exact ⟨⟨St, 304⟩, by simp, 288, rfl, by simp; omega⟩
      · exact ⟨⟨O, 16⟩, by simp, 0, by simp, by simp⟩
      · exact ⟨⟨S, 2304⟩, by simp, 0, by simp, by simp⟩
    writes := by
      rw [wr, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨O, 16⟩, by simp, 0, by simp, by simp⟩
      · exact ⟨⟨S, 2304⟩, by simp, 0, by simp, by simp⟩ }

theorem finPre_wp {s₀ : State} {St O S : Addr} {R : Nat} (hp : VG.Proof.CmacAes.Stream.X86_64.HPre s₀ St O S R) :
    WP isa finPre s₀ (VG.Proof.CmacAes.Stream.X86_64.HMid s₀ St O S R) := by
  obtain ⟨s₁, run₁, rdi₁, rsi₁, rdx₁, rcx₁, r8₁, r9₁, sv₁, zf₁, m₁, rd₁, wr₁⟩ := VG.Proof.CmacAes.Stream.X86_64.finishPre_ok hp
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := sv₁ _ (by simp [calleeSaved])
  by_cases h0 : (s₀.gpr .rdx).toNat = 0
  · refine WP.ite true (by show s₁.zf = _; rw [zf₁, VG.Proof.CmacAes.Stream.X86_64.beq_zero_iff, h0]; rfl)
      (fun _ => WP.block_nil ?_) (fun h => by cases h)
    refine ⟨hp.fargs (held_le _) rdi₁ rsi₁ rdx₁ rcx₁ ?_ r9₁ rsp₁ rd₁ wr₁, m₁, sv₁⟩
    rw [h0, r8₁]; exact BitVec.eq_of_toNat_eq (by rw [h0]; rfl)
  · refine WP.ite false (by show s₁.zf = _; rw [zf₁, VG.Proof.CmacAes.Stream.X86_64.beq_zero_iff]; simp [h0])
      (fun h => by cases h) fun _ => ?_
    refine WP.of_runBlock ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some]
      rfl, ?_⟩
    simp only [gpr_setReg, gpr_arithFlags, ite_true, r8₁, VG.Proof.CmacAes.Stream.X86_64.sx1, VG.Proof.CmacAes.Stream.X86_64.sx15]
    have hne : s₀.gpr .rdx ≠ 0 := fun e => h0 (by rw [e]; rfl)
    have hc : ∀ r ∈ calleeSaved, r ≠ .r8 := by decide
    refine ⟨hp.fargs (held_le _) rdi₁ rsi₁ rdx₁ rcx₁ (VG.Proof.CmacAes.Stream.X86_64.held_bv _ hne) r9₁ rsp₁ rd₁ wr₁, m₁,
      fun r hr => by simp only [gpr_setReg, gpr_arithFlags, hc r hr, ite_false]; exact sv₁ r hr⟩

/-! ## The whole function -/

theorem finish_wp (v : Ctr32Impl) {s₀ : State} (h0 : finishX86_64.pre s₀) :
    WP isa (finish v.callee v.suffix) s₀ fun s' => gprPreserved s₀ s' ∧ finishX86_64.post s₀ s' := by
  have hp := HPre.of h0
  generalize s₀.gpr .rdi = St at hp
  generalize s₀.gpr .rcx = O at hp
  generalize s₀.gpr .r8 = S at hp
  generalize (s₀.gpr .rsi).toNat = R at hp
  have hw := hp.wSt
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.X86_64.finPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.mono (VG.Proof.CmacAes.Stream.X86_64.fin_call v _ h₁.args) fun s₂ h₂ => ?_
  have rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := h₁.saved _ (by simp [calleeSaved])
  -- The state is unchanged before the call.
  have fSt : ∀ {d n : Nat}, d + n ≤ 304 → Spec.Aes.bytesAt s₁.mem (St + BitVec.ofNat 64 d) n =
      Spec.Aes.bytesAt s₀.mem (St + BitVec.ofNat 64 d) n := fun {d n} hd => by
    rw [h₁.mem]
    exact VG.Proof.CmacAes.X86_64.bytesAt_frame (VG.Proof.CmacAes.Stream.X86_64.copyMem_frame _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_o.sub_left (Offset.sub_base St hd)) (by omega)
  refine ⟨⟨fun r hr => by rw [h₂.saved r hr, h₁.saved r hr], ?_⟩, ?_⟩
  · have big : Frame [⟨O, 16⟩, ⟨S, 2176⟩, below (s₀.gpr .rsp) 16] s₀.mem s₂.mem := by
      refine ((h₁.mem ▸ VG.Proof.CmacAes.Stream.X86_64.copyMem_frame _ _ _ : Frame [⟨O, 16⟩] s₀.mem s₁.mem).mono (by simp)).trans ?_
      rw [← rsp₁]; exact h₂.frame
    refine big.readW (r := ⟨s₀.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.ret_o
    · exact hp.ret_s.sub_right (Region.sub_prefix (by decide))
    · exact Offset.base_disjoint_below _ (by decide)
  · intro key msg hr hR hc hlen
    rw [hp.rdi] at hr
    -- `St + 240` and the others, as offsets.
    rw [Proof.Cmac.Stream.repr_iff] at hr
    obtain ⟨⟨hkl, hks, hsk⟩, hcv, hhb⟩ := hr
    have hn : (s₀.gpr .rdx).toNat = msg.length := by rw [hc, VG.Proof.CmacAes.Stream.X86_64.toNat_ofNat hlen]
    rw [hp.rcx]
    have hR' : R = Spec.Aes.rounds (key.length / 4) := by rw [← hp.rsi]; exact hR
    have hsch : Spec.Aes.bytesAt s₁.mem St (16 * (R + 1)) = Spec.Aes.expandKey key := by
      have := fSt (d := 0) (n := 16 * (R + 1)) (by rcases hp.rounds with h | h | h <;> omega)
      rw [k0] at this; rw [this, hR']; exact hks
    have hciph : Spec.Cmac.aesWith R (Spec.Aes.bytesAt s₁.mem St (16 * (R + 1))) = Spec.Cmac.aes key := by
      rw [hsch, hR']; rfl
    have e₁ : Spec.Aes.bytesAt s₁.mem (St + 240) 32 = Spec.Aes.bytesAt s₀.mem (St + 240) 32 :=
      fSt (d := 240) (by decide)
    have e₂ : Spec.Aes.bytesAt s₁.mem O 16 = Spec.Aes.bytesAt s₀.mem (St + 272) 16 := by
      rw [h₁.mem]; exact VG.Proof.CmacAes.Stream.X86_64.copyMem_bytes _ (hp.st_o.symm.sub_right (Offset.sub_base St (by decide)))
    have e₃ : Spec.Aes.bytesAt s₁.mem (St + BitVec.ofNat 64 288) (held (s₀.gpr .rdx).toNat) =
        Spec.Aes.bytesAt s₀.mem (St + 288) (held msg.length) := by
      rw [hn]; exact fSt (by have := held_le msg.length; omega)
    obtain ⟨hm, hne, hst, happ⟩ := Proof.Cmac.Stream.repr_finish
      ((Proof.Cmac.Stream.repr_iff _ _ _ _).mpr ⟨⟨hkl, hks, hsk⟩, hcv, hhb⟩)
    have out := h₂.out (by rw [hciph, e₁]; exact hsk) _ hm (by rw [hn]; exact hne)
      (by rw [hciph, e₂]; exact hst)
    rw [out, hciph, e₃, happ, Proof.Cmac.Stream.aesCmac_eq]

/-! ## Constant time -/

theorem finish_rel (v : Ctr32Impl) {s₀ s₀' : State} (h0 : finishX86_64.pre s₀)
    (h0' : finishX86_64.pre s₀') (hq : finishX86_64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (finish v.callee v.suffix) fun _ _ => True := by
  obtain ⟨q1, q2, q3, q4, q5, q6⟩ := hq
  have hp := HPre.of h0
  have hp' : VG.Proof.CmacAes.Stream.X86_64.HPre s₀' (s₀.gpr .rdi) (s₀.gpr .rcx) (s₀.gpr .r8) (s₀.gpr .rsi).toNat := by
    rw [q2, q3, q5, q6]; exact HPre.of h0'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .rsp]) finPre h).isSome =
      true := ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption) hA).wp
    (F₁ := VG.Proof.CmacAes.Stream.X86_64.HMid s₀ _ _ _ _) (F₂ := VG.Proof.CmacAes.Stream.X86_64.HMid s₀' _ _ _ _) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨VG.Proof.CmacAes.Stream.X86_64.finPre_wp hp, VG.Proof.CmacAes.Stream.X86_64.finPre_wp hp'⟩
  have c := VG.Proof.CmacAes.Stream.X86_64.fin_rel v ("vg_cmac_aes_finalize" ++ v.suffix) (P := fun s₁ s₂ =>
      VG.Proof.CmacAes.Stream.X86_64.HMid s₀ (s₀.gpr .rdi) (s₀.gpr .rcx) (s₀.gpr .r8) (s₀.gpr .rsi).toNat s₁ ∧
      VG.Proof.CmacAes.Stream.X86_64.HMid s₀' (s₀.gpr .rdi) (s₀.gpr .rcx) (s₀.gpr .r8) (s₀.gpr .rsi).toNat s₂)
    fun s₁ s₂ h => ⟨_, _, _, _, _, _, h.1.args, by rw [q4]; exact h.2.args, by
      rw [h.1.saved _ (by simp [calleeSaved]), h.2.saved _ (by simp [calleeSaved]), q1]⟩
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq c

theorem finish_ct (v : Ctr32Impl) :
    ConstantTime isa finishX86_64.pre finishX86_64.pub (finish v.callee v.suffix) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (VG.Proof.CmacAes.Stream.X86_64.finish_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.Stream.X86_64

end

section

/-!
# Streaming AES-CMAC on x86-64: `vg_cmac_aes_absorb` is constant time

Two runs from states that agree on the public arguments are related piece by
piece (`RelCT`): the taint analysis covers the code between the calls, from
the registers the correctness proof pins to values of the public arguments
(`AMid₁`, `AAfter₁`, `AMid₂`, `AAfter₂`), and each call of
`vg_cmac_aes_update` is constant time by its own proof (`upd_rel`).
-/

namespace VG.Proof.CmacAes.Stream.X86_64

open VG VG.X86_64 VG.Impl.CmacAes.Stream.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- What the first call leaves, for `chain2`. -/
structure AAfter₁ (s₀ : State) (St D S : Addr) (L : Nat) (s : State) : Prop where
  rbx : s.gpr .rbx = St
  rbp : s.gpr .rbp = s₀.gpr .rsi
  r13 : s.gpr .r13 = D + BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.X86_64.fOf (s₀.gpr .rdx).toNat L)
  r14 : s.gpr .r14 = BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.X86_64.leftOf (s₀.gpr .rdx).toNat L)
  r15 : s.gpr .r15 = S
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem call1_after (v : Ctr32Impl) {s₀ s : State} {St D S : Addr} {L R : Nat}
    (h : VG.Proof.CmacAes.Stream.X86_64.AMid₁ s₀ St D S L R s) :
    WP isa (.call ("vg_cmac_aes_update" ++ v.suffix) (Impl.CmacAes.X86_64.update v.callee)) s
      (VG.Proof.CmacAes.Stream.X86_64.AAfter₁ s₀ St D S L) :=
  WP.mono (VG.Proof.CmacAes.Stream.X86_64.upd_call v _ h.args) fun _ h₆ =>
    ⟨by rw [h₆.saved _ (by simp [calleeSaved]), h.rbx], by rw [h₆.saved _ (by simp [calleeSaved]), h.rbp],
      by rw [h₆.saved _ (by simp [calleeSaved]), h.r13], by rw [h₆.saved _ (by simp [calleeSaved]), h.r14],
      by rw [h₆.saved _ (by simp [calleeSaved]), h.r15], by rw [h₆.saved _ (by simp [calleeSaved]), h.rsp],
      by rw [h₆.rd, h.rd], by rw [h₆.wr, h.wr]⟩

/-- What `chain2` leaves, for the second call. -/
structure AMid₂ (s₀ : State) (St D S : Addr) (L R : Nat) (s : State) : Prop where
  args : VG.Proof.CmacAes.Stream.X86_64.UArgs s St (St + BitVec.ofNat 64 272) (D + BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.X86_64.fOf (s₀.gpr .rdx).toNat L)) S R
    (VG.Proof.CmacAes.Stream.X86_64.nbOf (s₀.gpr .rdx).toNat L)
  rbx : s.gpr .rbx = St
  r12 : s.gpr .r12 = BitVec.ofNat 64 (16 * VG.Proof.CmacAes.Stream.X86_64.nbOf (s₀.gpr .rdx).toNat L)
  r13 : s.gpr .r13 = D + BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.X86_64.fOf (s₀.gpr .rdx).toNat L)
  r14 : s.gpr .r14 = BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.X86_64.leftOf (s₀.gpr .rdx).toNat L)
  r15 : s.gpr .r15 = S
  rsp : s.gpr .rsp = s₀.gpr .rsp

theorem chain2_mid {s₀ s : State} {St D S : Addr} {L R : Nat} (hp : VG.Proof.CmacAes.Stream.X86_64.APre s₀ St D S L R)
    (h : VG.Proof.CmacAes.Stream.X86_64.AAfter₁ s₀ St D S L s) : WP isa chain2 s (VG.Proof.CmacAes.Stream.X86_64.AMid₂ s₀ St D S L R) := by
  obtain ⟨c, hc⟩ : ∃ c, (s₀.gpr .rdx).toNat = c := ⟨_, rfl⟩
  have hL := hp.lt
  have ⟨hfL, _⟩ := VG.Proof.CmacAes.Stream.X86_64.f_le c L
  have hsum := VG.Proof.CmacAes.Stream.X86_64.nb_le c L
  obtain ⟨rbx₆, rbp₆, r13₆, r14₆, r15₆, rsp₆, rd₆, wr₆⟩ := h
  rw [hc] at r13₆ r14₆
  refine WP.mono (VG.Proof.CmacAes.Stream.X86_64.chain2_wp (x := VG.Proof.CmacAes.Stream.X86_64.leftOf c L) (by unfold VG.Proof.CmacAes.Stream.X86_64.leftOf; omega) r14₆) fun s₇ h₇ => ?_
  obtain ⟨r12₇, r8₇, rdi₇, rsi₇, rdx₇, rcx₇, r9₇, sv₇, -, rd₇, wr₇⟩ := h₇
  have hnb : (if VG.Proof.CmacAes.Stream.X86_64.leftOf c L = 0 then 0 else (VG.Proof.CmacAes.Stream.X86_64.leftOf c L - 1) / 16) = VG.Proof.CmacAes.Stream.X86_64.nbOf c L := rfl
  rw [hnb] at r12₇ r8₇
  have k₇ (r : Reg) (hr : r ∈ calleeSaved) (a : r ≠ .r12) : s₇.gpr r = s.gpr r := sv₇ r hr a
  have c272 : Region.Sub ⟨St + BitVec.ofNat 64 272, 16⟩ ⟨St, 304⟩ := Offset.sub_base St (by decide)
  subst hc
  have dD : Region.Sub ⟨D + BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.X86_64.fOf (s₀.gpr .rdx).toNat L), 16 * VG.Proof.CmacAes.Stream.X86_64.nbOf (s₀.gpr .rdx).toNat L⟩ ⟨D, L⟩ :=
    Offset.sub_base D (by omega)
  refine ⟨hp.uargs (s := s₇) (Dd := D + BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.X86_64.fOf (s₀.gpr .rdx).toNat L)) (n := VG.Proof.CmacAes.Stream.X86_64.nbOf (s₀.gpr .rdx).toNat L)
    (by rw [rdi₇, rbx₆]) (by rw [rsi₇, rbp₆]) (by rw [rdx₇, rbx₆]) (by rw [rcx₇, r13₆]) r8₇
    (by rw [r9₇, r15₆]) (by rw [k₇ _ (by simp [calleeSaved]) (by decide), rsp₆]) (by rw [rd₇, rd₆])
    (by rw [wr₇, wr₆]) (by omega) ((hp.st_d.sub_left c272).symm.sub_left dD)
    ((hp.d_s.sub_left dD).sub_right (Region.sub_prefix (by decide))) (hp.stk_d.sub_right dD)
    (by
      by_cases h0 : VG.Proof.CmacAes.Stream.X86_64.nbOf (s₀.gpr .rdx).toNat L = 0
      · rw [h0]; have := (D + BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.X86_64.fOf (s₀.gpr .rdx).toNat L)).isLt; omega
      · have := hp.wD; rw [VG.Proof.CmacAes.Stream.X86_64.toNat_add_lt D hp.wD (by omega)]; omega)
    ⟨⟨D, L⟩, by simp, VG.Proof.CmacAes.Stream.X86_64.fOf (s₀.gpr .rdx).toNat L, rfl, by simp; omega⟩,
    by rw [k₇ _ (by simp [calleeSaved]) (by decide), rbx₆], r12₇,
    by rw [k₇ _ (by simp [calleeSaved]) (by decide), r13₆], by rw [k₇ _ (by simp [calleeSaved]) (by decide), r14₆],
    by rw [k₇ _ (by simp [calleeSaved]) (by decide), r15₆],
    by rw [k₇ _ (by simp [calleeSaved]) (by decide), rsp₆]⟩

/-- What the second call leaves, for `absorbPost`. -/
structure AAfter₂ (s₀ : State) (St D S : Addr) (L : Nat) (s : State) : Prop where
  rbx : s.gpr .rbx = St
  r12 : s.gpr .r12 = BitVec.ofNat 64 (16 * VG.Proof.CmacAes.Stream.X86_64.nbOf (s₀.gpr .rdx).toNat L)
  r13 : s.gpr .r13 = D + BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.X86_64.fOf (s₀.gpr .rdx).toNat L)
  r14 : s.gpr .r14 = BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.X86_64.leftOf (s₀.gpr .rdx).toNat L)
  r15 : s.gpr .r15 = S

theorem call2_after (v : Ctr32Impl) {s₀ s : State} {St D S : Addr} {L R : Nat}
    (h : VG.Proof.CmacAes.Stream.X86_64.AMid₂ s₀ St D S L R s) :
    WP isa (.call ("vg_cmac_aes_update" ++ v.suffix) (Impl.CmacAes.X86_64.update v.callee)) s
      (VG.Proof.CmacAes.Stream.X86_64.AAfter₂ s₀ St D S L) :=
  WP.mono (VG.Proof.CmacAes.Stream.X86_64.upd_call v _ h.args) fun _ h₈ =>
    ⟨by rw [h₈.saved _ (by simp [calleeSaved]), h.rbx], by rw [h₈.saved _ (by simp [calleeSaved]), h.r12],
      by rw [h₈.saved _ (by simp [calleeSaved]), h.r13], by rw [h₈.saved _ (by simp [calleeSaved]), h.r14],
      by rw [h₈.saved _ (by simp [calleeSaved]), h.r15]⟩

theorem absorb_rel (v : Ctr32Impl) {s₀ s₀' : State} (h0 : absorbX86_64.pre s₀) (h0' : absorbX86_64.pre s₀')
    (hq : absorbX86_64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (absorb v.callee v.suffix) fun _ _ => True := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := hq
  have hp := APre.of h0
  have hp' : VG.Proof.CmacAes.Stream.X86_64.APre s₀' (s₀.gpr .rdi) (s₀.gpr .rcx) (s₀.gpr .r9) (s₀.gpr .r8).toNat (s₀.gpr .rsi).toNat := by
    rw [q2, q3, q5, q6, q7]; exact APre.of h0'
  generalize s₀.gpr .rdi = St at hp hp'
  generalize s₀.gpr .rcx = D at hp hp'
  generalize s₀.gpr .r9 = S at hp hp'
  generalize (s₀.gpr .r8).toNat = L at hp hp'
  generalize (s₀.gpr .rsi).toNat = R at hp hp'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) absorbPre h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.rbx, .rbp, .r13, .r14, .r15, .rsp]) chain2 h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ h, (taint.check (Taint.ofRegs [.rbx, .r12, .r13, .r14, .r15]) absorbPost h).isSome =
      true := ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption) hA).wp
    (F₁ := VG.Proof.CmacAes.Stream.X86_64.AMid₁ s₀ St D S L R) (F₂ := VG.Proof.CmacAes.Stream.X86_64.AMid₁ s₀' St D S L R) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨VG.Proof.CmacAes.Stream.X86_64.absorbPre_wp hp, VG.Proof.CmacAes.Stream.X86_64.absorbPre_wp hp'⟩
  have c₁ := (VG.Proof.CmacAes.Stream.X86_64.upd_rel v _ (P := fun a b => VG.Proof.CmacAes.Stream.X86_64.AMid₁ s₀ St D S L R a ∧ VG.Proof.CmacAes.Stream.X86_64.AMid₁ s₀' St D S L R b)
    fun a b h => ⟨_, _, _, _, _, _, h.1.args, by rw [q4]; exact h.2.args, by rw [h.1.rsp, h.2.rsp, q1]⟩).wp
    (F₁ := VG.Proof.CmacAes.Stream.X86_64.AAfter₁ s₀ St D S L) (F₂ := VG.Proof.CmacAes.Stream.X86_64.AAfter₁ s₀' St D S L) fun a b h => ⟨VG.Proof.CmacAes.Stream.X86_64.call1_after v h.1, VG.Proof.CmacAes.Stream.X86_64.call1_after v h.2⟩
  have m := (RelCT.taint (A := taint) (P := fun a b => VG.Proof.CmacAes.Stream.X86_64.AAfter₁ s₀ St D S L a ∧ VG.Proof.CmacAes.Stream.X86_64.AAfter₁ s₀' St D S L b) _
    (fun a b h => by
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [h.1.rbx, h.2.rbx]
      · rw [h.1.rbp, h.2.rbp, q3]
      · rw [h.1.r13, h.2.r13, q4]
      · rw [h.1.r14, h.2.r14, q4]
      · rw [h.1.r15, h.2.r15]
      · rw [h.1.rsp, h.2.rsp, q1]) hB).wp
    (F₁ := VG.Proof.CmacAes.Stream.X86_64.AMid₂ s₀ St D S L R) (F₂ := VG.Proof.CmacAes.Stream.X86_64.AMid₂ s₀' St D S L R) fun a b h => ⟨VG.Proof.CmacAes.Stream.X86_64.chain2_mid hp h.1, VG.Proof.CmacAes.Stream.X86_64.chain2_mid hp' h.2⟩
  have c₂ := (VG.Proof.CmacAes.Stream.X86_64.upd_rel v _ (P := fun a b => VG.Proof.CmacAes.Stream.X86_64.AMid₂ s₀ St D S L R a ∧ VG.Proof.CmacAes.Stream.X86_64.AMid₂ s₀' St D S L R b)
    fun a b h => ⟨_, _, _, _, _, _, h.1.args, by rw [q4]; exact h.2.args, by rw [h.1.rsp, h.2.rsp, q1]⟩).wp
    (F₁ := VG.Proof.CmacAes.Stream.X86_64.AAfter₂ s₀ St D S L) (F₂ := VG.Proof.CmacAes.Stream.X86_64.AAfter₂ s₀' St D S L) fun a b h =>
      ⟨VG.Proof.CmacAes.Stream.X86_64.call2_after v h.1, VG.Proof.CmacAes.Stream.X86_64.call2_after v h.2⟩
  have p := RelCT.taint (A := taint) (P := fun a b => VG.Proof.CmacAes.Stream.X86_64.AAfter₂ s₀ St D S L a ∧ VG.Proof.CmacAes.Stream.X86_64.AAfter₂ s₀' St D S L b) _
    (fun a b h => by
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [h.1.rbx, h.2.rbx]
      · rw [h.1.r12, h.2.r12, q4]
      · rw [h.1.r13, h.2.r13, q4]
      · rw [h.1.r14, h.2.r14, q4]
      · rw [h.1.r15, h.2.r15]) hC
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((c₁.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((m.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((c₂.mono (fun _ _ h => h) fun _ _ h => h.2).seq p)))

theorem absorb_ct (v : Ctr32Impl) :
    ConstantTime isa absorbX86_64.pre absorbX86_64.pub (absorb v.callee v.suffix) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (VG.Proof.CmacAes.Stream.X86_64.absorb_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.Stream.X86_64

end

/-!
# Streaming AES-CMAC on x86-64: `Verified`

Correctness and constant time (for any implementation `v` of AES), a state
satisfying each precondition, and the shared contracts of
`Spec/Cmac/Contract.lean` (with 16 bytes of stack: the return addresses of the
call of a CMAC function and of its call of `vg_aes_ctr32`).
-/

namespace VG.Proof.CmacAes.Stream.X86_64

open VG VG.X86_64 VG.Impl.CmacAes.Stream.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.CmacAes.X86_64 (update_mx subkeys_mx finalize_mx update_spSafe subkeys_spSafe finalize_spSafe)

theorem init_mx (v : Ctr32Impl) :
    (init v.expand v.callee v.suffix).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [init, Code.allInstrs, v.expandMxcsr, subkeys_mx v]; decide +kernel

theorem absorb_mx (v : Ctr32Impl) : (absorb v.callee v.suffix).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [absorb, absorbPre, absorbPost, held, fill, copy, chain1, chain2, Code.allInstrs, update_mx v]
  decide +kernel

theorem finish_mx (v : Ctr32Impl) : (finish v.callee v.suffix).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [finish, finPre, lastLen, Code.allInstrs, finalize_mx v]; decide +kernel

theorem init_spSafe (v : Ctr32Impl) :
    (init v.expand v.callee v.suffix).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [init, Code.all, v.expandSpSafe, subkeys_spSafe v]; decide +kernel

theorem absorb_spSafe (v : Ctr32Impl) :
    (absorb v.callee v.suffix).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [absorb, absorbPre, absorbPost, held, fill, copy, chain1, chain2, Code.all, update_spSafe v]
  decide +kernel

theorem finish_spSafe (v : Ctr32Impl) :
    (finish v.callee v.suffix).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [finish, finPre, lastLen, Code.all, finalize_spSafe v]; decide +kernel

theorem init_correct (v : Ctr32Impl) (s : State) (hs : initX86_64.pre s) :
    ∃ t s', Exec isa (init v.expand v.callee v.suffix) s t s' ∧ abiPreserved s s' ∧ initX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := VG.Proof.CmacAes.Stream.X86_64.init_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (VG.Proof.CmacAes.Stream.X86_64.init_mx v) he hg, hp⟩

theorem absorb_correct (v : Ctr32Impl) (s : State) (hs : absorbX86_64.pre s) :
    ∃ t s', Exec isa (absorb v.callee v.suffix) s t s' ∧ abiPreserved s s' ∧ absorbX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := VG.Proof.CmacAes.Stream.X86_64.absorb_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (VG.Proof.CmacAes.Stream.X86_64.absorb_mx v) he hg, hp⟩

theorem finish_correct (v : Ctr32Impl) (s : State) (hs : finishX86_64.pre s) :
    ∃ t s', Exec isa (finish v.callee v.suffix) s t s' ∧ abiPreserved s s' ∧ finishX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := VG.Proof.CmacAes.Stream.X86_64.finish_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (VG.Proof.CmacAes.Stream.X86_64.finish_mx v) he hg, hp⟩

/-- A state satisfying `vg_cmac_aes_init`'s precondition. -/
def initSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x3000 | .rdx => 16 | .rcx => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x3000, 16⟩]
  wr := [⟨0x1000, 304⟩, ⟨0x4000, 2304⟩]

theorem init_verified (v : Ctr32Impl) :
    Verified X86_64.target (init v.expand v.callee v.suffix) (initScratchContract X86_64.abi 16) :=
  Verified.of_correct (VG.Proof.CmacAes.Stream.X86_64.init_correct v) (VG.Proof.CmacAes.Stream.X86_64.init_ct v) (by
    sig_implies [initScratchContract, initScratchSig, Spec.Cmac.aesInitPre, Spec.Cmac.aesInitPost, VG.Proof.CmacAes.Stream.X86_64.initX86_64, X86_64.abi,
      X86_64.argRegs] [initSat] using VG.Proof.CmacAes.Stream.X86_64.initSat)

/-- A state satisfying `vg_cmac_aes_absorb`'s precondition (with no data). -/
def absorbSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rcx => 0x3000 | .r9 => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x3000, 0⟩]
  wr := [⟨0x1000, 304⟩, ⟨0x4000, 2304⟩]

theorem absorb_verified (v : Ctr32Impl) :
    Verified X86_64.target (absorb v.callee v.suffix) (absorbScratchContract X86_64.abi 16) :=
  Verified.of_correct (VG.Proof.CmacAes.Stream.X86_64.absorb_correct v) (VG.Proof.CmacAes.Stream.X86_64.absorb_ct v) (by
    sig_implies [absorbScratchContract, absorbScratchSig, Spec.Cmac.aesAbsorbPre, Spec.Cmac.aesAbsorbPost, VG.Proof.CmacAes.Stream.X86_64.absorbX86_64, X86_64.abi,
      X86_64.argRegs] [absorbSat] using VG.Proof.CmacAes.Stream.X86_64.absorbSat)

/-- A state satisfying `vg_cmac_aes_finish`'s precondition. -/
def finishSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rcx => 0x2000 | .r8 => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 304⟩, ⟨0x2000, 16⟩, ⟨0x4000, 2304⟩]

theorem finish_verified (v : Ctr32Impl) :
    Verified X86_64.target (finish v.callee v.suffix) (finishScratchContract X86_64.abi 16) :=
  Verified.of_correct (VG.Proof.CmacAes.Stream.X86_64.finish_correct v) (VG.Proof.CmacAes.Stream.X86_64.finish_ct v) (by
    sig_implies [finishScratchContract, finishScratchSig, Spec.Cmac.aesFinishPre, Spec.Cmac.aesFinishPost, VG.Proof.CmacAes.Stream.X86_64.finishX86_64, X86_64.abi,
      X86_64.argRegs] [finishSat] using VG.Proof.CmacAes.Stream.X86_64.finishSat)

end VG.Proof.CmacAes.Stream.X86_64

end
