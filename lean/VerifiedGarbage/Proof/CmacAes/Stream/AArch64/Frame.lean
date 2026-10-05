import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.CmacAes.AArch64.Variant
import VerifiedGarbage.Proof.CmacAes.AArch64.Verified
import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Impl.CmacAes.Stream.AArch64
import VerifiedGarbage.Proof.Framework.AArch64.Spill
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Cmac.Contract
import VerifiedGarbage.Proof.CmacAes.Stream.Scratch
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.Stream.AArch64.Common`. -/
section

section

section

/-!
# Streaming AES-CMAC on AArch64: the contracts the proofs are written against

The artifacts' contracts are the shared ones of `Spec/Cmac/Contract.lean`,
which imply these (`Verified.lean`). A call (`bl`) stores nothing in memory,
so no stack is used.
-/

namespace VG.Proof.CmacAes.Stream.AArch64

open VG VG.AArch64

/-- `vg_cmac_aes_init(state = x0, key = x1, key_len = x2, scratch = x3)`. -/
def initAArch64 : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 304⟩
    let key : Region := ⟨s.gpr .x1, (s.gpr .x2).toNat⟩
    let scr : Region := ⟨s.gpr .x3, 2304⟩
    s.rd = [key] ∧ s.wr = [state, scr] ∧
      state.Disjoint key ∧ state.Disjoint scr ∧ key.Disjoint scr ∧
      (s.gpr .x0).toNat + 304 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + (s.gpr .x2).toNat ≤ 2 ^ 64 ∧
      (s.gpr .x3).toNat + 2304 ≤ 2 ^ 64 ∧
      ((s.gpr .x2).toNat = 16 ∨ (s.gpr .x2).toNat = 24 ∨ (s.gpr .x2).toNat = 32)
  post s s' :=
    Spec.Cmac.Repr s'.mem (s.gpr .x0) (Spec.Aes.bytesAt s.mem (s.gpr .x1) (s.gpr .x2).toNat) []
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

/-- `vg_cmac_aes_absorb(state = x0, rounds = x1, count = x2, data = x3, len = x4, scratch = x5)`. -/
def absorbAArch64 : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 304⟩
    let data : Region := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
    let scr : Region := ⟨s.gpr .x5, 2304⟩
    s.rd = [data] ∧ s.wr = [state, scr] ∧
      state.Disjoint data ∧ state.Disjoint scr ∧ data.Disjoint scr ∧
      (s.gpr .x0).toNat + 304 ≤ 2 ^ 64 ∧ (s.gpr .x3).toNat + (s.gpr .x4).toNat ≤ 2 ^ 64 ∧
      (s.gpr .x5).toNat + 2304 ≤ 2 ^ 64 ∧
      ((s.gpr .x1).toNat = 10 ∨ (s.gpr .x1).toNat = 12 ∨ (s.gpr .x1).toNat = 14)
  post s s' :=
    ∀ key msg, Spec.Cmac.Repr s.mem (s.gpr .x0) key msg →
      (s.gpr .x1).toNat = Spec.Aes.rounds (key.length / 4) →
      s.gpr .x2 = BitVec.ofNat 64 msg.length → msg.length + (s.gpr .x4).toNat < 2 ^ 64 →
      Spec.Cmac.Repr s'.mem (s.gpr .x0) key
        (msg ++ Spec.Aes.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧ s₁.sp = s₂.sp

/-- `vg_cmac_aes_finish(state = x0, rounds = x1, count = x2, out = x3, scratch = x4)`. -/
def finishAArch64 : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 304⟩
    let out : Region := ⟨s.gpr .x3, 16⟩
    let scr : Region := ⟨s.gpr .x4, 2304⟩
    s.rd = [] ∧ s.wr = [state, out, scr] ∧
      state.Disjoint out ∧ state.Disjoint scr ∧ out.Disjoint scr ∧
      (s.gpr .x0).toNat + 304 ≤ 2 ^ 64 ∧ (s.gpr .x3).toNat + 16 ≤ 2 ^ 64 ∧
      (s.gpr .x4).toNat + 2304 ≤ 2 ^ 64 ∧
      ((s.gpr .x1).toNat = 10 ∨ (s.gpr .x1).toNat = 12 ∨ (s.gpr .x1).toNat = 14)
  post s s' :=
    ∀ key msg, Spec.Cmac.Repr s.mem (s.gpr .x0) key msg →
      (s.gpr .x1).toNat = Spec.Aes.rounds (key.length / 4) →
      s.gpr .x2 = BitVec.ofNat 64 msg.length → msg.length < 2 ^ 64 →
      Spec.Aes.bytesAt s'.mem (s.gpr .x3) 16 = Spec.Cmac.aesCmac key 16 msg
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

end VG.Proof.CmacAes.Stream.AArch64

end

/-!
# Streaming AES-CMAC on AArch64: the calls

A call of each function the streaming functions call (`vg_aes_expand_key_scratch`,
`vg_cmac_aes_subkeys`, `vg_cmac_aes_update` and `vg_cmac_aes_finalize`, for
any implementation of AES), from its contract (with `WP.call`): what it needs
(`…Args`), what it leaves (`…Post`, in terms of the memory before the call),
and that two calls with the same arguments leak the same (`…_rel`). A call
stores nothing in memory: the callees change only the buffers they are given.
-/

namespace VG.Proof.CmacAes.Stream.AArch64

open VG VG.AArch64
open VG.Proof.Aes.AArch64 (Ctr32Impl)
open VG.Proof.CmacAes.AArch64 (updateAArch64 subkeysAArch64 finalizeAArch64 update_correct subkeys_correct
  finalize_correct update_ct subkeys_ct finalize_ct toNat_rounds callEntry_x0 callEntry_x1 callEntry_x2
  callEntry_x3 callEntry_x4 callEntry_x5)

theorem toNat_ofNat {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-! ## No frames -/

theorem subkeys_noFrames (v : Ctr32Impl) : (Impl.CmacAes.AArch64.subkeys v.callee).noFrames = true := by
  simp [Impl.CmacAes.AArch64.subkeys, Code.noFrames, v.noFrames]

theorem finalize_noFrames (v : Ctr32Impl) : (Impl.CmacAes.AArch64.finalize v.callee).noFrames = true := by
  simp [Impl.CmacAes.AArch64.finalize, Impl.CmacAes.AArch64.finPre, Impl.CmacAes.AArch64.partialBlock,
    Impl.CmacAes.AArch64.copy, Code.noFrames, v.noFrames]

/-! ## `vg_cmac_aes_update` -/

/-- What a call of `vg_cmac_aes_update` needs: the key schedule `W`, the
chaining value `C`, `n` blocks at `D`, the working space `S` and the rounds
`R`. -/
structure UArgs (s : State) (W C D S : Addr) (R n : Nat) : Prop where
  x0 : s.gpr .x0 = W
  x1 : s.gpr .x1 = BitVec.ofNat 64 R
  x2 : s.gpr .x2 = C
  x3 : s.gpr .x3 = D
  x4 : s.gpr .x4 = BitVec.ofNat 64 n
  x5 : s.gpr .x5 = S
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
  saved : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r
  frame : Frame [⟨C, 16⟩, ⟨S, 2176⟩] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem C 16 =
    Spec.Cmac.chain (Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem W (16 * (R + 1))))
      (Spec.Aes.bytesAt s.mem C 16) (Spec.Cmac.blocksAt s.mem D 16 n)

theorem UArgs.pre {s : State} {W C D S : Addr} {R n : Nat} (h : VG.Proof.CmacAes.Stream.AArch64.UArgs s W C D S R n) :
    updateAArch64.pre (s.callEntry.withRegions [⟨W, 240⟩, ⟨D, 16 * n⟩] [⟨C, 16⟩, ⟨S, 2176⟩]) := by
  have hR := toNat_rounds h.rounds
  have hN := VG.Proof.CmacAes.Stream.AArch64.toNat_ofNat (n := n) (by have := h.hn; omega)
  simp only [updateAArch64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, callEntry_x4, callEntry_x5,
    h.x0, h.x1, h.x2, h.x3, h.x4, h.x5, hR, hN]
  exact ⟨trivial, trivial, h.wc, h.ws, h.dc, h.ds, h.cs, h.wrapC, h.wrapD, h.wrapS, h.rounds⟩

theorem upd_call (v : Proof.CmacAes.AArch64.UpdateImpl) (nm : String) {s : State} {W C D S : Addr} {R n : Nat}
    (h : VG.Proof.CmacAes.Stream.AArch64.UArgs s W C D S R n) :
    WP isa (.call nm v.callee.code) s (VG.Proof.CmacAes.Stream.AArch64.UPost s W C D S R n) := by
  have hR := toNat_rounds h.rounds
  have hN := VG.Proof.CmacAes.Stream.AArch64.toNat_ofNat (n := n) (by have := h.hn; omega)
  refine WP.call (k := updateAArch64) v.ok h.pre h.reads h.writes ?_ v.noFrames
  intro s' hrd hwr hsp hf hsaved _ hpost
  refine ⟨hrd, hwr, hsp, hsaved, hf, ?_⟩
  simp only [updateAArch64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, callEntry_x4, h.x0, h.x1, h.x2, h.x3, h.x4,
    hR, hN] at hpost
  exact hpost

theorem upd_rel (v : Proof.CmacAes.AArch64.UpdateImpl) (nm : String) {W C D S : Addr} {R n : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → VG.Proof.CmacAes.Stream.AArch64.UArgs s₁ W C D S R n ∧ VG.Proof.CmacAes.Stream.AArch64.UArgs s₂ W C D S R n ∧ s₁.sp = s₂.sp) :
    RelCT isa P (.call nm v.callee.code) fun _ _ => True := by
  refine RelCT.call v.ok v.ct [⟨W, 240⟩, ⟨D, 16 * n⟩] [⟨C, 16⟩, ⟨S, 2176⟩] fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes⟩
  simp only [updateAArch64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, callEntry_x4, callEntry_x5,
    h₁.x0, h₁.x1, h₁.x2, h₁.x3, h₁.x4, h₁.x5, h₂.x0, h₂.x1, h₂.x2, h₂.x3, h₂.x4, h₂.x5, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## `vg_cmac_aes_subkeys` -/

/-- What a call of `vg_cmac_aes_subkeys` needs: the key schedule `W`, the
subkeys `K`, the working space `S` and the rounds `R`. -/
structure SArgs (s : State) (W K S : Addr) (R : Nat) : Prop where
  x0 : s.gpr .x0 = W
  x1 : s.gpr .x1 = BitVec.ofNat 64 R
  x2 : s.gpr .x2 = K
  x3 : s.gpr .x3 = S
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
  saved : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r
  frame : Frame [⟨K, 32⟩, ⟨S, 2176⟩] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem K 32 =
    (Spec.Cmac.subkeys (Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem W (16 * (R + 1)))) 16).1 ++
      (Spec.Cmac.subkeys (Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem W (16 * (R + 1)))) 16).2

theorem SArgs.pre {s : State} {W K S : Addr} {R : Nat} (h : VG.Proof.CmacAes.Stream.AArch64.SArgs s W K S R) :
    subkeysAArch64.pre (s.callEntry.withRegions [⟨W, 240⟩] [⟨K, 32⟩, ⟨S, 2176⟩]) := by
  have hR := toNat_rounds h.rounds
  simp only [subkeysAArch64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, h.x0, h.x1, h.x2, h.x3, hR]
  exact ⟨trivial, trivial, h.wk, h.ws, h.ks, h.wrapK, h.wrapS, h.rounds⟩

theorem sub_call (v : Ctr32Impl) (nm : String) {s : State} {W K S : Addr} {R : Nat}
    (h : VG.Proof.CmacAes.Stream.AArch64.SArgs s W K S R) :
    WP isa (.call nm (Impl.CmacAes.AArch64.subkeys v.callee)) s (VG.Proof.CmacAes.Stream.AArch64.SPost s W K S R) := by
  have hR := toNat_rounds h.rounds
  refine WP.call (k := subkeysAArch64) (subkeys_correct v) h.pre h.reads h.writes ?_ (VG.Proof.CmacAes.Stream.AArch64.subkeys_noFrames v)
  intro s' hrd hwr hsp hf hsaved _ hpost
  refine ⟨hrd, hwr, hsp, hsaved, hf, ?_⟩
  simp only [subkeysAArch64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    callEntry_x0, callEntry_x1, callEntry_x2, h.x0, h.x1, h.x2, hR] at hpost
  exact hpost

theorem sub_rel (v : Ctr32Impl) (nm : String) {W K S : Addr} {R : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → VG.Proof.CmacAes.Stream.AArch64.SArgs s₁ W K S R ∧ VG.Proof.CmacAes.Stream.AArch64.SArgs s₂ W K S R ∧ s₁.sp = s₂.sp) :
    RelCT isa P (.call nm (Impl.CmacAes.AArch64.subkeys v.callee)) fun _ _ => True := by
  refine RelCT.call (subkeys_correct v) (subkeys_ct v) [⟨W, 240⟩] [⟨K, 32⟩, ⟨S, 2176⟩] fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes⟩
  simp only [subkeysAArch64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3,
    h₁.x0, h₁.x1, h₁.x2, h₁.x3, h₂.x0, h₂.x1, h₂.x2, h₂.x3, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

/-! ## `vg_cmac_aes_finalize` -/

/-- What a call of `vg_cmac_aes_finalize` needs: the key schedule and
subkeys `K`, the state `St`, the `L` last bytes at `P`, the working space
`S` and the rounds `R`. -/
structure FArgs (s : State) (K St P S : Addr) (L R : Nat) : Prop where
  x0 : s.gpr .x0 = K
  x1 : s.gpr .x1 = BitVec.ofNat 64 R
  x2 : s.gpr .x2 = St
  x3 : s.gpr .x3 = P
  x4 : s.gpr .x4 = BitVec.ofNat 64 L
  x5 : s.gpr .x5 = S
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
  saved : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r
  frame : Frame [⟨St, 16⟩, ⟨S, 2176⟩] s.mem s'.mem
  out : let ciph := Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem K (16 * (R + 1)))
    let ks := Spec.Cmac.subkeys ciph 16
    Spec.Aes.bytesAt s.mem (K + 240) 32 = ks.1 ++ ks.2 →
    ∀ msg : List Byte, msg.length % 16 = 0 → (msg = [] ∨ 0 < L) →
      Spec.Aes.bytesAt s.mem St 16 = Spec.Cmac.chain ciph (Spec.Cmac.zeros 16) (Spec.Cmac.blocks 16 msg) →
      Spec.Aes.bytesAt s'.mem St 16 = Spec.Cmac.macFull ciph 16 (msg ++ Spec.Aes.bytesAt s.mem P L)

theorem FArgs.pre {s : State} {K St P S : Addr} {L R : Nat} (h : VG.Proof.CmacAes.Stream.AArch64.FArgs s K St P S L R) :
    finalizeAArch64.pre (s.callEntry.withRegions [⟨K, 272⟩, ⟨P, L⟩] [⟨St, 16⟩, ⟨S, 2176⟩]) := by
  have hR := toNat_rounds h.rounds
  have hL := VG.Proof.CmacAes.Stream.AArch64.toNat_ofNat (n := L) (by have := h.len; omega)
  simp only [finalizeAArch64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, callEntry_x4, callEntry_x5,
    h.x0, h.x1, h.x2, h.x3, h.x4, h.x5, hR, hL]
  exact ⟨trivial, trivial, h.kst, h.ks, h.pst, h.ps, h.sts, h.wrapK, h.wrapSt, h.wrapP, h.wrapS,
    h.rounds, h.len⟩

theorem fin_call (v : Ctr32Impl) (nm : String) {s : State} {K St P S : Addr} {L R : Nat}
    (h : VG.Proof.CmacAes.Stream.AArch64.FArgs s K St P S L R) :
    WP isa (.call nm (Impl.CmacAes.AArch64.finalize v.callee)) s (VG.Proof.CmacAes.Stream.AArch64.FPost s K St P S L R) := by
  have hR := toNat_rounds h.rounds
  have hL := VG.Proof.CmacAes.Stream.AArch64.toNat_ofNat (n := L) (by have := h.len; omega)
  refine WP.call (k := finalizeAArch64) (finalize_correct v) h.pre h.reads h.writes ?_
    (VG.Proof.CmacAes.Stream.AArch64.finalize_noFrames v)
  intro s' hrd hwr hsp hf hsaved _ hpost
  refine ⟨hrd, hwr, hsp, hsaved, hf, ?_⟩
  simp only [finalizeAArch64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, callEntry_x4, h.x0, h.x1, h.x2, h.x3, h.x4,
    hR, hL] at hpost
  exact hpost

theorem fin_rel (v : Ctr32Impl) (nm : String) {K St Q S : Addr} {L R : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → VG.Proof.CmacAes.Stream.AArch64.FArgs s₁ K St Q S L R ∧ VG.Proof.CmacAes.Stream.AArch64.FArgs s₂ K St Q S L R ∧ s₁.sp = s₂.sp) :
    RelCT isa P (.call nm (Impl.CmacAes.AArch64.finalize v.callee)) fun _ _ => True := by
  refine RelCT.call (finalize_correct v) (finalize_ct v) [⟨K, 272⟩, ⟨Q, L⟩] [⟨St, 16⟩, ⟨S, 2176⟩]
    fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes⟩
  simp only [finalizeAArch64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, callEntry_x4, callEntry_x5,
    h₁.x0, h₁.x1, h₁.x2, h₁.x3, h₁.x4, h₁.x5, h₂.x0, h₂.x1, h₂.x2, h₂.x3, h₂.x4, h₂.x5, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## `vg_aes_expand_key_scratch` -/

/-- What a call of `vg_aes_expand_key_scratch` needs: the key `Kp` of `KL` bytes,
the schedule `W` and the working space `S`. -/
structure EArgs (s : State) (Kp W S : Addr) (KL : Nat) : Prop where
  x0 : s.gpr .x0 = Kp
  x1 : s.gpr .x1 = BitVec.ofNat 64 KL
  x2 : s.gpr .x2 = W
  x3 : s.gpr .x3 = S
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
  saved : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r
  frame : Frame [⟨W, 240⟩, ⟨S, 512⟩] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem W (16 * (Spec.Aes.rounds (KL / 4) + 1)) =
    Spec.Aes.expandKey (Spec.Aes.bytesAt s.mem Kp KL)

theorem EArgs.pre {s : State} {Kp W S : Addr} {KL : Nat} (h : VG.Proof.CmacAes.Stream.AArch64.EArgs s Kp W S KL) :
    Proof.Aes.expandKeyAArch64.pre (s.callEntry.withRegions [⟨Kp, KL⟩] [⟨W, 240⟩, ⟨S, 512⟩]) := by
  have hK := VG.Proof.CmacAes.Stream.AArch64.toNat_ofNat (n := KL) (by rcases h.klen with h | h | h <;> omega)
  simp only [Proof.Aes.expandKeyAArch64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, h.x0, h.x1, h.x2, h.x3, hK]
  exact ⟨trivial, trivial, h.kw, h.ks, h.ws, h.klen⟩

theorem ek_call (v : Ctr32Impl) {s : State} {Kp W S : Addr} {KL : Nat} (h : VG.Proof.CmacAes.Stream.AArch64.EArgs s Kp W S KL) :
    WP isa (.call v.expand.name v.expand.code) s (VG.Proof.CmacAes.Stream.AArch64.EPost s Kp W S KL) := by
  have hK := VG.Proof.CmacAes.Stream.AArch64.toNat_ofNat (n := KL) (by rcases h.klen with h | h | h <;> omega)
  refine WP.call (k := Proof.Aes.expandKeyAArch64) v.expandOk h.pre h.reads h.writes ?_ v.expandNoFrames
  intro s' hrd hwr hsp hf hsaved _ hpost
  refine ⟨hrd, hwr, hsp, hsaved, hf, ?_⟩
  simp only [Proof.Aes.expandKeyAArch64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    callEntry_x0, callEntry_x1, callEntry_x2, h.x0, h.x1, h.x2, hK] at hpost
  exact hpost

theorem ek_rel (v : Ctr32Impl) {Kp W S : Addr} {KL : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → VG.Proof.CmacAes.Stream.AArch64.EArgs s₁ Kp W S KL ∧ VG.Proof.CmacAes.Stream.AArch64.EArgs s₂ Kp W S KL ∧ s₁.sp = s₂.sp) :
    RelCT isa P (.call v.expand.name v.expand.code) fun _ _ => True := by
  refine RelCT.call v.expandOk v.expandCt [⟨Kp, KL⟩] [⟨W, 240⟩, ⟨S, 512⟩] fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes⟩
  simp only [Proof.Aes.expandKeyAArch64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3,
    h₁.x0, h₁.x1, h₁.x2, h₁.x3, h₂.x0, h₂.x1, h₂.x2, h₂.x3, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

end VG.Proof.CmacAes.Stream.AArch64

end

/-!
# Streaming AES-CMAC on AArch64: arithmetic, memory and copying bytes

The number of bytes held back, as the code computes it from `count`
(`held_bv`); immediates; branch conditions; bytes written (`writeBytes`); and
`copy`, which copies the `x8` bytes at `x7` to `x6`, a byte at a time (none if
`x8` is 0), changing only `x6` to `x9`.
-/

namespace VG.Proof.CmacAes.Stream.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.WriteBytes
open VG.Impl.CmacAes.Stream.AArch64 (copy)
open VG.Proof.Cmac.Stream (held held_pos)
open VG.Proof.CmacAes.AArch64 (copyStep_ok succ_ofNat ofNat_ne_zero)

/-! ## Arithmetic -/

theorem mz0 : BitVec.setWidth 64 (0 : BitVec 16) <<< (16 * 0) = 0 := by decide
theorem mz1 : BitVec.setWidth 64 (1 : BitVec 16) <<< (16 * 0) = 1 := by decide
theorem mz15 : BitVec.setWidth 64 (15 : BitVec 16) <<< (16 * 0) = 15 := by decide
theorem mz16 : BitVec.setWidth 64 (16 : BitVec 16) <<< (16 * 0) = BitVec.ofNat 64 16 := by decide

theorem and15 (x : BitVec 64) : (x &&& 15).toNat = x.toNat % 16 := by
  rw [BitVec.toNat_and, show (15 : BitVec 64).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- The number of bytes held back for a nonzero `count`, as `sub 1; and 15; add 1` computes it. -/
theorem held_bv (c : BitVec 64) (h : c ≠ 0) :
    ((c - BitVec.ofNat 64 1) &&& 15) + BitVec.ofNat 64 1 = BitVec.ofNat 64 (held c.toNat) := by
  have hc : c.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
  rw [held_pos (by omega)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, VG.Proof.CmacAes.Stream.AArch64.and15, BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat]
  have := c.isLt
  omega

theorem toNat_add_lt (p : Addr) {d k : Nat} (h : p.toNat + k ≤ 2 ^ 64) (hd : d < k) :
    (p + BitVec.ofNat 64 d).toNat = p.toNat + d := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : d < 2 ^ 64)]
  exact Nat.mod_eq_of_lt (by omega)

theorem ofNat_toNat_eq {x : BitVec 64} {n : Nat} (h : x.toNat = n) : x = BitVec.ofNat 64 n :=
  BitVec.eq_of_toNat_eq (by rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (h ▸ x.isLt)])

/-- The rounds, as `lsr 2; add 6` computes them from the key length. -/
theorem rounds_bv {KL : Nat} (h : KL = 16 ∨ KL = 24 ∨ KL = 32) :
    BitVec.ofNat 64 KL >>> 2 + BitVec.ofNat 64 6 = BitVec.ofNat 64 (KL / 4 + 6) := by
  rcases h with rfl | rfl | rfl <;> decide

/-! ## Branch conditions -/

theorem eval_zero {s : State} {r : Reg} {x : Nat} (hx : x < 2 ^ 64) (h : s.gpr r = BitVec.ofNat 64 x) :
    isa.eval (.zero .x r) s = some (decide (x = 0)) := by
  show some (s.read .x r == 0) = _
  rw [State.read, h, BitVec.setWidth_eq]
  have := ofNat_ne_zero hx
  rw [bne] at this
  cases hb : (BitVec.ofNat 64 x == 0) <;> rw [hb] at this <;> cases hd : decide (x = 0) <;> simp_all

theorem eval_nonzero {s : State} {r : Reg} {x : Nat} (hx : x < 2 ^ 64) (h : s.gpr r = BitVec.ofNat 64 x) :
    isa.eval (.nonzero .x r) s = some !decide (x = 0) := by
  show some (s.read .x r != 0) = _
  rw [State.read, h, BitVec.setWidth_eq, ofNat_ne_zero hx]

/-! ## Bytes written -/

theorem writeBytes_at (m : Mem) (q : Addr) (xs : List Byte) {i : Nat} (hi : i < 2 ^ 64) :
    writeBytes m q xs (q + BitVec.ofNat 64 i) =
      if i < xs.length then xs.getD i 0 else m (q + BitVec.ofNat 64 i) := by
  simp only [writeBytes, Mem.sub_ofNat_toNat q hi]

theorem bytesAt_writeBytes_self (m : Mem) (q : Addr) {xs : List Byte} (h : xs.length < 2 ^ 64) :
    Spec.Aes.bytesAt (writeBytes m q xs) q xs.length = xs := by
  apply List.ext_getElem (by simp [Spec.Aes.bytesAt])
  intro i h1 _
  simp only [Spec.Aes.bytesAt, List.length_map, List.length_range] at h1
  simp only [Spec.Aes.bytesAt, List.getElem_map, List.getElem_range, VG.Proof.CmacAes.Stream.AArch64.writeBytes_at m q xs (by omega : i < 2 ^ 64),
    h1, ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some]

/-- Bytes `[0, r)` from `p` stay, and the bytes `xs` follow them. -/
theorem bytesAt_writeBytes (m : Mem) (p : Addr) (r : Nat) (xs : List Byte) (h : r + xs.length < 2 ^ 64) :
    Spec.Aes.bytesAt (writeBytes m (p + BitVec.ofNat 64 r) xs) p (r + xs.length) =
      Spec.Aes.bytesAt m p r ++ xs := by
  rw [Proof.Cmac.Stream.bytesAt_append, VG.Proof.CmacAes.Stream.AArch64.bytesAt_writeBytes_self _ _ (by omega)]
  refine congrArg (· ++ xs) ?_
  simp only [Spec.Aes.bytesAt]
  apply List.map_congr_left
  intro i hi
  exact writeBytes_before m p xs (List.mem_range.mp hi) (by omega)

/-! ## Copying bytes -/

/-- What `copy` leaves. -/
structure Copied (s : State) (C : Addr) (xs : List Byte) (s' : State) : Prop where
  mem : s'.mem = writeBytes s.mem C xs
  other : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem copy_ok (s : State) {P C : Addr} {L : Nat} (hL : L < 2 ^ 64) (h7 : s.gpr .x7 = P)
    (h6 : s.gpr .x6 = C) (h8 : s.gpr .x8 = BitVec.ofNat 64 L)
    (hr : ∀ i < L, InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < L, InRegions s.wr (C + BitVec.ofNat 64 i) 1)
    (hdis : (⟨P, L⟩ : Region).Disjoint ⟨C, L⟩) :
    WP isa copy s (VG.Proof.CmacAes.Stream.AArch64.Copied s C (Spec.Aes.bytesAt s.mem P L)) := by
  by_cases hL0 : L = 0
  · subst hL0
    refine WP.ite true (by rw [VG.Proof.CmacAes.Stream.AArch64.eval_zero hL h8]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    exact ⟨by simp [Spec.Aes.bytesAt, writeBytes_nil], fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
  refine WP.ite false (by rw [VG.Proof.CmacAes.Stream.AArch64.eval_zero hL h8]; simp [hL0]) (fun h => by cases h) fun _ => ?_
  refine WP.loop (M := isa) (body := .block Proof.CmacAes.AArch64.copyBody) (c := .nonzero .x .x8)
    (fun (n : Nat) (t : State) => ∃ i, n = L - i ∧ i < L ∧ t.gpr .x7 = P + BitVec.ofNat 64 i ∧
      t.gpr .x6 = C + BitVec.ofNat 64 i ∧ t.gpr .x8 = BitVec.ofNat 64 (L - i) ∧
      t.mem = writeBytes s.mem C (Spec.Aes.bytesAt s.mem P i) ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → t.gpr r = s.gpr r) ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (L - 0) _
    ⟨0, rfl, by omega, by rw [h7]; simp, by rw [h6]; simp, by rw [h8, Nat.sub_zero],
      by simp [Spec.Aes.bytesAt, writeBytes_nil], fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
  rintro n t ⟨i, rfl, hi, x7, x6, x8, mem, g, sp, rd, wr⟩
  obtain ⟨t', run', mem', x7', x6', x8', g', sp', rd', wr'⟩ := copyStep_ok t
    (A := P + BitVec.ofNat 64 i) (B := C + BitVec.ofNat 64 i) (by rw [x7, BitVec.add_zero])
    (by rw [x6, BitVec.add_zero]) (by rw [rd, wr]; exact hr i hi) (by rw [wr]; exact hw i hi)
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hlen : (Spec.Aes.bytesAt s.mem P i).length = i := by simp [Spec.Aes.bytesAt]
  have hx : writeBytes s.mem C (Spec.Aes.bytesAt s.mem P i) (P + BitVec.ofNat 64 i) =
      s.mem (P + BitVec.ofNat 64 i) :=
    (writeBytes_frame s.mem C _ (R := ⟨C, i⟩) (by rw [hlen]; exact Region.contains_self _ _)) _
      fun r hr hcon => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hdis _ (Offset.contains_base P (by omega) (by omega)) (Region.sub_prefix (by omega) _ hcon)
  have hmem : t'.mem = writeBytes s.mem C (Spec.Aes.bytesAt s.mem P (i + 1)) := by
    rw [mem', mem, hx, Proof.Cmac.bytesAt_succ,
      writeBytes_snoc s.mem C (Spec.Aes.bytesAt s.mem P i) (s.mem (P + BitVec.ofNat 64 i)) (by rw [hlen]; omega),
      hlen]
  have x8'' : t'.gpr .x8 = BitVec.ofNat 64 (L - (i + 1)) := by
    rw [x8', x8, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega)]; rfl
  have ev := VG.Proof.CmacAes.Stream.AArch64.eval_nonzero (s := t') (x := L - (i + 1)) (by omega) x8''
  have gg : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → t'.gpr r = s.gpr r := fun r h₁ h₂ h₃ h₄ => by
    rw [g' r h₁ h₂ h₃ h₄, g r h₁ h₂ h₃ h₄]
  by_cases he : i + 1 = L
  · left
    refine ⟨by rw [ev]; simp [he], ⟨by rw [hmem, he], gg, by rw [sp', sp], by rw [rd', rd], by rw [wr', wr]⟩⟩
  · right
    refine ⟨by rw [ev]; simp; omega, L - (i + 1), by omega, i + 1, rfl, by omega,
      by rw [x7', x7, BitVec.add_assoc, succ_ofNat], by rw [x6', x6, BitVec.add_assoc, succ_ofNat], x8'', hmem,
      gg, by rw [sp', sp], by rw [rd', rd], by rw [wr', wr]⟩

end VG.Proof.CmacAes.Stream.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.Stream.AArch64.AbsorbBlocks`. -/
section

/-!
# Streaming AES-CMAC on AArch64: `vg_cmac_aes_absorb`'s straight-line code

What each piece of code between the copies and calls computes, in terms of
`count` (`c`) and `len` (`L`): the bytes held back `h = held c`, the bytes
copied after them `f = min L (16 - h)`, the data left `L - f`, whether to
chain the block held back (`b1`), the blocks chained after it (`nb`), and the
rest (`rest`); and the registers `absorb` saves at `scratch + 2176`, where the
functions it calls do not write, and restores at the end.
-/

namespace VG.Proof.CmacAes.Stream.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.CmacAes.Stream.AArch64
open VG.Impl.CmacAes.AArch64 (mov)
open VG.Proof.CmacAes.AArch64 (readW_writeW_other)
open VG.Proof.Cmac.Stream (held held_le)

/-! ## The numbers -/

/-- The bytes copied after the `held c` held back. -/
def fOf (c L : Nat) : Nat := min L (16 - held c)

/-- The data left after them. -/
def leftOf (c L : Nat) : Nat := L - VG.Proof.CmacAes.Stream.AArch64.fOf c L

/-- The number of blocks the first call chains: the block held back, if data is left. -/
def b1Of (c L : Nat) : Nat := if VG.Proof.CmacAes.Stream.AArch64.leftOf c L = 0 then 0 else 1

/-- The number of blocks the second call chains: those of the data left but its
last 1 to 16 bytes. -/
def nbOf (c L : Nat) : Nat := if VG.Proof.CmacAes.Stream.AArch64.leftOf c L = 0 then 0 else (VG.Proof.CmacAes.Stream.AArch64.leftOf c L - 1) / 16

/-- The bytes copied to the start of the bytes held back at the end. -/
def restOf (c L : Nat) : Nat := VG.Proof.CmacAes.Stream.AArch64.leftOf c L - 16 * VG.Proof.CmacAes.Stream.AArch64.nbOf c L

theorem f_le (c L : Nat) : VG.Proof.CmacAes.Stream.AArch64.fOf c L ≤ L ∧ VG.Proof.CmacAes.Stream.AArch64.fOf c L + held c ≤ 16 := by
  have := held_le c; unfold VG.Proof.CmacAes.Stream.AArch64.fOf; omega

theorem nb_le (c L : Nat) : VG.Proof.CmacAes.Stream.AArch64.fOf c L + 16 * VG.Proof.CmacAes.Stream.AArch64.nbOf c L + VG.Proof.CmacAes.Stream.AArch64.restOf c L = L := by
  have := VG.Proof.CmacAes.Stream.AArch64.f_le c L; unfold VG.Proof.CmacAes.Stream.AArch64.restOf VG.Proof.CmacAes.Stream.AArch64.nbOf VG.Proof.CmacAes.Stream.AArch64.leftOf; split <;> omega

/-! ## Arithmetic on registers -/

theorem shr_ofNat {n k : Nat} (hn : n < 2 ^ 64) : BitVec.ofNat 64 n >>> k = BitVec.ofNat 64 (n / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (by have := Nat.div_le_self n (2 ^ k); omega)]

/-- The sign of `m - k`, for `m` and `k` of at most 16. -/
theorem lsr63 {m k : Nat} (hm : m ≤ 16) (hk : k ≤ 16) :
    (BitVec.ofNat 64 m - BitVec.ofNat 64 k) >>> 63 = BitVec.ofNat 64 (if m < k then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  split <;> simp only [BitVec.toNat_ofNat] <;> omega

/-- `16 nb` for the data left `x > 0`, as `sub 1; and 15; sub` computes it. -/
theorem nb16_bv {x : Nat} (hx : 0 < x) (hx' : x < 2 ^ 64) :
    BitVec.ofNat 64 x - BitVec.ofNat 64 1 - ((BitVec.ofNat 64 x - BitVec.ofNat 64 1) &&& 15) =
      BitVec.ofNat 64 (16 * ((x - 1) / 16)) := by
  apply BitVec.eq_of_toNat_eq
  have e : (BitVec.ofNat 64 x - BitVec.ofNat 64 1).toNat = x - 1 := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  rw [BitVec.toNat_sub, VG.Proof.CmacAes.Stream.AArch64.and15, e, BitVec.toNat_ofNat]
  omega

/-! ## Saving and restoring the registers -/

/-- The memory after saving the registers at `S + 2176`. -/
abbrev absSavedMem (s : State) (S : Addr) : Mem := Spill.saveMem s.mem S s.gpr saved

/-- Each slot holds the register saved there. -/
theorem absSaved_slot (s : State) (S : Addr) {r : Reg} {d : Nat} (h : (r, d) ∈ saved) :
    (VG.Proof.CmacAes.Stream.AArch64.absSavedMem s S).readW (S + BitVec.ofNat 64 d) 64 = s.gpr r :=
  Spill.saveMem_saved (l := saved) (by decide) s.mem S s.gpr (r, d) h

/-- Saving the registers changes only their slots. -/
theorem absSavedMem_frame (s : State) (S : Addr) :
    Frame [⟨S + BitVec.ofNat 64 2176, 56⟩] s.mem (VG.Proof.CmacAes.Stream.AArch64.absSavedMem s S) :=
  Spill.saveMem_frame (by decide) (by decide) _ _ _

theorem save_ok (s : State) {S : Addr} (hS : s.gpr .x5 = S)
    (hw : ∀ d, 2176 ≤ d → d + 8 ≤ 2232 → InRegions s.wr (S + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa save s = some s' ∧
      s'.gpr .x19 = s.gpr .x0 ∧ s'.gpr .x20 = s.gpr .x1 ∧ s'.gpr .x21 = s.gpr .x3 ∧
      s'.gpr .x22 = s.gpr .x4 ∧ s'.gpr .x23 = S ∧ s'.gpr .x2 = s.gpr .x2 ∧
      (∀ r, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x22 → r ≠ .x23 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = VG.Proof.CmacAes.Stream.AArch64.absSavedMem s S ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [← hS] at hw ⊢
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul, Nat.reduceMod, and_self, save, saved, mov, List.map, List.cons_append,
      List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.store, Size.bytes,
      Size.bits, State.read, gpr_write, Option.bind_some,
      hw 2176 (by decide) (by decide), hw 2184 (by decide) (by decide), hw 2192 (by decide) (by decide),
      hw 2200 (by decide) (by decide), hw 2208 (by decide) (by decide), hw 2216 (by decide) (by decide),
      hw 2224 (by decide) (by decide)]
    rfl, ?_⟩
  refine ⟨by simp [gpr_write], by simp [gpr_write], by simp [gpr_write], by simp [gpr_write],
    by simp [gpr_write], by simp [gpr_write], fun r h₁ h₂ h₃ h₄ h₅ => ?_, rfl, ?_, rfl, rfl⟩
  · simp [gpr_write, h₁, h₂, h₃, h₄, h₅]
  · simp only [mem_write, VG.Proof.CmacAes.Stream.AArch64.absSavedMem, saved, Spill.saveMem, Mem.writeW, BitVec.setWidth_eq]

theorem restore_ok (s : State) {B : Addr} (hb : s.gpr .x23 = B)
    (hr : ∀ d, 2176 ≤ d → d + 8 ≤ 2232 → InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa restore s = some s' ∧
      (∀ r d, (r, d) ∈ saved → s'.gpr r = s.mem.readW (B + BitVec.ofNat 64 d) 64) ∧
      (∀ r, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x22 → r ≠ .x24 → r ≠ .x30 → r ≠ .x23 →
        s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul, Nat.reduceMod, and_self, restore, saved, List.map, runBlock_cons, runStep_some,
      runBlock_nil, exec, addr, State.load, Size.bytes, Size.bits, gpr_write, mem_write, rd_write,
      wr_write, Option.bind_some, Option.map_some, hb,
      hr 2176 (by decide) (by decide), hr 2184 (by decide) (by decide), hr 2192 (by decide) (by decide),
      hr 2200 (by decide) (by decide), hr 2208 (by decide) (by decide), hr 2216 (by decide) (by decide),
      hr 2224 (by decide) (by decide)]
    rfl, ?_⟩
  refine ⟨fun r d h => ?_, fun r h₁ h₂ h₃ h₄ h₅ h₆ h₇ => ?_, rfl, rfl⟩
  · simp only [saved, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [gpr_write, Mem.readW]
  · simp [gpr_write, h₁, h₂, h₃, h₄, h₅, h₆, h₇]

/-! ## `held`: the bytes held back -/

theorem held_wp {s : State} {c : Nat} (hc : c < 2 ^ 64) (hd : s.gpr .x2 = BitVec.ofNat 64 c) :
    WP isa held s fun s' => s'.gpr .x9 = BitVec.ofNat 64 (held c) ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  by_cases h0 : c = 0
  · subst h0
    refine WP.ite true (by rw [VG.Proof.CmacAes.Stream.AArch64.eval_zero hc hd]; rfl) (fun _ => ?_) (fun h => by cases h)
    refine WP.of_runBlock ⟨_, by
      simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
        ite_true]
      rfl, ?_⟩
    exact ⟨by simp [gpr_write]; rfl, fun r h _ => by simp [gpr_write, h], rfl, rfl, rfl, rfl⟩
  · have hne : BitVec.ofNat 64 c ≠ 0 := fun e => h0 (by
      have := congrArg BitVec.toNat e; rwa [VG.Proof.CmacAes.Stream.AArch64.toNat_ofNat hc] at this)
    refine WP.ite false (by rw [VG.Proof.CmacAes.Stream.AArch64.eval_zero hc hd]; simp [h0]) (fun h => by cases h) fun _ => ?_
    refine WP.of_runBlock ⟨_, by
      simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
        State.read, gpr_write, ite_true, ite_false, BitVec.setWidth_eq]
      rfl, ?_⟩
    refine ⟨?_, fun r h₁ h₂ => by simp [gpr_write, h₁, h₂], rfl, rfl, rfl, rfl⟩
    simp only [gpr_write, ite_true, ite_false, BitVec.setWidth_eq, VG.Proof.CmacAes.Stream.AArch64.mz15, hd, reduceCtorEq]
    rw [VG.Proof.CmacAes.Stream.AArch64.held_bv _ hne, VG.Proof.CmacAes.Stream.AArch64.toNat_ofNat hc]

/-! ## `fill`: how many bytes to copy, and where -/

theorem clamp_wp {s : State} {L : Nat} (hL : L < 2 ^ 64) (h22 : s.gpr .x22 = BitVec.ofNat 64 L) :
    WP isa clamp s fun s' => s'.gpr .x10 = BitVec.ofNat 64 (min L 16) ∧
      (∀ r, r ≠ .x10 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, x10₁, g₁⟩ : ∃ s₁, runBlock isa [.lsr .x .x10 .x22 4] s = some s₁ ∧
      s₁.gpr .x10 = BitVec.ofNat 64 (L / 16) ∧ s₁ = s.write .x .x10 (BitVec.ofNat 64 (L / 16)) := by
    refine ⟨_, by
      simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
        State.read, ite_true, BitVec.setWidth_eq, h22, VG.Proof.CmacAes.Stream.AArch64.shr_ofNat hL], by simp [gpr_write], rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have ev := VG.Proof.CmacAes.Stream.AArch64.eval_zero (s := s₁) (x := L / 16) (by omega) x10₁
  subst g₁
  by_cases hl : L < 16
  · refine WP.ite true (by rw [ev]; simp; omega) (fun _ => ?_) (fun h => by cases h)
    refine WP.of_runBlock ⟨_, by
      simp (config := {decide := true}) only [mov, runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
        State.read, gpr_write, ite_true, ite_false, BitVec.setWidth_eq]
      rfl, ?_⟩
    refine ⟨?_, fun r h => by simp [gpr_write, h], rfl, rfl, rfl, rfl⟩
    simp only [gpr_write, ite_true, BitVec.setWidth_eq, BitVec.add_zero, h22, Nat.min_eq_left (Nat.le_of_lt hl)]
  · refine WP.ite false (by rw [ev]; simp; omega) (fun h => by cases h) fun _ => ?_
    refine WP.of_runBlock ⟨_, by
      simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
        ite_true]
      rfl, ?_⟩
    refine ⟨?_, fun r h => by simp [gpr_write, h], rfl, rfl, rfl, rfl⟩
    simp only [gpr_write, ite_true, BitVec.setWidth_eq, VG.Proof.CmacAes.Stream.AArch64.mz16, Nat.min_eq_right (Nat.le_of_not_lt hl)]

theorem fill_wp {s : State} {St D : Addr} {c L : Nat} (hL : L < 2 ^ 64)
    (h9 : s.gpr .x9 = BitVec.ofNat 64 (held c)) (h22 : s.gpr .x22 = BitVec.ofNat 64 L)
    (h19 : s.gpr .x19 = St) (h21 : s.gpr .x21 = D) :
    WP isa fill s fun s' => s'.gpr .x8 = BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.AArch64.fOf c L) ∧
      s'.gpr .x10 = BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.AArch64.fOf c L) ∧ s'.gpr .x6 = St + BitVec.ofNat 64 (288 + held c) ∧
      s'.gpr .x7 = D ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x10 → r ≠ .x11 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hh := held_le c
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.AArch64.clamp_wp hL h22) fun s₁ ⟨x10₁, g₁, sp₁, m₁, rd₁, wr₁⟩ => ?_)
  obtain ⟨s₂, run₂, x8₂, x10₂, x11₂, g₂, sp₂, m₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa [.movz .x .x8 16 0,
      .sub .x .x8 .x8 .x9, .sub .x .x11 .x10 .x8, .lsr .x .x11 .x11 63] s₁ = some s₂ ∧
      s₂.gpr .x8 = BitVec.ofNat 64 (16 - held c) ∧ s₂.gpr .x10 = BitVec.ofNat 64 (min L 16) ∧
      s₂.gpr .x11 = BitVec.ofNat 64 (if min L 16 < 16 - held c then 1 else 0) ∧
      (∀ r, r ≠ .x8 → r ≠ .x11 → s₂.gpr r = s₁.gpr r) ∧ s₂.sp = s₁.sp ∧ s₂.mem = s₁.mem ∧
      s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by
      simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
        State.read, gpr_write, ite_true, ite_false, BitVec.setWidth_eq]
      rfl, ?_⟩
    have x9₁ : s₁.gpr .x9 = BitVec.ofNat 64 (held c) := by rw [g₁ _ (by decide), h9]
    refine ⟨?_, ?_, ?_, fun r h₁ h₂ => by simp [gpr_write, h₁, h₂], rfl, rfl, rfl, rfl⟩
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, VG.Proof.CmacAes.Stream.AArch64.mz16, x9₁,
        Offset.ofNat_sub_ofNat hh]
    · simp only [gpr_write, ite_false, reduceCtorEq, x10₁]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, VG.Proof.CmacAes.Stream.AArch64.mz16, x9₁, x10₁,
        Offset.ofNat_sub_ofNat hh]
      exact VG.Proof.CmacAes.Stream.AArch64.lsr63 (by omega) (by omega)
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have hf : VG.Proof.CmacAes.Stream.AArch64.fOf c L = min (min L 16) (16 - held c) := by unfold VG.Proof.CmacAes.Stream.AArch64.fOf; omega
  refine WP.seq (WP.mono (Q := fun (s₃ : State) => s₃.gpr .x8 = BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.AArch64.fOf c L) ∧
    (∀ r, r ≠ .x8 → s₃.gpr r = s₂.gpr r) ∧ s₃.sp = s₂.sp ∧ s₃.mem = s₂.mem ∧ s₃.rd = s₂.rd ∧
      s₃.wr = s₂.wr) ?_ fun s₃ h₃ => ?_)
  · have ev := VG.Proof.CmacAes.Stream.AArch64.eval_zero (s := s₂) (x := if min L 16 < 16 - held c then 1 else 0) (by split <;> omega) x11₂
    by_cases hl : min L 16 < 16 - held c
    · refine WP.ite false (by rw [ev]; simp [hl]) (fun h => by cases h) fun _ => ?_
      refine WP.of_runBlock ⟨_, by
        simp (config := {decide := true}) only [mov, runBlock_cons, runStep_some, runBlock_nil, exec,
          Size.bits, State.read, ite_true, BitVec.setWidth_eq]
        rfl, ?_⟩
      refine ⟨?_, fun r h => by simp [gpr_write, h], rfl, rfl, rfl, rfl⟩
      simp only [gpr_write, ite_true, BitVec.setWidth_eq, BitVec.add_zero, x10₂, hf,
        Nat.min_eq_left (Nat.le_of_lt hl)]
    · refine WP.ite true (by rw [ev]; simp [hl]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      exact ⟨by rw [x8₂, hf, Nat.min_eq_right (Nat.le_of_not_lt hl)], fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨x8₃, g₃, sp₃, m₃, rd₃, wr₃⟩ := h₃
    have g (r : Reg) (a : r ≠ .x8) (b : r ≠ .x11) (d : r ≠ .x10) : s₃.gpr r = s.gpr r := by
      rw [g₃ r a, g₂ r a b, g₁ r d]
    refine WP.of_runBlock ⟨_, by
      simp (config := {decide := true}) only [mov, runBlock_cons, runStep_some, runBlock_nil, exec,
        Size.bits, State.read, gpr_write, ite_true, ite_false, BitVec.setWidth_eq]
      rfl, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, fun r a b d e f => ?_, by simp only [sp_write, sp₃, sp₂, sp₁],
      by simp only [mem_write, m₃, m₂, m₁], by simp only [rd_write, rd₃, rd₂, rd₁],
      by simp only [wr_write, wr₃, wr₂, wr₁]⟩
    · simp only [gpr_write, ite_false, reduceCtorEq, x8₃]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, BitVec.add_zero, x8₃]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq,
        g .x19 (by decide) (by decide) (by decide), g .x9 (by decide) (by decide) (by decide), h19, h9]
      rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_comm]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, BitVec.add_zero,
        g .x21 (by decide) (by decide) (by decide), h21]
    · simp only [gpr_write, a, b, e, ite_false]
      exact g r d f e

/-! ## `chain1`: the arguments of the first call -/

theorem chain1_wp {s : State} {St D S : Addr} {f L : Nat} (hf : f ≤ L) (hL : L < 2 ^ 64)
    (h21 : s.gpr .x21 = D) (h10 : s.gpr .x10 = BitVec.ofNat 64 f) (h22 : s.gpr .x22 = BitVec.ofNat 64 L)
    (h19 : s.gpr .x19 = St) (h23 : s.gpr .x23 = S) :
    WP isa chain1 s fun s' => s'.gpr .x21 = D + BitVec.ofNat 64 f ∧ s'.gpr .x22 = BitVec.ofNat 64 (L - f) ∧
      s'.gpr .x4 = BitVec.ofNat 64 (if L - f = 0 then 0 else 1) ∧ s'.gpr .x0 = St ∧
      s'.gpr .x1 = s.gpr .x20 ∧ s'.gpr .x2 = St + BitVec.ofNat 64 272 ∧
      s'.gpr .x3 = St + BitVec.ofNat 64 288 ∧ s'.gpr .x5 = S ∧
      (∀ r ∈ preserved, r ≠ .x21 → r ≠ .x22 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, x21₁, x22₁, x4₁, g₁, sp₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [.add .x .x21 .x21 .x10,
      .sub .x .x22 .x22 .x10, .movz .x .x4 0 0] s = some s₁ ∧
      s₁.gpr .x21 = D + BitVec.ofNat 64 f ∧ s₁.gpr .x22 = BitVec.ofNat 64 (L - f) ∧
      s₁.gpr .x4 = BitVec.ofNat 64 0 ∧
      (∀ r, r ≠ .x21 → r ≠ .x22 → r ≠ .x4 → s₁.gpr r = s.gpr r) ∧ s₁.sp = s.sp ∧ s₁.mem = s.mem ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by
      simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
        State.read, gpr_write, ite_true, ite_false, BitVec.setWidth_eq]
      rfl, ?_⟩
    refine ⟨?_, ?_, ?_, fun r a b c => by simp [gpr_write, a, b, c], rfl, rfl, rfl, rfl⟩
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, h21, h10]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, h22, h10,
        Offset.ofNat_sub_ofNat hf]
    · simp only [gpr_write, ite_true, BitVec.setWidth_eq, VG.Proof.CmacAes.Stream.AArch64.mz0]; rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (Q := fun (s₂ : State) => s₂.gpr .x4 = BitVec.ofNat 64 (if L - f = 0 then 0 else 1) ∧
    (∀ r, r ≠ .x4 → s₂.gpr r = s₁.gpr r) ∧ s₂.sp = s₁.sp ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧
      s₂.wr = s₁.wr) ?_ fun s₂ h₂ => ?_)
  · have ev := VG.Proof.CmacAes.Stream.AArch64.eval_zero (s := s₁) (x := L - f) (by omega) x22₁
    by_cases h0 : L - f = 0
    · refine WP.ite true (by rw [ev]; simp [h0]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      exact ⟨by rw [x4₁]; simp [h0], fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
    · refine WP.ite false (by rw [ev]; simp [h0]) (fun h => by cases h) fun _ => ?_
      refine WP.of_runBlock ⟨_, by
        simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
          ite_true]
        rfl, ?_⟩
      refine ⟨?_, fun r h => by simp [gpr_write, h], rfl, rfl, rfl, rfl⟩
      simp only [gpr_write, ite_true, BitVec.setWidth_eq, VG.Proof.CmacAes.Stream.AArch64.mz1, h0]; rfl
  · obtain ⟨x4₂, g₂, sp₂, m₂, rd₂, wr₂⟩ := h₂
    have g (r : Reg) (a : r ≠ .x21) (b : r ≠ .x22) (c : r ≠ .x4) : s₂.gpr r = s.gpr r := by
      rw [g₂ r c, g₁ r a b c]
    refine WP.of_runBlock ⟨_, by
      simp (config := {decide := true}) only [mov, runBlock_cons, runStep_some, runBlock_nil, exec,
        Size.bits, State.read, gpr_write, ite_true, ite_false, BitVec.setWidth_eq]
      rfl, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr a b => ?_, by simp only [sp_write, sp₂, sp₁],
      by simp only [mem_write, m₂, m₁], by simp only [rd_write, rd₂, rd₁], by simp only [wr_write, wr₂, wr₁]⟩
    · simp only [gpr_write, ite_false, reduceCtorEq, g₂ _ (by decide : Reg.x21 ≠ .x4), x21₁]
    · simp only [gpr_write, ite_false, reduceCtorEq, g₂ _ (by decide : Reg.x22 ≠ .x4), x22₁]
    · simp only [gpr_write, ite_false, reduceCtorEq, x4₂]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, BitVec.add_zero,
        g .x19 (by decide) (by decide) (by decide), h19]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, BitVec.add_zero,
        g .x20 (by decide) (by decide) (by decide)]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq,
        g .x19 (by decide) (by decide) (by decide), h19]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq,
        g .x19 (by decide) (by decide) (by decide), h19]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, BitVec.add_zero,
        g .x23 (by decide) (by decide) (by decide), h23]
    · have hc : ∀ r ∈ preserved, r ≠ .x0 ∧ r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x3 ∧ r ≠ .x4 ∧ r ≠ .x5 := by decide
      obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hc r hr
      simp only [gpr_write, n0, n1, n2, n3, n5, ite_false]
      exact g r a b n4

/-! ## `chain2`: the arguments of the second call -/

theorem chain2_wp {s : State} {x : Nat} (hx : x < 2 ^ 64) (h22 : s.gpr .x22 = BitVec.ofNat 64 x) :
    WP isa chain2 s fun s' =>
      s'.gpr .x24 = BitVec.ofNat 64 (16 * (if x = 0 then 0 else (x - 1) / 16)) ∧
      s'.gpr .x4 = BitVec.ofNat 64 (if x = 0 then 0 else (x - 1) / 16) ∧ s'.gpr .x0 = s.gpr .x19 ∧
      s'.gpr .x1 = s.gpr .x20 ∧ s'.gpr .x2 = s.gpr .x19 + BitVec.ofNat 64 272 ∧
      s'.gpr .x3 = s.gpr .x21 ∧ s'.gpr .x5 = s.gpr .x23 ∧
      (∀ r ∈ preserved, r ≠ .x24 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, x24₁, g₁⟩ : ∃ s₁, runBlock isa [.movz .x .x24 0 0] s = some s₁ ∧
      s₁.gpr .x24 = BitVec.ofNat 64 0 ∧ s₁ = s.write .x .x24 (BitVec.ofNat 64 0) := by
    refine ⟨_, by
      simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
        ite_true, VG.Proof.CmacAes.Stream.AArch64.mz0]
      rfl, by simp [gpr_write], rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  subst g₁
  refine WP.seq (WP.mono (Q := fun (s₂ : State) =>
    s₂.gpr .x24 = BitVec.ofNat 64 (16 * (if x = 0 then 0 else (x - 1) / 16)) ∧
    (∀ r, r ≠ .x24 → r ≠ .x9 → s₂.gpr r = s.gpr r) ∧ s₂.sp = s.sp ∧ s₂.mem = s.mem ∧ s₂.rd = s.rd ∧
      s₂.wr = s.wr) ?_ fun s₂ h₂ => ?_)
  · have ev := VG.Proof.CmacAes.Stream.AArch64.eval_zero (s := s.write .x .x24 (BitVec.ofNat 64 0)) (r := .x22) (x := x) hx
      (by simp only [gpr_write, reduceCtorEq, ite_false, h22])
    by_cases h0 : x = 0
    · refine WP.ite true (by rw [ev]; simp [h0]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      exact ⟨by rw [x24₁]; simp [h0], fun r h _ => by simp [gpr_write, h], rfl, rfl, rfl, rfl⟩
    · refine WP.ite false (by rw [ev]; simp [h0]) (fun h => by cases h) fun _ => ?_
      refine WP.of_runBlock ⟨_, by
        simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
          State.read, gpr_write, ite_true, ite_false, BitVec.setWidth_eq]
        rfl, ?_⟩
      refine ⟨?_, fun r a b => by simp [gpr_write, a, b], rfl, rfl, rfl, rfl⟩
      simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, VG.Proof.CmacAes.Stream.AArch64.mz15, h22, h0]
      exact VG.Proof.CmacAes.Stream.AArch64.nb16_bv (by omega) hx
  · obtain ⟨x24₂, g₂, sp₂, m₂, rd₂, wr₂⟩ := h₂
    refine WP.of_runBlock ⟨_, by
      simp (config := {decide := true}) only [mov, runBlock_cons, runStep_some, runBlock_nil, exec,
        Size.bits, State.read, gpr_write, ite_true, ite_false, BitVec.setWidth_eq]
      rfl, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr a => ?_, by simp only [sp_write, sp₂],
      by simp only [mem_write, m₂], by simp only [rd_write, rd₂], by simp only [wr_write, wr₂]⟩
    · simp only [gpr_write, ite_false, reduceCtorEq, x24₂]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, x24₂]
      exact (VG.Proof.CmacAes.Stream.AArch64.shr_ofNat (by split <;> omega)).trans (by congr 1; omega)
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq,
        BitVec.add_zero, g₂ _ (by decide : Reg.x19 ≠ .x24) (by decide)]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq,
        BitVec.add_zero, g₂ _ (by decide : Reg.x20 ≠ .x24) (by decide)]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq,
        g₂ _ (by decide : Reg.x19 ≠ .x24) (by decide)]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq,
        BitVec.add_zero, g₂ _ (by decide : Reg.x21 ≠ .x24) (by decide)]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq,
        BitVec.add_zero, g₂ _ (by decide : Reg.x23 ≠ .x24) (by decide)]
    · have hc : ∀ r ∈ preserved, r ≠ .x0 ∧ r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x3 ∧ r ≠ .x4 ∧ r ≠ .x5 ∧ r ≠ .x9 := by
        decide
      obtain ⟨n0, n1, n2, n3, n4, n5, n9⟩ := hc r hr
      simp only [gpr_write, n0, n1, n2, n3, n4, n5, ite_false]
      exact g₂ r a n9

/-! ## `rest`: the arguments of the last copy -/

theorem rest_ok {s : State} {D : Addr} {a x n : Nat} (hn : 16 * n ≤ x)
    (h21 : s.gpr .x21 = D + BitVec.ofNat 64 a) (h24 : s.gpr .x24 = BitVec.ofNat 64 (16 * n))
    (h22 : s.gpr .x22 = BitVec.ofNat 64 x) :
    ∃ s', runBlock isa rest s = some s' ∧ s'.gpr .x21 = D + BitVec.ofNat 64 (a + 16 * n) ∧
      s'.gpr .x22 = BitVec.ofNat 64 (x - 16 * n) ∧ s'.gpr .x6 = s.gpr .x19 + BitVec.ofNat 64 288 ∧
      s'.gpr .x7 = D + BitVec.ofNat 64 (a + 16 * n) ∧ s'.gpr .x8 = BitVec.ofNat 64 (x - 16 * n) ∧
      (∀ r ∈ preserved, r ≠ .x21 → r ≠ .x22 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, rest, mov, runBlock_cons, runStep_some, runBlock_nil, exec,
      Size.bits, State.read, gpr_write, BitVec.setWidth_eq]
    rfl, ?_⟩
  have e : D + BitVec.ofNat 64 a + BitVec.ofNat 64 (16 * n) = D + BitVec.ofNat 64 (a + 16 * n) :=
    Offset.add_add _ _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, fun r hr a b => ?_, rfl, rfl, rfl, rfl⟩
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, h21, h24, e]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, h22, h24,
      Offset.ofNat_sub_ofNat hn]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, BitVec.add_zero, h21, h24, e]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, BitVec.add_zero, h22, h24,
      Offset.ofNat_sub_ofNat hn]
  · have hc : ∀ r ∈ preserved, r ≠ .x6 ∧ r ≠ .x7 ∧ r ≠ .x8 := by decide
    obtain ⟨n6, n7, n8⟩ := hc r hr
    simp only [gpr_write, a, b, n6, n7, n8, ite_false]

end VG.Proof.CmacAes.Stream.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.Stream.AArch64.AbsorbCorrect`. -/
section

section

/-!
# Streaming AES-CMAC on AArch64: `vg_cmac_aes_absorb` up to the first call

The code saves the registers, computes the bytes held back `h`, copies `f =
min(len, 16 - h)` bytes after them, and sets up the first call of
`vg_cmac_aes_update`, which chains the block held back if data is left
(`AMid₁`).
-/

namespace VG.Proof.CmacAes.Stream.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.CmacAes.Stream.AArch64 VG.WriteBytes
open VG.Proof.Cmac.Stream (held held_le)

/-- The precondition, by name: the state `St`, the `L` bytes of data at `D`,
the scratch buffer `S` and the rounds `R`. -/
structure APre (s₀ : State) (St D S : Addr) (L R : Nat) : Prop where
  x0 : s₀.gpr .x0 = St
  x3 : s₀.gpr .x3 = D
  x4 : (s₀.gpr .x4).toNat = L
  x5 : s₀.gpr .x5 = S
  x1 : (s₀.gpr .x1).toNat = R
  rd : s₀.rd = [⟨D, L⟩]
  wr : s₀.wr = [⟨St, 304⟩, ⟨S, 2304⟩]
  st_d : (⟨St, 304⟩ : Region).Disjoint ⟨D, L⟩
  st_s : (⟨St, 304⟩ : Region).Disjoint ⟨S, 2304⟩
  d_s : (⟨D, L⟩ : Region).Disjoint ⟨S, 2304⟩
  wSt : St.toNat + 304 ≤ 2 ^ 64
  wD : D.toNat + L ≤ 2 ^ 64
  wS : S.toNat + 2304 ≤ 2 ^ 64
  rounds : R = 10 ∨ R = 12 ∨ R = 14

theorem APre.of {s₀ : State} (h : absorbAArch64.pre s₀) :
    VG.Proof.CmacAes.Stream.AArch64.APre s₀ (s₀.gpr .x0) (s₀.gpr .x3) (s₀.gpr .x5) (s₀.gpr .x4).toNat (s₀.gpr .x1).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i⟩ := h
  ⟨rfl, rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i⟩

section
variable {s₀ : State} {St D S : Addr} {L R : Nat} (hp : VG.Proof.CmacAes.Stream.AArch64.APre s₀ St D S L R)
include hp

theorem APre.lt : L < 2 ^ 64 := by rw [← hp.x4]; exact BitVec.isLt _

theorem APre.x4' : s₀.gpr .x4 = BitVec.ofNat 64 L := VG.Proof.CmacAes.Stream.AArch64.ofNat_toNat_eq hp.x4

theorem APre.x1' : s₀.gpr .x1 = BitVec.ofNat 64 R := VG.Proof.CmacAes.Stream.AArch64.ofNat_toNat_eq hp.x1

theorem APre.inSt {d n : Nat} (h : d + n ≤ 304) : InRegions s₀.wr (St + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact ⟨⟨St, 304⟩, by simp, Offset.contains_base _ h (by have := hp.wSt; omega)⟩

theorem APre.inS {d n : Nat} (h : d + n ≤ 2304) : InRegions s₀.wr (S + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact ⟨⟨S, 2304⟩, by simp, Offset.contains_base _ h (by have := hp.wS; omega)⟩

theorem APre.inD {d n : Nat} (h : d + n ≤ L) : InRegions (s₀.rd ++ s₀.wr) (D + BitVec.ofNat 64 d) n := by
  rw [hp.rd]; exact ⟨⟨D, L⟩, by simp, Offset.contains_base _ h (by have := hp.lt; omega)⟩

/-- The arguments of a call of `vg_cmac_aes_update` on `n` blocks at `Dd`,
from a state with the permissions of `s₀`. -/
theorem APre.uargs {s : State} {Dd : Addr} {n : Nat} (hx0 : s.gpr .x0 = St)
    (hx1 : s.gpr .x1 = s₀.gpr .x1) (hx2 : s.gpr .x2 = St + BitVec.ofNat 64 272) (hx3 : s.gpr .x3 = Dd)
    (hx4 : s.gpr .x4 = BitVec.ofNat 64 n) (hx5 : s.gpr .x5 = S)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hn : 16 * n < 2 ^ 64)
    (hdc : (⟨Dd, 16 * n⟩ : Region).Disjoint ⟨St + BitVec.ofNat 64 272, 16⟩)
    (hds : (⟨Dd, 16 * n⟩ : Region).Disjoint ⟨S, 2176⟩) (hwrap : Dd.toNat + 16 * n ≤ 2 ^ 64)
    (hcov : ∃ r' ∈ ([⟨D, L⟩, ⟨St, 304⟩, ⟨S, 2304⟩] : List Region), ∃ off, Dd = r'.base + BitVec.ofNat 64 off ∧
      off + 16 * n ≤ r'.len) :
    VG.Proof.CmacAes.Stream.AArch64.UArgs s St (St + BitVec.ofNat 64 272) Dd S R n := by
  have hw := hp.wSt
  have c272 : Region.Sub ⟨St + BitVec.ofNat 64 272, 16⟩ ⟨St, 304⟩ := Offset.sub_base St (by decide)
  exact
  { x0 := hx0, x2 := hx2, x3 := hx3, x4 := hx4, x5 := hx5, rounds := hp.rounds, hn := hn
    x1 := by rw [hx1]; exact hp.x1'
    wc := Offset.base_disjoint St (by decide) (by omega)
    ws := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    dc := hdc, ds := hds
    cs := (hp.st_s.sub_left c272).sub_right (Region.sub_prefix (by decide))
    wrapC := by rw [VG.Proof.CmacAes.Stream.AArch64.toNat_add_lt St hw (by decide)]; omega
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
  writeBytes (VG.Proof.CmacAes.Stream.AArch64.absSavedMem s₀ S) (St + BitVec.ofNat 64 (288 + held c))
    (Spec.Aes.bytesAt (VG.Proof.CmacAes.Stream.AArch64.absSavedMem s₀ S) D (VG.Proof.CmacAes.Stream.AArch64.fOf c L))

/-- What the code before the first call leaves. -/
structure AMid₁ (s₀ : State) (St D S : Addr) (L R : Nat) (s : State) : Prop where
  args : VG.Proof.CmacAes.Stream.AArch64.UArgs s St (St + BitVec.ofNat 64 272) (St + BitVec.ofNat 64 288) S R (VG.Proof.CmacAes.Stream.AArch64.b1Of (s₀.gpr .x2).toNat L)
  x19 : s.gpr .x19 = St
  x20 : s.gpr .x20 = s₀.gpr .x1
  x21 : s.gpr .x21 = D + BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.AArch64.fOf (s₀.gpr .x2).toNat L)
  x22 : s.gpr .x22 = BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.AArch64.leftOf (s₀.gpr .x2).toNat L)
  x23 : s.gpr .x23 = S
  other : ∀ r ∈ preserved, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x22 → r ≠ .x23 → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  mem : s.mem = VG.Proof.CmacAes.Stream.AArch64.m4 s₀ St D S (s₀.gpr .x2).toNat L
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem absorbPre_wp {s₀ : State} {St D S : Addr} {L R : Nat} (hp : VG.Proof.CmacAes.Stream.AArch64.APre s₀ St D S L R) :
    WP isa absorbPre s₀ (VG.Proof.CmacAes.Stream.AArch64.AMid₁ s₀ St D S L R) := by
  generalize hc : (s₀.gpr .x2).toNat = c
  have hcl : c < 2 ^ 64 := by rw [← hc]; exact BitVec.isLt _
  have hdx : s₀.gpr .x2 = BitVec.ofNat 64 c := VG.Proof.CmacAes.Stream.AArch64.ofNat_toNat_eq hc
  have hL := hp.lt
  have hw := hp.wSt
  have ⟨hfL, hfh⟩ := VG.Proof.CmacAes.Stream.AArch64.f_le c L
  have hh := held_le c
  obtain ⟨s₁, run₁, x19₁, x20₁, x21₁, x22₁, x23₁, x2₁, g₁, sp₁, m₁, rd₁, wr₁⟩ :=
    VG.Proof.CmacAes.Stream.AArch64.save_ok s₀ hp.x5 fun d _ h => hp.inS (by omega)
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.AArch64.held_wp hcl (by rw [x2₁, hdx])) fun s₂ ⟨x9₂, g₂, sp₂, m₂, rd₂, wr₂⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.AArch64.fill_wp (St := St) (D := D) hL x9₂ (by rw [g₂ _ (by decide) (by decide), x22₁, hp.x4'])
    (by rw [g₂ _ (by decide) (by decide), x19₁, hp.x0]) (by rw [g₂ _ (by decide) (by decide), x21₁, hp.x3]))
    fun s₃ ⟨x8₃, x10₃, x6₃, x7₃, g₃, sp₃, m₃, rd₃, wr₃⟩ => ?_)
  have dCp : Region.Sub ⟨St + BitVec.ofNat 64 (288 + held c), VG.Proof.CmacAes.Stream.AArch64.fOf c L⟩ ⟨St, 304⟩ := Offset.sub_base St (by omega)
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.AArch64.copy_ok s₃ (P := D) (C := St + BitVec.ofNat 64 (288 + held c)) (L := VG.Proof.CmacAes.Stream.AArch64.fOf c L)
    (by omega) x7₃ x6₃ x8₃
    (fun i hi => by rw [rd₃, wr₃, rd₂, wr₂, rd₁, wr₁]; exact hp.inD (by omega))
    (fun i hi => by rw [wr₃, wr₂, wr₁, Offset.add_add]; exact hp.inSt (by omega))
    ((hp.st_d.sub_left dCp).symm.sub_left (Region.sub_prefix hfL))) fun s₄ h₄ => ?_)
  -- The registers `chain1` reads, unchanged since `save`.
  have g (r : Reg) (a : r ≠ .x6) (b : r ≠ .x7) (c : r ≠ .x8) (d : r ≠ .x9) (e : r ≠ .x10) (f : r ≠ .x11) :
      s₄.gpr r = s₁.gpr r := by
    rw [h₄.other r a b c d, g₃ r a b c e f, g₂ r d e]
  refine WP.mono (VG.Proof.CmacAes.Stream.AArch64.chain1_wp (St := St) (S := S) hfL hL
    (by rw [g .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), x21₁, hp.x3])
    (by rw [h₄.other _ (by decide) (by decide) (by decide) (by decide), x10₃])
    (by rw [g .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), x22₁, hp.x4'])
    (by rw [g .x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), x19₁, hp.x0])
    (by rw [g .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), x23₁]))
    fun s₅ h₅ => ?_
  obtain ⟨x21₅, x22₅, x4₅, x0₅, x1₅, x2₅, x3₅, x5₅, sv₅, sp₅, m₅, rd₅, wr₅⟩ := h₅
  have k (r : Reg) (hr : r ∈ preserved) (a : r ≠ .x21) (b : r ≠ .x22) : s₅.gpr r = s₁.gpr r := by
    have hcc : ∀ r ∈ preserved, r ≠ .x6 ∧ r ≠ .x7 ∧ r ≠ .x8 ∧ r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x11 := by decide
    have hc := hcc r hr
    rw [sv₅ r hr a b, g r hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2]
  have hrd : s₅.rd = s₀.rd := by rw [rd₅, h₄.rd, rd₃, rd₂, rd₁]
  have hwr : s₅.wr = s₀.wr := by rw [wr₅, h₄.wr, wr₃, wr₂, wr₁]
  have hb1 : 16 * VG.Proof.CmacAes.Stream.AArch64.b1Of c L ≤ 16 := by unfold VG.Proof.CmacAes.Stream.AArch64.b1Of; split <;> omega
  have c288 : Region.Sub ⟨St + BitVec.ofNat 64 288, 16 * VG.Proof.CmacAes.Stream.AArch64.b1Of c L⟩ ⟨St, 304⟩ := Offset.sub_base St (by omega)
  have m₀ : s₅.mem = VG.Proof.CmacAes.Stream.AArch64.m4 s₀ St D S c L := by rw [m₅, h₄.mem, m₃, m₂, m₁, VG.Proof.CmacAes.Stream.AArch64.m4]
  subst hc
  refine ⟨hp.uargs x0₅
      (by rw [x1₅, g .x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), x20₁]) x2₅ x3₅
      (by rw [x4₅, VG.Proof.CmacAes.Stream.AArch64.b1Of, VG.Proof.CmacAes.Stream.AArch64.leftOf]) x5₅ hrd hwr (by omega)
      (Offset.disjoint St (by omega) (by omega) (by omega))
      ((hp.st_s.sub_left c288).sub_right (Region.sub_prefix (by decide)))
      (by rw [VG.Proof.CmacAes.Stream.AArch64.toNat_add_lt St hw (by decide)]; omega)
      ⟨⟨St, 304⟩, by simp, 288, rfl, by simp; omega⟩,
    by rw [k .x19 (by simp [preserved]) (by decide) (by decide), x19₁, hp.x0],
    by rw [k .x20 (by simp [preserved]) (by decide) (by decide), x20₁],
    x21₅, by rw [x22₅]; rfl, by rw [k .x23 (by simp [preserved]) (by decide) (by decide), x23₁],
    fun r hr a b c d e => by rw [k r hr c d, g₁ r a b c d e],
    by rw [sp₅, h₄.sp, sp₃, sp₂, sp₁], m₀, hrd, hwr⟩

end VG.Proof.CmacAes.Stream.AArch64

end

/-!
# Streaming AES-CMAC on AArch64: `vg_cmac_aes_absorb` is correct

After `absorbPre`, the first call chains the block held back if data is left
(`b1`), the second the whole blocks of the data left but its last 1 to 16
bytes (`nb`), and the last copy holds those back. If no data is left (`len ≤
16 - h`), the calls chain nothing and the copy copies nothing, and the data is
appended to the bytes held back (`repr_fill`); otherwise `repr_chain`.
-/

namespace VG.Proof.CmacAes.Stream.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.CmacAes.Stream.AArch64 VG.WriteBytes
open VG.Proof.Aes.AArch64 (Ctr32Impl)
open VG.Proof.Cmac (bytesAt_frame)
open VG.Proof.Cmac.Stream (held held_le)

theorem frame_at {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hp : p.toNat + n ≤ 2 ^ 64) {i : Nat} (hi : i < n) :
    m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i) :=
  hf _ fun r hr hc => hd r hr _ (Offset.contains_base p (by omega) (by omega)) hc

theorem blocksAt_zero (m : Mem) (p : Addr) : Spec.Cmac.blocksAt m p 16 0 = [] := rfl

theorem blocksAt_one (m : Mem) (p : Addr) :
    Spec.Cmac.blocksAt m p 16 1 = [Spec.Aes.bytesAt m p 16] := by
  simp [Spec.Cmac.blocksAt]

theorem absorb_wp (v : Proof.CmacAes.AArch64.UpdateImpl) {s₀ : State} (h0 : absorbAArch64.pre s₀) :
    WP isa (absorb v.callee) s₀ fun s' => GprAbi s₀ s' ∧ absorbAArch64.post s₀ s' := by
  have hp := APre.of h0
  generalize s₀.gpr .x0 = St at hp
  generalize s₀.gpr .x3 = D at hp
  generalize s₀.gpr .x5 = S at hp
  generalize (s₀.gpr .x4).toNat = L at hp
  generalize (s₀.gpr .x1).toNat = R at hp
  obtain ⟨c, hc⟩ : ∃ c, (s₀.gpr .x2).toNat = c := ⟨_, rfl⟩
  have hL := hp.lt
  have hw := hp.wSt
  have hsw := hp.wS
  have ⟨hfL, hfh⟩ := VG.Proof.CmacAes.Stream.AArch64.f_le c L
  have hsum := VG.Proof.CmacAes.Stream.AArch64.nb_le c L
  have hh := held_le c
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.AArch64.absorbPre_wp hp) fun s₅ h₅ => ?_)
  obtain ⟨args₅, x19₅, x20₅, x21₅, x22₅, x23₅, o₅, sp₅, m₅, rd₅, wr₅⟩ := h₅
  rw [hc] at args₅ x21₅ x22₅ m₅
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.AArch64.upd_call v _ args₅) fun s₆ h₆ => ?_)
  have k₆ (r : Reg) (hr : r ∈ preserved) (h30 : r ≠ .x30) : s₆.gpr r = s₅.gpr r := h₆.saved r hr h30
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.AArch64.chain2_wp (x := VG.Proof.CmacAes.Stream.AArch64.leftOf c L) (by unfold VG.Proof.CmacAes.Stream.AArch64.leftOf; omega)
    (by rw [k₆ .x22 (by simp [preserved]) (by decide), x22₅])) fun s₇ h₇ => ?_)
  obtain ⟨x24₇, x4₇, x0₇, x1₇, x2₇, x3₇, x5₇, sv₇, sp₇, m₇, rd₇, wr₇⟩ := h₇
  have hnb : (if VG.Proof.CmacAes.Stream.AArch64.leftOf c L = 0 then 0 else (VG.Proof.CmacAes.Stream.AArch64.leftOf c L - 1) / 16) = VG.Proof.CmacAes.Stream.AArch64.nbOf c L := rfl
  rw [hnb] at x24₇ x4₇
  have k₇ (r : Reg) (hr : r ∈ preserved) (a : r ≠ .x24) (h30 : r ≠ .x30) : s₇.gpr r = s₅.gpr r := by
    rw [sv₇ r hr a, k₆ r hr h30]
  have dD : Region.Sub ⟨D + BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.AArch64.fOf c L), 16 * VG.Proof.CmacAes.Stream.AArch64.nbOf c L⟩ ⟨D, L⟩ := Offset.sub_base D (by omega)
  have c272 : Region.Sub ⟨St + BitVec.ofNat 64 272, 16⟩ ⟨St, 304⟩ := Offset.sub_base St (by decide)
  have args₇ := hp.uargs (s := s₇) (Dd := D + BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.AArch64.fOf c L)) (n := VG.Proof.CmacAes.Stream.AArch64.nbOf c L)
    (by rw [x0₇, k₆ .x19 (by simp [preserved]) (by decide), x19₅])
    (by rw [x1₇, k₆ .x20 (by simp [preserved]) (by decide), x20₅])
    (by rw [x2₇, k₆ .x19 (by simp [preserved]) (by decide), x19₅])
    (by rw [x3₇, k₆ .x21 (by simp [preserved]) (by decide), x21₅]) x4₇
    (by rw [x5₇, k₆ .x23 (by simp [preserved]) (by decide), x23₅]) (by rw [rd₇, h₆.rd, rd₅])
    (by rw [wr₇, h₆.wr, wr₅]) (by omega) ((hp.st_d.sub_left c272).symm.sub_left dD)
    ((hp.d_s.sub_left dD).sub_right (Region.sub_prefix (by decide)))
    (by
      by_cases h0 : VG.Proof.CmacAes.Stream.AArch64.nbOf c L = 0
      · rw [h0]; have := (D + BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.AArch64.fOf c L)).isLt; omega
      · have := hp.wD; rw [VG.Proof.CmacAes.Stream.AArch64.toNat_add_lt D hp.wD (by omega)]; omega)
    ⟨⟨D, L⟩, by simp, VG.Proof.CmacAes.Stream.AArch64.fOf c L, rfl, by simp; omega⟩
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.AArch64.upd_call v _ args₇) fun s₈ h₈ => ?_)
  have k₈ (r : Reg) (hr : r ∈ preserved) (h30 : r ≠ .x30) : s₈.gpr r = s₇.gpr r := h₈.saved r hr h30
  obtain ⟨s₉, run₉, x21₉, x22₉, x6₉, x7₉, x8₉, sv₉, sp₉, m₉, rd₉, wr₉⟩ := VG.Proof.CmacAes.Stream.AArch64.rest_ok (s := s₈) (D := D)
    (a := VG.Proof.CmacAes.Stream.AArch64.fOf c L) (x := VG.Proof.CmacAes.Stream.AArch64.leftOf c L) (n := VG.Proof.CmacAes.Stream.AArch64.nbOf c L) (by unfold VG.Proof.CmacAes.Stream.AArch64.leftOf; omega)
    (by rw [k₈ .x21 (by simp [preserved]) (by decide), k₇ .x21 (by simp [preserved]) (by decide) (by decide),
      x21₅])
    (by rw [k₈ .x24 (by simp [preserved]) (by decide), x24₇])
    (by rw [k₈ .x22 (by simp [preserved]) (by decide), k₇ .x22 (by simp [preserved]) (by decide) (by decide),
      x22₅])
  refine WP.seq (WP.of_runBlock ⟨s₉, run₉, ?_⟩)
  have rd₉' : s₉.rd = s₀.rd := by rw [rd₉, h₈.rd, rd₇, h₆.rd, rd₅]
  have wr₉' : s₉.wr = s₀.wr := by rw [wr₉, h₈.wr, wr₇, h₆.wr, wr₅]
  have dR : Region.Sub ⟨D + BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.AArch64.fOf c L + 16 * VG.Proof.CmacAes.Stream.AArch64.nbOf c L), VG.Proof.CmacAes.Stream.AArch64.restOf c L⟩ ⟨D, L⟩ :=
    Offset.sub_base D (by omega)
  have hrr : VG.Proof.CmacAes.Stream.AArch64.restOf c L ≤ 16 := by unfold VG.Proof.CmacAes.Stream.AArch64.restOf VG.Proof.CmacAes.Stream.AArch64.nbOf VG.Proof.CmacAes.Stream.AArch64.leftOf; split <;> omega
  have sR : Region.Sub ⟨St + BitVec.ofNat 64 288, VG.Proof.CmacAes.Stream.AArch64.restOf c L⟩ ⟨St, 304⟩ := Offset.sub_base St (by omega)
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.AArch64.copy_ok s₉ (P := D + BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.AArch64.fOf c L + 16 * VG.Proof.CmacAes.Stream.AArch64.nbOf c L))
    (C := St + BitVec.ofNat 64 288) (L := VG.Proof.CmacAes.Stream.AArch64.restOf c L) (by omega) x7₉
    (by rw [x6₉, k₈ .x19 (by simp [preserved]) (by decide), k₇ .x19 (by simp [preserved]) (by decide) (by decide),
      x19₅]) x8₉
    (fun i hi => by rw [rd₉', wr₉', Offset.add_add]; exact hp.inD (by omega))
    (fun i hi => by rw [wr₉', Offset.add_add]; exact hp.inSt (by omega))
    ((hp.st_d.sub_left sR).symm.sub_left dR)) fun s₁₀ h₁₀ => ?_)
  have x23₁₀ : s₁₀.gpr .x23 = S := by
    rw [h₁₀.other _ (by decide) (by decide) (by decide) (by decide),
      sv₉ _ (by simp [preserved]) (by decide) (by decide),
      k₈ .x23 (by simp [preserved]) (by decide), k₇ .x23 (by simp [preserved]) (by decide) (by decide), x23₅]
  obtain ⟨s₁₁, run₁₁, slot₁₁, keep₁₁, sp₁₁, m₁₁⟩ := VG.Proof.CmacAes.Stream.AArch64.restore_ok s₁₀ x23₁₀
    (fun d _ h => by
      rw [h₁₀.rd, h₁₀.wr, rd₉', wr₉']
      obtain ⟨r, hr, hc⟩ := hp.inS (d := d) (n := 8) (by omega)
      exact ⟨r, List.mem_append_right _ hr, hc⟩)
  refine WP.of_runBlock ⟨s₁₁, run₁₁, ?_⟩
  -- The frames.
  have hlf : (Spec.Aes.bytesAt (VG.Proof.CmacAes.Stream.AArch64.absSavedMem s₀ S) D (VG.Proof.CmacAes.Stream.AArch64.fOf c L)).length = VG.Proof.CmacAes.Stream.AArch64.fOf c L := Proof.Cmac.bytesAt_length _ _ _
  have hlr : (Spec.Aes.bytesAt s₉.mem (D + BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.AArch64.fOf c L + 16 * VG.Proof.CmacAes.Stream.AArch64.nbOf c L)) (VG.Proof.CmacAes.Stream.AArch64.restOf c L)).length =
    VG.Proof.CmacAes.Stream.AArch64.restOf c L := Proof.Cmac.bytesAt_length _ _ _
  have fS : Frame [⟨S + BitVec.ofNat 64 2176, 56⟩] s₀.mem (VG.Proof.CmacAes.Stream.AArch64.absSavedMem s₀ S) := VG.Proof.CmacAes.Stream.AArch64.absSavedMem_frame _ _
  have fC1 : Frame [⟨St + BitVec.ofNat 64 (288 + held c), VG.Proof.CmacAes.Stream.AArch64.fOf c L⟩] (VG.Proof.CmacAes.Stream.AArch64.absSavedMem s₀ S) s₅.mem := by
    rw [m₅, VG.Proof.CmacAes.Stream.AArch64.m4]; exact writeBytes_frame _ _ _ (by rw [hlf]; exact Region.contains_self _ _)
  have f6 : Frame [⟨St + BitVec.ofNat 64 272, 16⟩, ⟨S, 2176⟩] s₅.mem s₆.mem := h₆.frame
  have f8 : Frame [⟨St + BitVec.ofNat 64 272, 16⟩, ⟨S, 2176⟩] s₆.mem s₈.mem := by
    rw [← m₇]; exact h₈.frame
  have fC2 : Frame [⟨St + BitVec.ofNat 64 288, VG.Proof.CmacAes.Stream.AArch64.restOf c L⟩] s₈.mem s₁₁.mem := by
    rw [m₁₁, h₁₀.mem, m₉]
    exact writeBytes_frame _ _ _ (by rw [← m₉, hlr]; exact Region.contains_self _ _)
  let K : List Region := [⟨S + BitVec.ofNat 64 2176, 56⟩, ⟨St + BitVec.ofNat 64 (288 + held c), VG.Proof.CmacAes.Stream.AArch64.fOf c L⟩,
    ⟨St + BitVec.ofNat 64 272, 16⟩, ⟨S, 2176⟩, ⟨St + BitVec.ofNat 64 288, VG.Proof.CmacAes.Stream.AArch64.restOf c L⟩]
  have F5 : Frame K s₀.mem s₅.mem := (fS.mono (by simp [K])).trans (fC1.mono (by simp [K]))
  have F6 : Frame K s₀.mem s₆.mem := F5.trans (f6.mono (by simp [K]))
  have F8 : Frame K s₀.mem s₈.mem := F6.trans (f8.mono (by simp [K]))
  have F11 : Frame K s₀.mem s₁₁.mem := F8.trans (fC2.mono (by simp [K]))
  -- The key and the data are in none of these.
  have dK : ∀ r ∈ K, (⟨St, 272⟩ : Region).Disjoint r := by
    intro r hr
    simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base S (by decide))
    · exact Offset.base_disjoint St (by omega) (by omega)
    · exact Offset.base_disjoint St (by omega) (by omega)
    · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    · exact Offset.base_disjoint St (by omega) (by omega)
  have dDat : ∀ r ∈ K, (⟨D, L⟩ : Region).Disjoint r := by
    intro r hr
    simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hp.d_s.sub_right (Offset.sub_base S (by decide))
    · exact hp.st_d.symm.sub_right (Offset.sub_base St (by omega))
    · exact hp.st_d.symm.sub_right (Offset.sub_base St (by decide))
    · exact hp.d_s.sub_right (Region.sub_prefix (by decide))
    · exact hp.st_d.symm.sub_right (Offset.sub_base St (by omega))
  have k0 : ∀ p : Addr, p + BitVec.ofNat 64 0 = p := fun p => BitVec.add_zero p
  refine ⟨⟨fun r hr => ?_, by rw [sp₁₁, h₁₀.sp, sp₉, h₈.sp, sp₇, h₆.sp, sp₅]⟩, ?_⟩
  · -- The registers, restored from their slots.
    have Fp : Frame K.tail (VG.Proof.CmacAes.Stream.AArch64.absSavedMem s₀ S) s₁₁.mem :=
      ((fC1.mono (by simp [K])).trans (f6.mono (by simp [K]))).trans
        ((f8.mono (by simp [K])).trans (fC2.mono (by simp [K])))
    have slot (d : Nat) (h₁ : 2176 ≤ d) (h₂ : d + 8 ≤ 2232) :
        s₁₀.mem.readW (S + BitVec.ofNat 64 d) 64 = (VG.Proof.CmacAes.Stream.AArch64.absSavedMem s₀ S).readW (S + BitVec.ofNat 64 d) 64 := by
      rw [← m₁₁]
      have sub : Region.Sub ⟨S + BitVec.ofNat 64 d, 8⟩ ⟨S, 2304⟩ := Offset.sub_base S (by omega)
      refine Fp.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [K, List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact (hp.st_s.sub_left (Offset.sub_base St (by omega))).symm.sub_left sub
      · exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).symm.sub_left sub
      · exact Offset.disjoint_base S (by omega) (by omega)
      · exact (hp.st_s.sub_left (Offset.sub_base St (by omega))).symm.sub_left sub
    have sl {r : Reg} {d : Nat} (h : (r, d) ∈ saved) : s₁₁.gpr r = s₀.gpr r := by
      have hd : 2176 ≤ d ∧ d + 8 ≤ 2232 := by
        simp only [saved, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
        omega
      rw [slot₁₁ r d h, slot d hd.1 hd.2, VG.Proof.CmacAes.Stream.AArch64.absSaved_slot s₀ S h]
    have hc' : ∀ r ∈ preserved, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x22 → r ≠ .x24 → r ≠ .x30 →
        r ≠ .x23 → r ≠ .x6 ∧ r ≠ .x7 ∧ r ≠ .x8 ∧ r ≠ .x9 := by decide
    have oth (r : Reg) (hr : r ∈ preserved) (a : r ≠ .x19) (b : r ≠ .x20) (c : r ≠ .x21) (d : r ≠ .x22)
        (e : r ≠ .x24) (f : r ≠ .x30) (g : r ≠ .x23) : s₁₁.gpr r = s₀.gpr r := by
      obtain ⟨n6, n7, n8, n9⟩ := hc' r hr a b c d e f g
      rw [keep₁₁ r a b c d e f g, h₁₀.other r n6 n7 n8 n9, sv₉ r hr c d, k₈ r hr f, k₇ r hr e f,
        o₅ r hr a b c d g]
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact sl (d := 2176) (by simp [saved])
    · exact sl (d := 2184) (by simp [saved])
    · exact sl (d := 2192) (by simp [saved])
    · exact sl (d := 2200) (by simp [saved])
    · exact sl (d := 2224) (by simp [saved])
    · exact sl (d := 2208) (by simp [saved])
    · exact oth _ (by simp [preserved]) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)
    · exact oth _ (by simp [preserved]) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)
    · exact oth _ (by simp [preserved]) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)
    · exact oth _ (by simp [preserved]) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)
    · exact sl (d := 2216) (by simp [saved])
  · intro key msg hr hR hcnt hlen
    rw [hp.x0] at hr ⊢
    rw [hp.x3, hp.x4]
    rw [hp.x4] at hlen
    have hcm : c = msg.length := by rw [← hc, hcnt, VG.Proof.CmacAes.Stream.AArch64.toNat_ofNat (by omega)]
    subst hcm
    have hRk : R = Spec.Aes.rounds (key.length / 4) := by rw [← hp.x1]; exact hR
    have hRb : 16 * (R + 1) ≤ 272 := by rcases hp.rounds with h | h | h <;> omega
    have hsch := ((Proof.Cmac.Stream.repr_iff _ _ _ _).mp hr).1.2.1
    rw [← hRk] at hsch
    have ciph : ∀ m : Mem, Frame K s₀.mem m →
        Spec.Cmac.aesWith R (Spec.Aes.bytesAt m St (16 * (R + 1))) = Spec.Cmac.aes key := fun m hf => by
      rw [bytesAt_frame hf (fun r hr => (dK r hr).sub_left (Region.sub_prefix hRb)) (by omega), hsch,
        Spec.Cmac.aes, ← hRk]
    -- The data, wherever it is read.
    have dat : ∀ m : Mem, Frame K s₀.mem m → ∀ a b : Nat, a + b ≤ L →
        Spec.Aes.bytesAt m (D + BitVec.ofNat 64 a) b =
          ((Spec.Aes.bytesAt s₀.mem D L).drop a).take b := fun m hf a b hab => by
      rw [Proof.Cmac.Stream.bytesAt_offset m D hab, bytesAt_frame hf dDat (by omega)]
    have fS' : Frame K s₀.mem (VG.Proof.CmacAes.Stream.AArch64.absSavedMem s₀ S) := fS.mono (by simp [K])
    -- The chaining value.
    have cv5 : Spec.Aes.bytesAt s₅.mem (St + BitVec.ofNat 64 272) 16 =
        Spec.Aes.bytesAt s₀.mem (St + BitVec.ofNat 64 272) 16 := by
      rw [bytesAt_frame fC1 (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint St (by omega) (by omega) (by omega))
          (by decide),
        bytesAt_frame fS (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).sub_right (Offset.sub_base S (by decide)))
          (by decide)]
    have cv11 : Spec.Aes.bytesAt s₁₁.mem (St + BitVec.ofNat 64 272) 16 =
        Spec.Aes.bytesAt s₈.mem (St + BitVec.ofNat 64 272) 16 :=
      bytesAt_frame fC2 (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint St (by omega) (by omega) (by omega))
        (by decide)
    have out6 := h₆.out
    rw [ciph _ F5] at out6
    have out8 := h₈.out
    rw [m₇, ciph _ F6] at out8
    have hk : ∀ i < 272, s₁₁.mem (St + BitVec.ofNat 64 i) = s₀.mem (St + BitVec.ofNat 64 i) :=
      fun i hi => VG.Proof.CmacAes.Stream.AArch64.frame_at F11 dK (by omega) hi
    have hdl : (Spec.Aes.bytesAt s₀.mem D L).length = L := Proof.Cmac.bytesAt_length _ _ _
    -- The bytes held back so far, and the first `f` bytes of data after them.
    have hb5 : Spec.Aes.bytesAt s₅.mem (St + BitVec.ofNat 64 288) (held msg.length + VG.Proof.CmacAes.Stream.AArch64.fOf msg.length L) =
        Spec.Aes.bytesAt s₀.mem (St + BitVec.ofNat 64 288) (held msg.length) ++
          (Spec.Aes.bytesAt s₀.mem D L).take (VG.Proof.CmacAes.Stream.AArch64.fOf msg.length L) := by
      have e := VG.Proof.CmacAes.Stream.AArch64.bytesAt_writeBytes (VG.Proof.CmacAes.Stream.AArch64.absSavedMem s₀ S) (St + BitVec.ofNat 64 288) (held msg.length)
        (Spec.Aes.bytesAt (VG.Proof.CmacAes.Stream.AArch64.absSavedMem s₀ S) D (VG.Proof.CmacAes.Stream.AArch64.fOf msg.length L)) (by rw [hlf]; omega)
      rw [hlf] at e
      rw [m₅, VG.Proof.CmacAes.Stream.AArch64.m4, ← Offset.add_add, e,
        bytesAt_frame fS (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hp.st_s.sub_left (Offset.sub_base St (by omega))).sub_right (Offset.sub_base S (by decide)))
          (by omega)]
      refine congrArg (_ ++ ·) ?_
      have := dat _ fS' 0 (VG.Proof.CmacAes.Stream.AArch64.fOf msg.length L) (by omega)
      rwa [k0, List.drop_zero] at this
    generalize hd : Spec.Aes.bytesAt s₀.mem D L = d at hdl hb5 dat ⊢
    by_cases hx : VG.Proof.CmacAes.Stream.AArch64.leftOf msg.length L = 0
    · -- Everything fits in the block held back.
      have hfL' : VG.Proof.CmacAes.Stream.AArch64.fOf msg.length L = L := by unfold VG.Proof.CmacAes.Stream.AArch64.leftOf at hx; omega
      have hb : VG.Proof.CmacAes.Stream.AArch64.b1Of msg.length L = 0 := by simp [VG.Proof.CmacAes.Stream.AArch64.b1Of, hx]
      have hn : VG.Proof.CmacAes.Stream.AArch64.nbOf msg.length L = 0 := by simp [VG.Proof.CmacAes.Stream.AArch64.nbOf, hx]
      have hr0 : VG.Proof.CmacAes.Stream.AArch64.restOf msg.length L = 0 := by simp [VG.Proof.CmacAes.Stream.AArch64.restOf, hn, hx]
      have m118 : s₁₁.mem = s₈.mem := by
        rw [m₁₁, h₁₀.mem, m₉, hr0, show Spec.Aes.bytesAt s₈.mem
          (D + BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.AArch64.fOf msg.length L + 16 * VG.Proof.CmacAes.Stream.AArch64.nbOf msg.length L)) 0 = [] from rfl, writeBytes_nil]
      refine Proof.Cmac.Stream.repr_fill hr hk (by rw [hdl]; have := (VG.Proof.CmacAes.Stream.AArch64.f_le msg.length L).2; omega) ?_ ?_
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 272) _ = Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 272) _
        rw [cv11, out8, hn, VG.Proof.CmacAes.Stream.AArch64.blocksAt_zero, out6, hb, VG.Proof.CmacAes.Stream.AArch64.blocksAt_zero]
        exact cv5
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 288) _ = Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 288) _ ++ _
        have sub : Region.Sub ⟨St + BitVec.ofNat 64 288, held msg.length + L⟩ ⟨St, 304⟩ :=
          Offset.sub_base St (by omega)
        have dj : ∀ r ∈ [⟨St + BitVec.ofNat 64 272, 16⟩, ⟨S, 2176⟩],
            (⟨St + BitVec.ofNat 64 288, held msg.length + L⟩ : Region).Disjoint r := by
          intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact Offset.disjoint St (by omega) (by omega) (by omega)
          · exact (hp.st_s.sub_left sub).sub_right (Region.sub_prefix (by decide))
        have hb5' := hb5
        rw [hfL', List.take_of_length_le (by rw [hdl])] at hb5'
        rw [m118, hdl, bytesAt_frame f8 dj (by omega), bytesAt_frame f6 dj (by omega), hb5']
    · -- The block held back is complete, and more blocks may follow.
      have hlt : 16 - held msg.length < L := by unfold VG.Proof.CmacAes.Stream.AArch64.leftOf VG.Proof.CmacAes.Stream.AArch64.fOf at hx; omega
      have hf' : VG.Proof.CmacAes.Stream.AArch64.fOf msg.length L = 16 - held msg.length := by unfold VG.Proof.CmacAes.Stream.AArch64.fOf; omega
      have hb : VG.Proof.CmacAes.Stream.AArch64.b1Of msg.length L = 1 := by simp [VG.Proof.CmacAes.Stream.AArch64.b1Of, hx]
      have hn : VG.Proof.CmacAes.Stream.AArch64.nbOf msg.length L = Proof.Cmac.Stream.nblocks msg.length L := by
        simp only [VG.Proof.CmacAes.Stream.AArch64.nbOf, hx, ↓reduceIte]
        unfold VG.Proof.CmacAes.Stream.AArch64.leftOf Proof.Cmac.Stream.nblocks
        rw [hf']
      have hb5' := hb5
      rw [hf', Nat.add_sub_cancel' hh] at hb5'
      refine Proof.Cmac.Stream.repr_chain hr hk (by rw [hdl]; exact hlt) ?_ ?_
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 272) _ =
          Spec.Cmac.chain _ (Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 272) _)
            ([Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 288) _ ++ _] ++ _)
        rw [cv11, out8, out6, hb, VG.Proof.CmacAes.Stream.AArch64.blocksAt_one, cv5, Proof.Cmac.chain_append, Proof.Cmac.Stream.blocksAt_eq,
          dat _ F6 _ _ (by omega), hb5', hdl, hf', hn]
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 288) _ = _
        have e := VG.Proof.CmacAes.Stream.AArch64.bytesAt_writeBytes_self s₈.mem (St + BitVec.ofNat 64 288)
          (xs := Spec.Aes.bytesAt s₈.mem (D + BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.AArch64.fOf msg.length L + 16 * VG.Proof.CmacAes.Stream.AArch64.nbOf msg.length L))
            (VG.Proof.CmacAes.Stream.AArch64.restOf msg.length L)) (by rw [Proof.Cmac.bytesAt_length]; omega)
        rw [Proof.Cmac.bytesAt_length] at e
        have hr' : d.length - (16 - held msg.length) - 16 * Proof.Cmac.Stream.nblocks msg.length d.length =
            VG.Proof.CmacAes.Stream.AArch64.restOf msg.length L := by
          rw [hdl, ← hn, ← hf']; rfl
        rw [hr', m₁₁, h₁₀.mem, m₉, e, dat _ F8 _ _ (by omega),
          List.take_of_length_le (by simp only [List.length_drop, hdl]; unfold VG.Proof.CmacAes.Stream.AArch64.restOf VG.Proof.CmacAes.Stream.AArch64.leftOf; omega),
          List.drop_drop, hdl, ← hn, hf']

end VG.Proof.CmacAes.Stream.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.Stream.AArch64.Finish`. -/
section

/-!
# Streaming AES-CMAC on AArch64: `vg_cmac_aes_finish`

The code copies the chaining value to `out`, saves `x19` and `x30` in the
scratch buffer, computes the number of bytes held back, and calls
`vg_cmac_aes_finalize` with the state as its key and `out` as its state: its
result is the MAC of the message the state represents (`repr_finish`). The
code before the call and the restore after it are constant time by the taint
analysis, and the call by its own proof (`fin_rel`), its arguments pinned by
`HMid`.
-/

namespace VG.Proof.CmacAes.Stream.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.CmacAes.Stream.AArch64
open VG.Impl.CmacAes.AArch64 (mov)
open VG.Proof.CmacAes.AArch64 (k0 readW_writeW_other agree_of)
open VG.Proof.Aes.AArch64 (Ctr32Impl)
open VG.Proof.Cmac.Stream (held held_le)

/-- The precondition, by name: the state `St`, `out` (`O`), the scratch
buffer `S` and the rounds `R`. -/
structure HPre (s₀ : State) (St O S : Addr) (R : Nat) : Prop where
  x0 : s₀.gpr .x0 = St
  x3 : s₀.gpr .x3 = O
  x4 : s₀.gpr .x4 = S
  x1 : (s₀.gpr .x1).toNat = R
  rd : s₀.rd = []
  wr : s₀.wr = [⟨St, 304⟩, ⟨O, 16⟩, ⟨S, 2304⟩]
  st_o : (⟨St, 304⟩ : Region).Disjoint ⟨O, 16⟩
  st_s : (⟨St, 304⟩ : Region).Disjoint ⟨S, 2304⟩
  o_s : (⟨O, 16⟩ : Region).Disjoint ⟨S, 2304⟩
  wSt : St.toNat + 304 ≤ 2 ^ 64
  wO : O.toNat + 16 ≤ 2 ^ 64
  wS : S.toNat + 2304 ≤ 2 ^ 64
  rounds : R = 10 ∨ R = 12 ∨ R = 14

theorem HPre.of {s₀ : State} (h : finishAArch64.pre s₀) :
    VG.Proof.CmacAes.Stream.AArch64.HPre s₀ (s₀.gpr .x0) (s₀.gpr .x3) (s₀.gpr .x4) (s₀.gpr .x1).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i⟩ := h
  ⟨rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i⟩

/-! ## Before the call -/

/-- The memory after copying the block at `p` to `o`, a word at a time. -/
def copyMem (m : Mem) (o p : Addr) : Mem :=
  let m₁ := m.writeW o (m.readW p 64)
  m₁.writeW (o + BitVec.ofNat 64 8) (m₁.readW (p + BitVec.ofNat 64 8) 64)

theorem copyMem_frame (m : Mem) (o p : Addr) : Frame [⟨o, 16⟩] m (VG.Proof.CmacAes.Stream.AArch64.copyMem m o p) :=
  Proof.Cmac.frame_store2 _ _ _

theorem copyMem_bytes (m : Mem) {o p : Addr} (h : (⟨o, 16⟩ : Region).Disjoint ⟨p, 16⟩) :
    Spec.Aes.bytesAt (VG.Proof.CmacAes.Stream.AArch64.copyMem m o p) o 16 = Spec.Aes.bytesAt m p 16 := by
  have g : Frame [⟨o, 8⟩] m (m.writeW o (m.readW p 64)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  rw [VG.Proof.CmacAes.Stream.AArch64.copyMem, Proof.Cmac.bytesAt_store2,
    g.readW (r := ⟨p + BitVec.ofNat 64 8, 8⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (h.sub_left (Region.sub_prefix (by decide))).sub_right
          (Offset.sub_base p (d := 8) (n := 8) (k := 16) (by decide)) |>.symm) (by decide),
    Proof.Cmac.le8_readW, Proof.Cmac.le8_readW, ← Proof.Cmac.bytesAt_split]

/-- The memory after `finishPre`. -/
def finMem (s : State) (St O S : Addr) : Mem :=
  ((VG.Proof.CmacAes.Stream.AArch64.copyMem s.mem O (St + BitVec.ofNat 64 272)).writeW (S + BitVec.ofNat 64 2176) (s.gpr .x19)).writeW
    (S + BitVec.ofNat 64 2184) (s.gpr .x30)

theorem finishPre_ok {s₀ : State} {St O S : Addr} {R : Nat} (hp : VG.Proof.CmacAes.Stream.AArch64.HPre s₀ St O S R) :
    ∃ s₁, runBlock isa finishPre s₀ = some s₁ ∧ s₁.gpr .x0 = St ∧ s₁.gpr .x1 = s₀.gpr .x1 ∧
      s₁.gpr .x2 = O ∧ s₁.gpr .x3 = St + BitVec.ofNat 64 288 ∧ s₁.gpr .x4 = s₀.gpr .x2 ∧
      s₁.gpr .x5 = S ∧ s₁.gpr .x19 = S ∧ (∀ r ∈ preserved, r ≠ .x19 → s₁.gpr r = s₀.gpr r) ∧
      s₁.sp = s₀.sp ∧ s₁.mem = VG.Proof.CmacAes.Stream.AArch64.finMem s₀ St O S ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr := by
  have hw := hp.wSt
  have inSt (d : Nat) (hd : d + 8 ≤ 304) : InRegions (s₀.rd ++ s₀.wr) (St + BitVec.ofNat 64 d) 8 := by
    rw [hp.rd, hp.wr]; exact ⟨⟨St, 304⟩, by simp, Offset.contains_base _ hd (by omega)⟩
  have inO (d : Nat) (hd : d + 8 ≤ 16) : InRegions s₀.wr (O + BitVec.ofNat 64 d) 8 := by
    rw [hp.wr]; exact ⟨⟨O, 16⟩, by simp, Offset.contains_base _ hd (by have := hp.wO; omega)⟩
  have inS (d : Nat) (hd : d + 8 ≤ 2304) : InRegions s₀.wr (S + BitVec.ofNat 64 d) 8 := by
    rw [hp.wr]; exact ⟨⟨S, 2304⟩, by simp, Offset.contains_base _ hd (by have := hp.wS; omega)⟩
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul, Nat.reduceMod, and_self, finishPre, mov, runBlock_cons, runStep_some, runBlock_nil,
      exec, addr, State.load, State.store, Size.bytes, Size.bits, State.read, gpr_write, mem_write,
      rd_write, wr_write, Option.bind_some, Option.map_some, BitVec.setWidth_eq,
      hp.x0, hp.x3, hp.x4, inSt 272 (by decide), inSt 280 (by decide), inO 0 (by decide),
      inO 8 (by decide), inS 2176 (by decide), inS 2184 (by decide)]
    rfl, ?_⟩
  refine ⟨by simp [gpr_write, hp.x0], by simp [gpr_write], by simp [gpr_write],
    by simp [gpr_write], by simp [gpr_write], by simp [gpr_write], by simp [gpr_write],
    fun r hr h19 => ?_, rfl, ?_, rfl, rfl⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [gpr_write]
  · simp only [mem_write, VG.Proof.CmacAes.Stream.AArch64.finMem, VG.Proof.CmacAes.Stream.AArch64.copyMem, Mem.writeW, Mem.readW, BitVec.setWidth_eq, k0, Offset.add_add,
      Nat.reduceAdd]

/-- Storing two words in the slots at `S + 2176`. -/
theorem slots_frame (m : Mem) (S : Addr) (a b : BitVec 64) :
    Frame [⟨S + BitVec.ofNat 64 2176, 16⟩] m
      ((m.writeW (S + BitVec.ofNat 64 2176) a).writeW (S + BitVec.ofNat 64 2184) b) := by
  rw [(Offset.add_add_eq S (a := 2176) (b := 8) (c := 2184) rfl).symm]
  exact Proof.Cmac.frame_store2 _ _ _

theorem finMem_frame (s : State) (St O S : Addr) :
    Frame [⟨O, 16⟩, ⟨S + BitVec.ofNat 64 2176, 16⟩] s.mem (VG.Proof.CmacAes.Stream.AArch64.finMem s St O S) :=
  ((VG.Proof.CmacAes.Stream.AArch64.copyMem_frame _ _ _).mono fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp only [List.mem_cons, true_or]).trans
  ((VG.Proof.CmacAes.Stream.AArch64.slots_frame _ _ _ _).mono fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_of_mem _ (List.mem_singleton_self _))

theorem finMem_slots (s : State) (St O S : Addr) :
    (VG.Proof.CmacAes.Stream.AArch64.finMem s St O S).readW (S + BitVec.ofNat 64 2176) 64 = s.gpr .x19 ∧
      (VG.Proof.CmacAes.Stream.AArch64.finMem s St O S).readW (S + BitVec.ofNat 64 2184) 64 = s.gpr .x30 :=
  ⟨by rw [VG.Proof.CmacAes.Stream.AArch64.finMem, readW_writeW_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64],
    by rw [VG.Proof.CmacAes.Stream.AArch64.finMem, Mem.readW_writeW_self64]⟩

/-- What the code before the call leaves. -/
structure HMid (s₀ : State) (St O S : Addr) (R : Nat) (s : State) : Prop where
  args : VG.Proof.CmacAes.Stream.AArch64.FArgs s St O (St + BitVec.ofNat 64 288) S (held (s₀.gpr .x2).toNat) R
  mem : s.mem = VG.Proof.CmacAes.Stream.AArch64.finMem s₀ St O S
  x19 : s.gpr .x19 = S
  saved : ∀ r ∈ preserved, r ≠ .x19 → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem HPre.fargs {s₀ s : State} {St O S : Addr} {R L : Nat} (hp : VG.Proof.CmacAes.Stream.AArch64.HPre s₀ St O S R) (hL : L ≤ 16)
    (x0 : s.gpr .x0 = St) (x1 : s.gpr .x1 = s₀.gpr .x1) (x2 : s.gpr .x2 = O)
    (x3 : s.gpr .x3 = St + BitVec.ofNat 64 288) (x4 : s.gpr .x4 = BitVec.ofNat 64 L)
    (x5 : s.gpr .x5 = S) (rd : s.rd = s₀.rd) (wr : s.wr = s₀.wr) :
    VG.Proof.CmacAes.Stream.AArch64.FArgs s St O (St + BitVec.ofNat 64 288) S L R := by
  have hw := hp.wSt
  have pSt : Region.Sub ⟨St + BitVec.ofNat 64 288, L⟩ ⟨St, 304⟩ := Offset.sub_base St (by omega)
  exact
  { x0 := x0, x2 := x2, x3 := x3, x4 := x4, x5 := x5
    x1 := by rw [x1]; exact VG.Proof.CmacAes.Stream.AArch64.ofNat_toNat_eq hp.x1
    rounds := hp.rounds, len := hL
    kst := hp.st_o.sub_left (Region.sub_prefix (by decide))
    ks := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    pst := hp.st_o.sub_left pSt
    ps := (hp.st_s.sub_left pSt).sub_right (Region.sub_prefix (by decide))
    sts := hp.o_s.sub_right (Region.sub_prefix (by decide))
    wrapK := by omega
    wrapSt := hp.wO
    wrapP := by rw [VG.Proof.CmacAes.Stream.AArch64.toNat_add_lt St hw (by decide)]; omega
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

theorem lastLen_ok (s : State) {c : BitVec 64} (h4 : s.gpr .x4 = c) (hc : c ≠ 0) :
    ∃ s', runBlock isa [.subImm .x .x4 .x4 1, .movz .x .x9 15 0, .logic .and .x .x4 .x4 .x9,
        .addImm .x .x4 .x4 1] s = some s' ∧ s'.gpr .x4 = BitVec.ofNat 64 (held c.toNat) ∧
      (∀ r, r ≠ .x4 → r ≠ .x9 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul, runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
      State.read, gpr_write, BitVec.setWidth_eq]
    rfl, ?_⟩
  refine ⟨?_, fun r h₁ h₂ => by simp [gpr_write, h₁, h₂], rfl, rfl, rfl, rfl⟩
  simp only [gpr_write, ite_true, BitVec.setWidth_eq, h4]
  exact VG.Proof.CmacAes.Stream.AArch64.held_bv c hc

theorem finPre_wp {s₀ : State} {St O S : Addr} {R : Nat} (hp : VG.Proof.CmacAes.Stream.AArch64.HPre s₀ St O S R) :
    WP isa finPre s₀ (VG.Proof.CmacAes.Stream.AArch64.HMid s₀ St O S R) := by
  obtain ⟨s₁, run₁, x0₁, x1₁, x2₁, x3₁, x4₁, x5₁, x19₁, sv₁, sp₁, m₁, rd₁, wr₁⟩ := VG.Proof.CmacAes.Stream.AArch64.finishPre_ok hp
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have hc := (s₀.gpr .x2).isLt
  have h2 : s₀.gpr .x2 = BitVec.ofNat 64 (s₀.gpr .x2).toNat := VG.Proof.CmacAes.Stream.AArch64.ofNat_toNat_eq rfl
  by_cases h0 : (s₀.gpr .x2).toNat = 0
  · refine WP.ite true (by rw [VG.Proof.CmacAes.Stream.AArch64.eval_zero hc (by rw [x4₁]; exact h2), h0]; rfl)
      (fun _ => WP.block_nil ?_) (fun h => by cases h)
    refine ⟨hp.fargs (held_le _) x0₁ x1₁ x2₁ x3₁ ?_ x5₁ rd₁ wr₁, m₁, x19₁, sv₁, sp₁, rd₁, wr₁⟩
    rw [x4₁, h2, h0]; rfl
  · refine WP.ite false (by rw [VG.Proof.CmacAes.Stream.AArch64.eval_zero hc (by rw [x4₁]; exact h2)]; simp [h0])
      (fun h => by cases h) fun _ => ?_
    have hne : s₀.gpr .x2 ≠ 0 := fun e => h0 (by rw [e]; rfl)
    obtain ⟨s₂, run₂, x4₂, g₂, sp₂, m₂, rd₂, wr₂⟩ := VG.Proof.CmacAes.Stream.AArch64.lastLen_ok s₁ x4₁ hne
    refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
    have hc : ∀ r ∈ preserved, r ≠ .x4 ∧ r ≠ .x9 := by decide
    refine ⟨hp.fargs (held_le _) (by rw [g₂ _ (by decide) (by decide), x0₁])
      (by rw [g₂ _ (by decide) (by decide), x1₁]) (by rw [g₂ _ (by decide) (by decide), x2₁])
      (by rw [g₂ _ (by decide) (by decide), x3₁]) x4₂ (by rw [g₂ _ (by decide) (by decide), x5₁])
      (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]), by rw [m₂, m₁],
      by rw [g₂ _ (by decide) (by decide), x19₁],
      fun r hr h19 => by rw [g₂ r (hc r hr).1 (hc r hr).2, sv₁ r hr h19], by rw [sp₂, sp₁], by rw [rd₂, rd₁],
      by rw [wr₂, wr₁]⟩

/-! ## After the call -/

theorem finishPost_ok (s : State) {B : Addr} (hb : s.gpr .x19 = B)
    (r₁ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 2184) 8)
    (r₂ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 2176) 8) :
    ∃ s', runBlock isa finishPost s = some s' ∧
      s'.gpr .x30 = s.mem.readW (B + BitVec.ofNat 64 2184) 64 ∧
      s'.gpr .x19 = s.mem.readW (B + BitVec.ofNat 64 2176) 64 ∧
      (∀ r, r ≠ .x19 → r ≠ .x30 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul, Nat.reduceMod, and_self, finishPost, runBlock_cons, runStep_some, runBlock_nil, exec,
      addr, State.load, Size.bytes, Size.bits, gpr_write, mem_write, rd_write, wr_write,
      Option.bind_some, Option.map_some, hb, r₁, r₂]
    rfl, ?_⟩
  refine ⟨by simp [gpr_write, Mem.readW], by simp [gpr_write, Mem.readW],
    fun r h₁ h₂ => by simp [gpr_write, h₁, h₂], rfl, rfl⟩

/-! ## The whole function -/

theorem finish_wp (v : Ctr32Impl) {s₀ : State} (h0 : finishAArch64.pre s₀) :
    WP isa (finish v.callee v.suffix) s₀ fun s' => GprAbi s₀ s' ∧ finishAArch64.post s₀ s' := by
  have hp := HPre.of h0
  generalize s₀.gpr .x0 = St at hp
  generalize s₀.gpr .x3 = O at hp
  generalize s₀.gpr .x4 = S at hp
  generalize (s₀.gpr .x1).toNat = R at hp
  have hw := hp.wSt
  have sw := hp.wS
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.AArch64.finPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.AArch64.fin_call v _ h₁.args) fun s₂ h₂ => ?_)
  have x19₂ : s₂.gpr .x19 = S := by rw [h₂.saved _ (by simp [preserved]) (by decide), h₁.x19]
  have inS (d : Nat) (hd : d + 8 ≤ 2304) : InRegions (s₂.rd ++ s₂.wr) (S + BitVec.ofNat 64 d) 8 := by
    rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr, hp.rd, hp.wr]
    exact ⟨⟨S, 2304⟩, by simp, Offset.contains_base _ hd (by omega)⟩
  obtain ⟨s₃, run₃, x30₃, x19₃, g₃, sp₃, m₃⟩ := VG.Proof.CmacAes.Stream.AArch64.finishPost_ok s₂ x19₂ (inS 2184 (by decide))
    (inS 2176 (by decide))
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  -- The slots, which the call does not write.
  have slots (d : Nat) (h₁' : 2176 ≤ d) (h₂' : d + 8 ≤ 2304) :
      s₂.mem.readW (S + BitVec.ofNat 64 d) 64 = s₁.mem.readW (S + BitVec.ofNat 64 d) 64 := by
    refine h₂.frame.readW (r := ⟨S + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.o_s.symm.sub_left (Offset.sub_base S h₂')
    · exact Offset.disjoint_base _ (by omega) (by omega)
  obtain ⟨sl19, sl30⟩ := VG.Proof.CmacAes.Stream.AArch64.finMem_slots s₀ St O S
  refine ⟨⟨fun r hr => ?_, by rw [sp₃, h₂.sp, h₁.sp]⟩, ?_⟩
  · by_cases h19 : r = .x19
    · subst h19; rw [x19₃, slots 2176 (by decide) (by decide), h₁.mem, sl19]
    by_cases h30 : r = .x30
    · subst h30; rw [x30₃, slots 2184 (by decide) (by decide), h₁.mem, sl30]
    rw [g₃ r h19 h30, h₂.saved r hr h30, h₁.saved r hr h19]
  · intro key msg hr hR hc hlen
    rw [hp.x0] at hr
    rw [Proof.Cmac.Stream.repr_iff] at hr
    obtain ⟨⟨hkl, hks, hsk⟩, hcv, hhb⟩ := hr
    have hn : (s₀.gpr .x2).toNat = msg.length := by rw [hc, VG.Proof.CmacAes.Stream.AArch64.toNat_ofNat hlen]
    rw [hp.x3, m₃]
    have hR' : R = Spec.Aes.rounds (key.length / 4) := by rw [← hp.x1]; exact hR
    -- The state is unchanged before the call.
    have fSt : ∀ {d n : Nat}, d + n ≤ 304 → Spec.Aes.bytesAt s₁.mem (St + BitVec.ofNat 64 d) n =
        Spec.Aes.bytesAt s₀.mem (St + BitVec.ofNat 64 d) n := fun {d n} hd => by
      rw [h₁.mem]
      exact Proof.Cmac.bytesAt_frame (VG.Proof.CmacAes.Stream.AArch64.finMem_frame _ _ _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hp.st_o.sub_left (Offset.sub_base St hd)
        · exact (hp.st_s.sub_left (Offset.sub_base St hd)).sub_right (Offset.sub_base S (by decide)))
        (by omega)
    have hsch : Spec.Aes.bytesAt s₁.mem St (16 * (R + 1)) = Spec.Aes.expandKey key := by
      have := fSt (d := 0) (n := 16 * (R + 1)) (by rcases hp.rounds with h | h | h <;> omega)
      rw [k0] at this; rw [this, hR']; exact hks
    have hciph : Spec.Cmac.aesWith R (Spec.Aes.bytesAt s₁.mem St (16 * (R + 1))) = Spec.Cmac.aes key := by
      rw [hsch, hR']; rfl
    have e₁ : Spec.Aes.bytesAt s₁.mem (St + 240) 32 = Spec.Aes.bytesAt s₀.mem (St + 240) 32 :=
      fSt (d := 240) (by decide)
    have e₂ : Spec.Aes.bytesAt s₁.mem O 16 = Spec.Aes.bytesAt s₀.mem (St + 272) 16 := by
      rw [h₁.mem, VG.Proof.CmacAes.Stream.AArch64.finMem, Proof.Cmac.bytesAt_frame16 (VG.Proof.CmacAes.Stream.AArch64.slots_frame _ _ _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.o_s.sub_right (Offset.sub_base S (by decide)))]
      exact VG.Proof.CmacAes.Stream.AArch64.copyMem_bytes _ (hp.st_o.symm.sub_right (Offset.sub_base St (by decide)))
    have e₃ : Spec.Aes.bytesAt s₁.mem (St + BitVec.ofNat 64 288) (held (s₀.gpr .x2).toNat) =
        Spec.Aes.bytesAt s₀.mem (St + 288) (held msg.length) := by
      rw [hn]; exact fSt (by have := held_le msg.length; omega)
    obtain ⟨hm, hne, hst, happ⟩ := Proof.Cmac.Stream.repr_finish
      ((Proof.Cmac.Stream.repr_iff _ _ _ _).mpr ⟨⟨hkl, hks, hsk⟩, hcv, hhb⟩)
    have out := h₂.out (by rw [hciph, e₁]; exact hsk) _ hm (by rw [hn]; exact hne)
      (by rw [hciph, e₂]; exact hst)
    rw [out, hciph, e₃, happ, Proof.Cmac.Stream.aesCmac_eq]

/-! ## Constant time -/

theorem finish_rel (v : Ctr32Impl) {s₀ s₀' : State} (h0 : finishAArch64.pre s₀)
    (h0' : finishAArch64.pre s₀') (hq : finishAArch64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (finish v.callee v.suffix) fun _ _ => True := by
  obtain ⟨q0, q1, q2, q3, q4, q5⟩ := hq
  have hp := HPre.of h0
  have hp' : VG.Proof.CmacAes.Stream.AArch64.HPre s₀' (s₀.gpr .x0) (s₀.gpr .x3) (s₀.gpr .x4) (s₀.gpr .x1).toNat := by
    rw [q0, q1, q3, q4]; exact HPre.of h0'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) finPre h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.x19]) (.block finishPost) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine agree_of q5 fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption) hA).wp
    (F₁ := VG.Proof.CmacAes.Stream.AArch64.HMid s₀ _ _ _ _) (F₂ := VG.Proof.CmacAes.Stream.AArch64.HMid s₀' _ _ _ _) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨VG.Proof.CmacAes.Stream.AArch64.finPre_wp hp, VG.Proof.CmacAes.Stream.AArch64.finPre_wp hp'⟩
  have c := (VG.Proof.CmacAes.Stream.AArch64.fin_rel v ("vg_cmac_aes_finalize" ++ v.suffix) (P := fun s₁ s₂ =>
      VG.Proof.CmacAes.Stream.AArch64.HMid s₀ (s₀.gpr .x0) (s₀.gpr .x3) (s₀.gpr .x4) (s₀.gpr .x1).toNat s₁ ∧
      VG.Proof.CmacAes.Stream.AArch64.HMid s₀' (s₀.gpr .x0) (s₀.gpr .x3) (s₀.gpr .x4) (s₀.gpr .x1).toNat s₂)
    fun s₁ s₂ h => ⟨h.1.args, by rw [q2]; exact h.2.args, by rw [h.1.sp, h.2.sp, q5]⟩).wp
    (F₁ := fun (s : State) => s.gpr .x19 = s₀.gpr .x4 ∧ s.sp = s₀.sp)
    (F₂ := fun (s : State) => s.gpr .x19 = s₀.gpr .x4 ∧ s.sp = s₀'.sp) fun s₁ s₂ h =>
      ⟨WP.mono (VG.Proof.CmacAes.Stream.AArch64.fin_call v _ h.1.args) fun _ hc =>
        ⟨by rw [hc.saved .x19 (by simp [preserved]) (by decide), h.1.x19], by rw [hc.sp, h.1.sp]⟩,
       WP.mono (VG.Proof.CmacAes.Stream.AArch64.fin_call v _ h.2.args) fun _ hc =>
        ⟨by rw [hc.saved .x19 (by simp [preserved]) (by decide), h.2.x19], by rw [hc.sp, h.2.sp]⟩⟩
  have b := RelCT.taint (A := taint)
    (P := fun s₁ s₂ => (s₁.gpr .x19 = s₀.gpr .x4 ∧ s₁.sp = s₀.sp) ∧ (s₂.gpr .x19 = s₀.gpr .x4 ∧ s₂.sp = s₀'.sp)) _
    (fun s₁ s₂ h => agree_of (by rw [h.1.2, h.2.2, q5]) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [h.1.1, h.2.1]) hB
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((c.mono (fun _ _ h => h) fun _ _ h => h.2).seq b)

theorem finish_ct (v : Ctr32Impl) :
    ConstantTime isa finishAArch64.pre finishAArch64.pub (finish v.callee v.suffix) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (VG.Proof.CmacAes.Stream.AArch64.finish_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.Stream.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.Stream.AArch64.Init`. -/
section

/-!
# Streaming AES-CMAC on AArch64: `vg_cmac_aes_init`

The code saves `x19`, `x20`, `x21` and `x30` in the scratch buffer, expands
the key into the state, derives the subkeys after the schedule, zeroes the
chaining value and restores the registers: the state then represents the empty
message. The code between the calls is constant time by the taint analysis,
and the calls by their own proofs (`ek_rel`, `sub_rel`), their arguments
pinned by `IMid₁` and `IMid₂`.
-/

namespace VG.Proof.CmacAes.Stream.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.CmacAes.Stream.AArch64
open VG.Impl.CmacAes.AArch64 (mov)
open VG.Proof.CmacAes.AArch64 (k0 readW_writeW_other agree_of)
open VG.Proof.Aes.AArch64 (Ctr32Impl)

/-- The precondition, by name: the state `St`, the key `Kp` of `KL` bytes
and the scratch buffer `S`. -/
structure IPre (s₀ : State) (St Kp S : Addr) (KL : Nat) : Prop where
  x0 : s₀.gpr .x0 = St
  x1 : s₀.gpr .x1 = Kp
  x2 : (s₀.gpr .x2).toNat = KL
  x3 : s₀.gpr .x3 = S
  rd : s₀.rd = [⟨Kp, KL⟩]
  wr : s₀.wr = [⟨St, 304⟩, ⟨S, 2304⟩]
  st_k : (⟨St, 304⟩ : Region).Disjoint ⟨Kp, KL⟩
  st_s : (⟨St, 304⟩ : Region).Disjoint ⟨S, 2304⟩
  k_s : (⟨Kp, KL⟩ : Region).Disjoint ⟨S, 2304⟩
  wSt : St.toNat + 304 ≤ 2 ^ 64
  wK : Kp.toNat + KL ≤ 2 ^ 64
  wS : S.toNat + 2304 ≤ 2 ^ 64
  klen : KL = 16 ∨ KL = 24 ∨ KL = 32

theorem IPre.of {s₀ : State} (h : initAArch64.pre s₀) :
    VG.Proof.CmacAes.Stream.AArch64.IPre s₀ (s₀.gpr .x0) (s₀.gpr .x1) (s₀.gpr .x3) (s₀.gpr .x2).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i⟩ := h
  ⟨rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i⟩

theorem IPre.rounds {s₀ : State} {St Kp S : Addr} {KL : Nat} (hp : VG.Proof.CmacAes.Stream.AArch64.IPre s₀ St Kp S KL) :
    KL / 4 + 6 = 10 ∨ KL / 4 + 6 = 12 ∨ KL / 4 + 6 = 14 := by
  rcases hp.klen with h | h | h <;> subst h <;> decide

/-- The memory after saving the registers. -/
def initSavedMem (s : State) (S : Addr) : Mem :=
  (((s.mem.writeW (S + BitVec.ofNat 64 2176) (s.gpr .x19)).writeW (S + BitVec.ofNat 64 2184) (s.gpr .x20)).writeW
    (S + BitVec.ofNat 64 2192) (s.gpr .x21)).writeW (S + BitVec.ofNat 64 2200) (s.gpr .x30)

theorem initSavedMem_frame (s : State) (S : Addr) :
    Frame [⟨S + BitVec.ofNat 64 2176, 32⟩] s.mem (VG.Proof.CmacAes.Stream.AArch64.initSavedMem s S) := by
  have c (d : Nat) (hd : d + 8 ≤ 32) : (⟨S + BitVec.ofNat 64 2176, 32⟩ : Region).Contains
      (S + BitVec.ofNat 64 (2176 + d)) 8 := by
    rw [← Offset.add_add]; exact Offset.contains_base _ hd (by omega)
  exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by simpa using c 0 (by decide))).writeW
    (List.mem_singleton_self _) _ (c 8 (by decide))).writeW (List.mem_singleton_self _) _
    (c 16 (by decide))).writeW (List.mem_singleton_self _) _ (c 24 (by decide))

theorem initSaved_read (s : State) (S : Addr) :
    (VG.Proof.CmacAes.Stream.AArch64.initSavedMem s S).readW (S + BitVec.ofNat 64 2176) 64 = s.gpr .x19 ∧
      (VG.Proof.CmacAes.Stream.AArch64.initSavedMem s S).readW (S + BitVec.ofNat 64 2184) 64 = s.gpr .x20 ∧
      (VG.Proof.CmacAes.Stream.AArch64.initSavedMem s S).readW (S + BitVec.ofNat 64 2192) 64 = s.gpr .x21 ∧
      (VG.Proof.CmacAes.Stream.AArch64.initSavedMem s S).readW (S + BitVec.ofNat 64 2200) 64 = s.gpr .x30 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [VG.Proof.CmacAes.Stream.AArch64.initSavedMem, readW_writeW_other _ _ _ (by decide) (by decide) (by decide),
      readW_writeW_other _ _ _ (by decide) (by decide) (by decide),
      readW_writeW_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
  · rw [VG.Proof.CmacAes.Stream.AArch64.initSavedMem, readW_writeW_other _ _ _ (by decide) (by decide) (by decide),
      readW_writeW_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
  · rw [VG.Proof.CmacAes.Stream.AArch64.initSavedMem, readW_writeW_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
  · rw [VG.Proof.CmacAes.Stream.AArch64.initSavedMem, Mem.readW_writeW_self64]

/-! ## Before the first call -/

theorem initPre_ok {s₀ : State} {St Kp S : Addr} {KL : Nat} (hp : VG.Proof.CmacAes.Stream.AArch64.IPre s₀ St Kp S KL) :
    ∃ s₁, runBlock isa initPre s₀ = some s₁ ∧ s₁.gpr .x0 = Kp ∧ s₁.gpr .x1 = BitVec.ofNat 64 KL ∧
      s₁.gpr .x2 = St ∧ s₁.gpr .x3 = S ∧ s₁.gpr .x19 = St ∧ s₁.gpr .x20 = S ∧
      s₁.gpr .x21 = BitVec.ofNat 64 (KL / 4 + 6) ∧
      (∀ r ∈ preserved, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → s₁.gpr r = s₀.gpr r) ∧ s₁.sp = s₀.sp ∧
      s₁.mem = VG.Proof.CmacAes.Stream.AArch64.initSavedMem s₀ S ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr := by
  have inS (d : Nat) (hd : d + 8 ≤ 2304) : InRegions s₀.wr (S + BitVec.ofNat 64 d) 8 := by
    rw [hp.wr]; exact ⟨⟨S, 2304⟩, by simp, Offset.contains_base _ hd (by have := hp.wS; omega)⟩
  have hKL : s₀.gpr .x2 = BitVec.ofNat 64 KL := VG.Proof.CmacAes.Stream.AArch64.ofNat_toNat_eq hp.x2
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul, Nat.reduceMod, and_self, initPre, initSaved, mov, List.map, List.cons_append,
      List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.store, Size.bytes,
      Size.bits, State.read, gpr_write, Option.bind_some,
      BitVec.setWidth_eq, hp.x3, inS 2176 (by decide), inS 2184 (by decide), inS 2192 (by decide),
      inS 2200 (by decide)]
    rfl, ?_⟩
  refine ⟨by simp [gpr_write, hp.x1], by simp [gpr_write, hKL], by simp [gpr_write, hp.x0],
    by simp [gpr_write, hp.x3], by simp [gpr_write, hp.x0], by simp [gpr_write],
    by simp [gpr_write, hKL, VG.Proof.CmacAes.Stream.AArch64.rounds_bv hp.klen], fun r hr h19 h20 h21 => ?_, rfl, ?_, rfl, rfl⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [gpr_write]
  · simp only [mem_write, VG.Proof.CmacAes.Stream.AArch64.initSavedMem, Mem.writeW, BitVec.setWidth_eq]

/-- What the code before the first call leaves. -/
structure IMid₁ (s₀ : State) (St Kp S : Addr) (KL : Nat) (s : State) : Prop where
  args : VG.Proof.CmacAes.Stream.AArch64.EArgs s Kp St S KL
  x19 : s.gpr .x19 = St
  x20 : s.gpr .x20 = S
  x21 : s.gpr .x21 = BitVec.ofNat 64 (KL / 4 + 6)
  other : ∀ r ∈ preserved, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  mem : s.mem = VG.Proof.CmacAes.Stream.AArch64.initSavedMem s₀ S
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem initPre_wp {s₀ : State} {St Kp S : Addr} {KL : Nat} (hp : VG.Proof.CmacAes.Stream.AArch64.IPre s₀ St Kp S KL) :
    WP isa (.block initPre) s₀ (VG.Proof.CmacAes.Stream.AArch64.IMid₁ s₀ St Kp S KL) := by
  obtain ⟨s₁, run₁, x0₁, x1₁, x2₁, x3₁, x19₁, x20₁, x21₁, o₁, sp₁, m₁, rd₁, wr₁⟩ := VG.Proof.CmacAes.Stream.AArch64.initPre_ok hp
  refine WP.of_runBlock ⟨s₁, run₁, ⟨?_, x19₁, x20₁, x21₁, o₁, sp₁, m₁, rd₁, wr₁⟩⟩
  exact
  { x0 := x0₁, x1 := x1₁, x2 := x2₁, x3 := x3₁, klen := hp.klen
    kw := hp.st_k.symm.sub_right (Region.sub_prefix (by decide))
    ks := hp.k_s.sub_right (Region.sub_prefix (by decide))
    ws := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
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

/-! ## Between the calls, and after them -/

theorem initMid_ok {s : State} {St S : Addr} {R : Nat} (h19 : s.gpr .x19 = St) (h20 : s.gpr .x20 = S)
    (h21 : s.gpr .x21 = BitVec.ofNat 64 R) :
    ∃ s', runBlock isa initMid s = some s' ∧ s'.gpr .x0 = St ∧ s'.gpr .x1 = BitVec.ofNat 64 R ∧
      s'.gpr .x2 = St + BitVec.ofNat 64 240 ∧ s'.gpr .x3 = S ∧
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, initMid, mov, runBlock_cons, runStep_some, runBlock_nil, exec,
      Size.bits, State.read, gpr_write, BitVec.setWidth_eq]
    rfl, ?_⟩
  refine ⟨by simp [gpr_write, h19], by simp [gpr_write, h21], by simp [gpr_write, h19],
    by simp [gpr_write, h20], fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]

/-- The memory after zeroing the chaining value. -/
def zeroCv (m : Mem) (St : Addr) : Mem :=
  (m.writeW (St + BitVec.ofNat 64 272) (0 : BitVec 64)).writeW (St + BitVec.ofNat 64 280) (0 : BitVec 64)

theorem zeroCv_eq (m : Mem) (St : Addr) : VG.Proof.CmacAes.Stream.AArch64.zeroCv m St = Proof.Cmac.zero2 m (St + BitVec.ofNat 64 272) := by
  rw [VG.Proof.CmacAes.Stream.AArch64.zeroCv, Proof.Cmac.zero2, Offset.add_add]

theorem initPost_ok {s : State} {St S : Addr} (h19 : s.gpr .x19 = St) (h20 : s.gpr .x20 = S)
    (w₁ : InRegions s.wr (St + BitVec.ofNat 64 272) 8) (w₂ : InRegions s.wr (St + BitVec.ofNat 64 280) 8)
    (r₁ : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 2176) 8)
    (r₂ : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 2184) 8)
    (r₃ : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 2192) 8)
    (r₄ : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 2200) 8) :
    ∃ s', runBlock isa initPost s = some s' ∧
      s'.gpr .x19 = (VG.Proof.CmacAes.Stream.AArch64.zeroCv s.mem St).readW (S + BitVec.ofNat 64 2176) 64 ∧
      s'.gpr .x20 = (VG.Proof.CmacAes.Stream.AArch64.zeroCv s.mem St).readW (S + BitVec.ofNat 64 2184) 64 ∧
      s'.gpr .x21 = (VG.Proof.CmacAes.Stream.AArch64.zeroCv s.mem St).readW (S + BitVec.ofNat 64 2192) 64 ∧
      s'.gpr .x30 = (VG.Proof.CmacAes.Stream.AArch64.zeroCv s.mem St).readW (S + BitVec.ofNat 64 2200) 64 ∧
      (∀ r, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x30 → r ≠ .x9 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = VG.Proof.CmacAes.Stream.AArch64.zeroCv s.mem St := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul, Nat.reduceMod, and_self, initPost, runBlock_cons, runStep_some, runBlock_nil, exec,
      addr, State.load, State.store, Size.bytes, Size.bits, State.read, gpr_write, mem_write, rd_write,
      wr_write, Option.bind_some, Option.map_some, BitVec.setWidth_eq, h19, h20,
      w₁, w₂, r₁, r₂, r₃, r₄]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, fun r a b c d f => by simp [gpr_write, a, b, c, d, f], rfl, ?_⟩
  all_goals simp [gpr_write, mem_write, VG.Proof.CmacAes.Stream.AArch64.zeroCv, Mem.readW, Mem.writeW]

/-- What the code between the calls leaves. -/
structure IMid₂ (s₀ : State) (St S : Addr) (KL : Nat) (m : Mem) (s : State) : Prop where
  args : VG.Proof.CmacAes.Stream.AArch64.SArgs s St (St + BitVec.ofNat 64 240) S (KL / 4 + 6)
  x19 : s.gpr .x19 = St
  x20 : s.gpr .x20 = S
  keep : ∀ r ∈ preserved, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x30 → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  mem : s.mem = m
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem initMid_wp {s₀ s : State} {St Kp S : Addr} {KL : Nat} (hp : VG.Proof.CmacAes.Stream.AArch64.IPre s₀ St Kp S KL)
    (h19 : s.gpr .x19 = St) (h20 : s.gpr .x20 = S) (h21 : s.gpr .x21 = BitVec.ofNat 64 (KL / 4 + 6))
    (hsp : s.sp = s₀.sp) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hk : ∀ r ∈ preserved, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x30 → s.gpr r = s₀.gpr r) :
    WP isa (.block initMid) s (VG.Proof.CmacAes.Stream.AArch64.IMid₂ s₀ St S KL s.mem) := by
  obtain ⟨s', run, x0, x1, x2, x3, sv, sp, mem, rd, wr⟩ := VG.Proof.CmacAes.Stream.AArch64.initMid_ok h19 h20 h21
  have hw := hp.wSt
  have kSt : Region.Sub ⟨St + BitVec.ofNat 64 240, 32⟩ ⟨St, 304⟩ := Offset.sub_base St (by decide)
  refine WP.of_runBlock ⟨s', run, ⟨?_, by rw [sv _ (by simp [preserved]), h19],
    by rw [sv _ (by simp [preserved]), h20], fun r hr a b c d => by rw [sv r hr, hk r hr a b c d],
    by rw [sp, hsp], mem, by rw [rd, hrd], by rw [wr, hwr]⟩⟩
  exact
  { x0 := x0, x1 := x1, x2 := x2, x3 := x3, rounds := hp.rounds
    wk := Offset.base_disjoint St (by decide) (by omega)
    ws := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    ks := (hp.st_s.sub_left kSt).sub_right (Region.sub_prefix (by decide))
    wrapK := by rw [VG.Proof.CmacAes.Stream.AArch64.toNat_add_lt St hw (by decide)]; omega
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

/-! ## The whole function -/

theorem init_wp (v : Ctr32Impl) {s₀ : State} (h0 : initAArch64.pre s₀) :
    WP isa (init v.expand v.callee v.suffix) s₀ fun s' => GprAbi s₀ s' ∧ initAArch64.post s₀ s' := by
  have hp := IPre.of h0
  generalize s₀.gpr .x0 = St at hp
  generalize s₀.gpr .x1 = Kp at hp
  generalize s₀.gpr .x3 = S at hp
  generalize (s₀.gpr .x2).toNat = KL at hp
  have hw := hp.wSt
  have hsw := hp.wS
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.AArch64.initPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.AArch64.ek_call v h₁.args) fun s₂ h₂ => ?_)
  have g₂ (r : Reg) (hr : r ∈ preserved) (h30 : r ≠ .x30) : s₂.gpr r = s₁.gpr r := h₂.saved r hr h30
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.AArch64.initMid_wp hp (by rw [g₂ _ (by simp [preserved]) (by decide), h₁.x19])
    (by rw [g₂ _ (by simp [preserved]) (by decide), h₁.x20])
    (by rw [g₂ _ (by simp [preserved]) (by decide), h₁.x21]) (by rw [h₂.sp, h₁.sp]) (by rw [h₂.rd, h₁.rd])
    (by rw [h₂.wr, h₁.wr]) (fun r hr a b c d => by rw [g₂ r hr d, h₁.other r hr a b c])) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (VG.Proof.CmacAes.Stream.AArch64.sub_call v _ h₃.args) fun s₄ h₄ => ?_)
  have g₄ (r : Reg) (hr : r ∈ preserved) (h30 : r ≠ .x30) : s₄.gpr r = s₃.gpr r := h₄.saved r hr h30
  have inS (d : Nat) (hd : d + 8 ≤ 2304) : InRegions s₄.wr (S + BitVec.ofNat 64 d) 8 := by
    rw [h₄.wr, h₃.wr, hp.wr]; exact ⟨⟨S, 2304⟩, by simp, Offset.contains_base _ hd (by omega)⟩
  have inSt (d : Nat) (hd : d + 8 ≤ 304) : InRegions s₄.wr (St + BitVec.ofNat 64 d) 8 := by
    rw [h₄.wr, h₃.wr, hp.wr]; exact ⟨⟨St, 304⟩, by simp, Offset.contains_base _ hd (by omega)⟩
  have inR (d : Nat) (hd : d + 8 ≤ 2304) : InRegions (s₄.rd ++ s₄.wr) (S + BitVec.ofNat 64 d) 8 := by
    obtain ⟨r, hr, hc⟩ := inS d hd; exact ⟨r, List.mem_append_right _ hr, hc⟩
  obtain ⟨s₅, run₅, x19₅, x20₅, x21₅, x30₅, keep₅, sp₅, m₅⟩ := VG.Proof.CmacAes.Stream.AArch64.initPost_ok (s := s₄) (St := St) (S := S)
    (by rw [g₄ _ (by simp [preserved]) (by decide), h₃.x19])
    (by rw [g₄ _ (by simp [preserved]) (by decide), h₃.x20])
    (inSt 272 (by decide)) (inSt 280 (by decide)) (inR 2176 (by decide)) (inR 2184 (by decide))
    (inR 2192 (by decide)) (inR 2200 (by decide))
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  -- The memory, step by step.
  have fz : Frame [⟨St + BitVec.ofNat 64 272, 16⟩] s₄.mem (VG.Proof.CmacAes.Stream.AArch64.zeroCv s₄.mem St) := by
    rw [VG.Proof.CmacAes.Stream.AArch64.zeroCv_eq]; exact Proof.Cmac.frame_store2 _ _ _
  have f₁ : Frame [⟨S + BitVec.ofNat 64 2176, 32⟩] s₀.mem s₁.mem := by
    rw [h₁.mem]; exact VG.Proof.CmacAes.Stream.AArch64.initSavedMem_frame _ _
  have f₂ : Frame [⟨St, 240⟩, ⟨S, 512⟩] s₁.mem s₂.mem := h₂.frame
  have f₄ : Frame [⟨St + BitVec.ofNat 64 240, 32⟩, ⟨S, 2176⟩] s₃.mem s₄.mem := h₄.frame
  have m₃ : s₃.mem = s₂.mem := h₃.mem
  -- The saved registers.
  have dSv (r : Region) (hr : r ∈ [⟨St, 240⟩, ⟨S, 512⟩, ⟨St + BitVec.ofNat 64 240, 32⟩,
      ⟨S, 2176⟩, ⟨St + BitVec.ofNat 64 272, 16⟩]) (d : Nat) (hd : 2176 ≤ d) (hd' : d + 8 ≤ 2304) :
      (⟨S + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
    have sub : Region.Sub ⟨S + BitVec.ofNat 64 d, 8⟩ ⟨S, 2304⟩ := Offset.sub_base S hd'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).symm.sub_left sub
    · exact Offset.disjoint_base S (by omega) (by omega)
    · exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).symm.sub_left sub
    · exact Offset.disjoint_base S (by omega) (by omega)
    · exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).symm.sub_left sub
  have rd' (d : Nat) (hd : 2176 ≤ d) (hd' : d + 8 ≤ 2304) :
      (VG.Proof.CmacAes.Stream.AArch64.zeroCv s₄.mem St).readW (S + BitVec.ofNat 64 d) 64 = s₁.mem.readW (S + BitVec.ofNat 64 d) 64 := by
    have c := Region.contains_self (S + BitVec.ofNat 64 d) 8
    rw [fz.readW c (fun r hr => dSv r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; simp [hr]) d hd hd') (by decide),
      f₄.readW c (fun r hr => dSv r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl <;> simp) d hd hd') (by decide), m₃,
      f₂.readW c (fun r hr => dSv r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl <;> simp) d hd hd') (by decide)]
  obtain ⟨sv₁, sv₂, sv₃, sv₄⟩ := VG.Proof.CmacAes.Stream.AArch64.initSaved_read s₀ S
  have m₁ := h₁.mem
  -- The state, outside what the last block writes.
  have dSt (d n : Nat) (hd : d + n ≤ 272) (r : Region) (hr : r ∈ [⟨St + BitVec.ofNat 64 272, 16⟩]) :
      (⟨St + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r := by
    simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint St (by omega) (by omega) (by omega)
  have hRb : 16 * (Spec.Aes.rounds (KL / 4) + 1) ≤ 240 := by
    have := hp.klen; simp only [Spec.Aes.rounds]; omega
  refine ⟨⟨fun r hr => ?_, by rw [sp₅, h₄.sp, h₃.sp]⟩, ?_⟩
  · by_cases h19 : r = .x19
    · subst h19; rw [x19₅, rd' 2176 (by decide) (by decide), m₁]; exact sv₁
    by_cases h20 : r = .x20
    · subst h20; rw [x20₅, rd' 2184 (by decide) (by decide), m₁]; exact sv₂
    by_cases h21 : r = .x21
    · subst h21; rw [x21₅, rd' 2192 (by decide) (by decide), m₁]; exact sv₃
    by_cases h30 : r = .x30
    · subst h30; rw [x30₅, rd' 2200 (by decide) (by decide), m₁]; exact sv₄
    have h9 : r ≠ .x9 := by rintro rfl; simp [preserved] at hr
    rw [keep₅ r h19 h20 h21 h30 h9, g₄ r hr h30, h₃.keep r hr h19 h20 h21 h30]
  · show Spec.Cmac.Repr s₅.mem (s₀.gpr .x0) (Spec.Aes.bytesAt s₀.mem (s₀.gpr .x1) (s₀.gpr .x2).toNat) []
    rw [hp.x0, hp.x1, hp.x2, Proof.Cmac.Stream.repr_iff]
    have hkey : Spec.Aes.bytesAt s₁.mem Kp KL = Spec.Aes.bytesAt s₀.mem Kp KL :=
      Proof.Cmac.bytesAt_frame f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.k_s.sub_right (Offset.sub_base S (by decide))) (by have := hp.wK; omega)
    have hlen : (Spec.Aes.bytesAt s₀.mem Kp KL).length = KL := Proof.Cmac.bytesAt_length _ _ _
    -- The schedule, from the first call on.
    have sch : ∀ {d n : Nat}, d + n ≤ 240 → Spec.Aes.bytesAt s₅.mem (St + BitVec.ofNat 64 d) n =
        Spec.Aes.bytesAt s₂.mem (St + BitVec.ofNat 64 d) n := fun {d n} hd => by
      rw [m₅, Proof.Cmac.bytesAt_frame fz (dSt d n (by omega)) (by omega),
        Proof.Cmac.bytesAt_frame f₄ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact Offset.disjoint St (by omega) (by omega) (by omega)
          · exact (hp.st_s.sub_left (Offset.sub_base St (by omega))).sub_right (Region.sub_prefix (by decide)))
          (by omega), m₃]
    have hsch : Spec.Aes.bytesAt s₂.mem St (16 * (Spec.Aes.rounds (KL / 4) + 1)) =
        Spec.Aes.expandKey (Spec.Aes.bytesAt s₀.mem Kp KL) := by rw [h₂.out, hkey]
    refine ⟨⟨by rw [hlen]; exact hp.klen, ?_, ?_⟩, ?_, by simp [Proof.Cmac.Stream.held_zero, Spec.Aes.bytesAt]⟩
    · rw [hlen]
      have := sch (d := 0) (n := 16 * (Spec.Aes.rounds (KL / 4) + 1)) (by omega)
      rw [k0] at this; rw [this, hsch]
    · have e : Spec.Aes.bytesAt s₅.mem (St + 240) 32 = Spec.Aes.bytesAt s₄.mem (St + 240) 32 := by
        rw [m₅]; exact Proof.Cmac.bytesAt_frame fz (dSt 240 32 (by decide)) (by decide)
      rw [e]
      refine h₄.out.trans ?_
      rw [m₃, show KL / 4 + 6 = Spec.Aes.rounds (KL / 4) from rfl, hsch]
      simp only [Spec.Cmac.aes, hlen]
    · rw [m₅, VG.Proof.CmacAes.Stream.AArch64.zeroCv_eq]; exact (Proof.Cmac.zero2_bytes _ _).trans rfl

/-! ## Constant time -/

/-- What the call of `vg_aes_expand_key_scratch` leaves, for `initMid`. -/
structure IAfter (s₀ : State) (St S : Addr) (KL : Nat) (s : State) : Prop where
  x19 : s.gpr .x19 = St
  x20 : s.gpr .x20 = S
  x21 : s.gpr .x21 = BitVec.ofNat 64 (KL / 4 + 6)
  sp : s.sp = s₀.sp
  keep : ∀ r ∈ preserved, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x30 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem ek_after (v : Ctr32Impl) {s₀ s : State} {St Kp S : Addr} {KL : Nat} (h : VG.Proof.CmacAes.Stream.AArch64.IMid₁ s₀ St Kp S KL s) :
    WP isa (.call v.expand.name v.expand.code) s (VG.Proof.CmacAes.Stream.AArch64.IAfter s₀ St S KL) :=
  WP.mono (VG.Proof.CmacAes.Stream.AArch64.ek_call v h.args) fun _ h₂ =>
    ⟨by rw [h₂.saved _ (by simp [preserved]) (by decide), h.x19],
      by rw [h₂.saved _ (by simp [preserved]) (by decide), h.x20],
      by rw [h₂.saved _ (by simp [preserved]) (by decide), h.x21], by rw [h₂.sp, h.sp],
      fun r hr a b c d => by rw [h₂.saved r hr d, h.other r hr a b c], by rw [h₂.rd, h.rd], by rw [h₂.wr, h.wr]⟩

theorem init_rel (v : Ctr32Impl) {s₀ s₀' : State} (h0 : initAArch64.pre s₀) (h0' : initAArch64.pre s₀')
    (hq : initAArch64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (init v.expand v.callee v.suffix) fun _ _ => True := by
  obtain ⟨q0, q1, q2, q3, q4⟩ := hq
  have hp := IPre.of h0
  have hp' : VG.Proof.CmacAes.Stream.AArch64.IPre s₀' (s₀.gpr .x0) (s₀.gpr .x1) (s₀.gpr .x3) (s₀.gpr .x2).toNat := by
    rw [q0, q1, q2, q3]; exact IPre.of h0'
  generalize s₀.gpr .x0 = St at hp hp'
  generalize s₀.gpr .x1 = Kp at hp hp'
  generalize s₀.gpr .x3 = S at hp hp'
  generalize (s₀.gpr .x2).toNat = KL at hp hp'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3]) (.block initPre) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.x19, .x20, .x21]) (.block initMid) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ h, (taint.check (Taint.ofRegs [.x19, .x20]) (.block initPost) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine agree_of q4 fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption) hA).wp
    (F₁ := VG.Proof.CmacAes.Stream.AArch64.IMid₁ s₀ St Kp S KL) (F₂ := VG.Proof.CmacAes.Stream.AArch64.IMid₁ s₀' St Kp S KL) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨VG.Proof.CmacAes.Stream.AArch64.initPre_wp hp, VG.Proof.CmacAes.Stream.AArch64.initPre_wp hp'⟩
  have e := (VG.Proof.CmacAes.Stream.AArch64.ek_rel v (P := fun a b => VG.Proof.CmacAes.Stream.AArch64.IMid₁ s₀ St Kp S KL a ∧ VG.Proof.CmacAes.Stream.AArch64.IMid₁ s₀' St Kp S KL b)
    fun a b h => ⟨h.1.args, h.2.args, by rw [h.1.sp, h.2.sp, q4]⟩).wp
    (F₁ := VG.Proof.CmacAes.Stream.AArch64.IAfter s₀ St S KL) (F₂ := VG.Proof.CmacAes.Stream.AArch64.IAfter s₀' St S KL) fun a b h => ⟨VG.Proof.CmacAes.Stream.AArch64.ek_after v h.1, VG.Proof.CmacAes.Stream.AArch64.ek_after v h.2⟩
  have m := (RelCT.taint (A := taint) (P := fun a b => VG.Proof.CmacAes.Stream.AArch64.IAfter s₀ St S KL a ∧ VG.Proof.CmacAes.Stream.AArch64.IAfter s₀' St S KL b) _
    (fun a b h => by
      refine agree_of (by rw [h.1.sp, h.2.sp, q4]) fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h.1.x19, h.2.x19]
      · rw [h.1.x20, h.2.x20]
      · rw [h.1.x21, h.2.x21]) hB).wp
    (F₁ := fun (s : State) => ∃ m, VG.Proof.CmacAes.Stream.AArch64.IMid₂ s₀ St S KL m s) (F₂ := fun (s : State) => ∃ m, VG.Proof.CmacAes.Stream.AArch64.IMid₂ s₀' St S KL m s)
    fun a b h => ⟨WP.mono (VG.Proof.CmacAes.Stream.AArch64.initMid_wp hp h.1.x19 h.1.x20 h.1.x21 h.1.sp h.1.rd h.1.wr h.1.keep)
        fun _ h => ⟨_, h⟩,
      WP.mono (VG.Proof.CmacAes.Stream.AArch64.initMid_wp hp' h.2.x19 h.2.x20 h.2.x21 h.2.sp h.2.rd h.2.wr h.2.keep) fun _ h => ⟨_, h⟩⟩
  have sk := (VG.Proof.CmacAes.Stream.AArch64.sub_rel v ("vg_cmac_aes_subkeys" ++ v.suffix)
    (P := fun a b => (∃ m, VG.Proof.CmacAes.Stream.AArch64.IMid₂ s₀ St S KL m a) ∧ ∃ m, VG.Proof.CmacAes.Stream.AArch64.IMid₂ s₀' St S KL m b)
    fun a b ⟨⟨_, h₁⟩, ⟨_, h₂⟩⟩ => ⟨h₁.args, h₂.args, by rw [h₁.sp, h₂.sp, q4]⟩).wp
    (F₁ := fun (s : State) => s.gpr .x19 = St ∧ s.gpr .x20 = S ∧ s.sp = s₀.sp)
    (F₂ := fun (s : State) => s.gpr .x19 = St ∧ s.gpr .x20 = S ∧ s.sp = s₀'.sp)
    fun a b ⟨⟨_, h₁⟩, ⟨_, h₂⟩⟩ =>
      ⟨WP.mono (VG.Proof.CmacAes.Stream.AArch64.sub_call v _ h₁.args) fun _ h => ⟨by rw [h.saved _ (by simp [preserved]) (by decide), h₁.x19],
          by rw [h.saved _ (by simp [preserved]) (by decide), h₁.x20], by rw [h.sp, h₁.sp]⟩,
        WP.mono (VG.Proof.CmacAes.Stream.AArch64.sub_call v _ h₂.args) fun _ h => ⟨by rw [h.saved _ (by simp [preserved]) (by decide), h₂.x19],
          by rw [h.saved _ (by simp [preserved]) (by decide), h₂.x20], by rw [h.sp, h₂.sp]⟩⟩
  have p := RelCT.taint (A := taint)
    (P := fun a b => (a.gpr .x19 = St ∧ a.gpr .x20 = S ∧ a.sp = s₀.sp) ∧
      b.gpr .x19 = St ∧ b.gpr .x20 = S ∧ b.sp = s₀'.sp) _
    (fun a b h => by
      refine agree_of (by rw [h.1.2.2, h.2.2.2, q4]) fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.1, h.2.1]
      · rw [h.1.2.1, h.2.2.1]) hC
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((e.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((m.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((sk.mono (fun _ _ h => h) fun _ _ h => h.2).seq p)))

theorem init_ct (v : Ctr32Impl) :
    ConstantTime isa initAArch64.pre initAArch64.pub (init v.expand v.callee v.suffix) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (VG.Proof.CmacAes.Stream.AArch64.init_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.Stream.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.Stream.AArch64.Verified`. -/
section

section

/-!
# Streaming AES-CMAC on AArch64: `vg_cmac_aes_absorb` is constant time

Two runs from states that agree on the public arguments are related piece by
piece (`RelCT`): the taint analysis covers the code between the calls, from
the registers the correctness proof pins to values of the public arguments
(`AMid₁`, `AAfter₁`, `AMid₂`, `AAfter₂`), and each call of
`vg_cmac_aes_update` is constant time by its own proof (`upd_rel`).
-/

namespace VG.Proof.CmacAes.Stream.AArch64

open VG VG.AArch64 VG.Impl.CmacAes.Stream.AArch64
open VG.Proof.Aes.AArch64 (Ctr32Impl)
open VG.Proof.CmacAes.AArch64 (agree_of)

/-- What the first call leaves, for `chain2`. -/
structure AAfter₁ (s₀ : State) (St D S : Addr) (L : Nat) (s : State) : Prop where
  x19 : s.gpr .x19 = St
  x20 : s.gpr .x20 = s₀.gpr .x1
  x21 : s.gpr .x21 = D + BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.AArch64.fOf (s₀.gpr .x2).toNat L)
  x22 : s.gpr .x22 = BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.AArch64.leftOf (s₀.gpr .x2).toNat L)
  x23 : s.gpr .x23 = S
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem call1_after (v : Proof.CmacAes.AArch64.UpdateImpl) {s₀ s : State} {St D S : Addr} {L R : Nat}
    (h : VG.Proof.CmacAes.Stream.AArch64.AMid₁ s₀ St D S L R s) :
    WP isa (.call v.callee.name v.callee.code) s
      (VG.Proof.CmacAes.Stream.AArch64.AAfter₁ s₀ St D S L) :=
  WP.mono (VG.Proof.CmacAes.Stream.AArch64.upd_call v _ h.args) fun _ h₆ =>
    ⟨by rw [h₆.saved .x19 (by simp [preserved]) (by decide), h.x19],
      by rw [h₆.saved .x20 (by simp [preserved]) (by decide), h.x20],
      by rw [h₆.saved .x21 (by simp [preserved]) (by decide), h.x21],
      by rw [h₆.saved .x22 (by simp [preserved]) (by decide), h.x22],
      by rw [h₆.saved .x23 (by simp [preserved]) (by decide), h.x23],
      by rw [h₆.sp, h.sp], by rw [h₆.rd, h.rd], by rw [h₆.wr, h.wr]⟩

/-- What `chain2` leaves, for the second call. -/
structure AMid₂ (s₀ : State) (St D S : Addr) (L R : Nat) (s : State) : Prop where
  args : VG.Proof.CmacAes.Stream.AArch64.UArgs s St (St + BitVec.ofNat 64 272) (D + BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.AArch64.fOf (s₀.gpr .x2).toNat L)) S R
    (VG.Proof.CmacAes.Stream.AArch64.nbOf (s₀.gpr .x2).toNat L)
  x19 : s.gpr .x19 = St
  x24 : s.gpr .x24 = BitVec.ofNat 64 (16 * VG.Proof.CmacAes.Stream.AArch64.nbOf (s₀.gpr .x2).toNat L)
  x21 : s.gpr .x21 = D + BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.AArch64.fOf (s₀.gpr .x2).toNat L)
  x22 : s.gpr .x22 = BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.AArch64.leftOf (s₀.gpr .x2).toNat L)
  x23 : s.gpr .x23 = S
  sp : s.sp = s₀.sp

theorem chain2_mid {s₀ s : State} {St D S : Addr} {L R : Nat} (hp : VG.Proof.CmacAes.Stream.AArch64.APre s₀ St D S L R)
    (h : VG.Proof.CmacAes.Stream.AArch64.AAfter₁ s₀ St D S L s) : WP isa chain2 s (VG.Proof.CmacAes.Stream.AArch64.AMid₂ s₀ St D S L R) := by
  obtain ⟨c, hc⟩ : ∃ c, (s₀.gpr .x2).toNat = c := ⟨_, rfl⟩
  have hL := hp.lt
  have ⟨hfL, _⟩ := VG.Proof.CmacAes.Stream.AArch64.f_le c L
  have hsum := VG.Proof.CmacAes.Stream.AArch64.nb_le c L
  obtain ⟨x19₆, x20₆, x21₆, x22₆, x23₆, sp₆, rd₆, wr₆⟩ := h
  rw [hc] at x21₆ x22₆
  refine WP.mono (VG.Proof.CmacAes.Stream.AArch64.chain2_wp (x := VG.Proof.CmacAes.Stream.AArch64.leftOf c L) (by unfold VG.Proof.CmacAes.Stream.AArch64.leftOf; omega) x22₆) fun s₇ h₇ => ?_
  obtain ⟨x24₇, x4₇, x0₇, x1₇, x2₇, x3₇, x5₇, sv₇, sp₇, -, rd₇, wr₇⟩ := h₇
  have hnb : (if VG.Proof.CmacAes.Stream.AArch64.leftOf c L = 0 then 0 else (VG.Proof.CmacAes.Stream.AArch64.leftOf c L - 1) / 16) = VG.Proof.CmacAes.Stream.AArch64.nbOf c L := rfl
  rw [hnb] at x24₇ x4₇
  have c272 : Region.Sub ⟨St + BitVec.ofNat 64 272, 16⟩ ⟨St, 304⟩ := Offset.sub_base St (by decide)
  subst hc
  have dD : Region.Sub ⟨D + BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.AArch64.fOf (s₀.gpr .x2).toNat L), 16 * VG.Proof.CmacAes.Stream.AArch64.nbOf (s₀.gpr .x2).toNat L⟩
      ⟨D, L⟩ := Offset.sub_base D (by omega)
  refine ⟨hp.uargs (s := s₇) (Dd := D + BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.AArch64.fOf (s₀.gpr .x2).toNat L))
    (n := VG.Proof.CmacAes.Stream.AArch64.nbOf (s₀.gpr .x2).toNat L)
    (by rw [x0₇, x19₆]) (by rw [x1₇, x20₆]) (by rw [x2₇, x19₆]) (by rw [x3₇, x21₆]) x4₇
    (by rw [x5₇, x23₆]) (by rw [rd₇, rd₆]) (by rw [wr₇, wr₆]) (by omega) ((hp.st_d.sub_left c272).symm.sub_left dD)
    ((hp.d_s.sub_left dD).sub_right (Region.sub_prefix (by decide)))
    (by
      by_cases h0 : VG.Proof.CmacAes.Stream.AArch64.nbOf (s₀.gpr .x2).toNat L = 0
      · rw [h0]; have := (D + BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.AArch64.fOf (s₀.gpr .x2).toNat L)).isLt; omega
      · have := hp.wD; rw [VG.Proof.CmacAes.Stream.AArch64.toNat_add_lt D hp.wD (by omega)]; omega)
    ⟨⟨D, L⟩, by simp, VG.Proof.CmacAes.Stream.AArch64.fOf (s₀.gpr .x2).toNat L, rfl, by simp; omega⟩,
    by rw [sv₇ .x19 (by simp [preserved]) (by decide), x19₆], x24₇,
    by rw [sv₇ .x21 (by simp [preserved]) (by decide), x21₆],
    by rw [sv₇ .x22 (by simp [preserved]) (by decide), x22₆],
    by rw [sv₇ .x23 (by simp [preserved]) (by decide), x23₆], by rw [sp₇, sp₆]⟩

/-- What the second call leaves, for `absorbPost`. -/
structure AAfter₂ (s₀ : State) (St D S : Addr) (L : Nat) (s : State) : Prop where
  x19 : s.gpr .x19 = St
  x24 : s.gpr .x24 = BitVec.ofNat 64 (16 * VG.Proof.CmacAes.Stream.AArch64.nbOf (s₀.gpr .x2).toNat L)
  x21 : s.gpr .x21 = D + BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.AArch64.fOf (s₀.gpr .x2).toNat L)
  x22 : s.gpr .x22 = BitVec.ofNat 64 (VG.Proof.CmacAes.Stream.AArch64.leftOf (s₀.gpr .x2).toNat L)
  x23 : s.gpr .x23 = S
  sp : s.sp = s₀.sp

theorem call2_after (v : Proof.CmacAes.AArch64.UpdateImpl) {s₀ s : State} {St D S : Addr} {L R : Nat}
    (h : VG.Proof.CmacAes.Stream.AArch64.AMid₂ s₀ St D S L R s) :
    WP isa (.call v.callee.name v.callee.code) s
      (VG.Proof.CmacAes.Stream.AArch64.AAfter₂ s₀ St D S L) :=
  WP.mono (VG.Proof.CmacAes.Stream.AArch64.upd_call v _ h.args) fun _ h₈ =>
    ⟨by rw [h₈.saved .x19 (by simp [preserved]) (by decide), h.x19],
      by rw [h₈.saved .x24 (by simp [preserved]) (by decide), h.x24],
      by rw [h₈.saved .x21 (by simp [preserved]) (by decide), h.x21],
      by rw [h₈.saved .x22 (by simp [preserved]) (by decide), h.x22],
      by rw [h₈.saved .x23 (by simp [preserved]) (by decide), h.x23], by rw [h₈.sp, h.sp]⟩

theorem absorb_rel (v : Proof.CmacAes.AArch64.UpdateImpl) {s₀ s₀' : State} (h0 : absorbAArch64.pre s₀) (h0' : absorbAArch64.pre s₀')
    (hq : absorbAArch64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (absorb v.callee) fun _ _ => True := by
  obtain ⟨q0, q1, q2, q3, q4, q5, q6⟩ := hq
  have hp := APre.of h0
  have hp' : VG.Proof.CmacAes.Stream.AArch64.APre s₀' (s₀.gpr .x0) (s₀.gpr .x3) (s₀.gpr .x5) (s₀.gpr .x4).toNat (s₀.gpr .x1).toNat := by
    rw [q0, q1, q3, q4, q5]; exact APre.of h0'
  generalize s₀.gpr .x0 = St at hp hp'
  generalize s₀.gpr .x3 = D at hp hp'
  generalize s₀.gpr .x5 = S at hp hp'
  generalize (s₀.gpr .x4).toNat = L at hp hp'
  generalize (s₀.gpr .x1).toNat = R at hp hp'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5]) absorbPre h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x22, .x23]) chain2 h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ h, (taint.check (Taint.ofRegs [.x19, .x21, .x22, .x23, .x24]) absorbPost h).isSome =
      true := ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine agree_of q6 fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption) hA).wp
    (F₁ := VG.Proof.CmacAes.Stream.AArch64.AMid₁ s₀ St D S L R) (F₂ := VG.Proof.CmacAes.Stream.AArch64.AMid₁ s₀' St D S L R) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨VG.Proof.CmacAes.Stream.AArch64.absorbPre_wp hp, VG.Proof.CmacAes.Stream.AArch64.absorbPre_wp hp'⟩
  have c₁ := (VG.Proof.CmacAes.Stream.AArch64.upd_rel v _ (P := fun a b => VG.Proof.CmacAes.Stream.AArch64.AMid₁ s₀ St D S L R a ∧ VG.Proof.CmacAes.Stream.AArch64.AMid₁ s₀' St D S L R b)
    fun a b h => ⟨h.1.args, by rw [q2]; exact h.2.args, by rw [h.1.sp, h.2.sp, q6]⟩).wp
    (F₁ := VG.Proof.CmacAes.Stream.AArch64.AAfter₁ s₀ St D S L) (F₂ := VG.Proof.CmacAes.Stream.AArch64.AAfter₁ s₀' St D S L) fun a b h => ⟨VG.Proof.CmacAes.Stream.AArch64.call1_after v h.1, VG.Proof.CmacAes.Stream.AArch64.call1_after v h.2⟩
  have m := (RelCT.taint (A := taint) (P := fun a b => VG.Proof.CmacAes.Stream.AArch64.AAfter₁ s₀ St D S L a ∧ VG.Proof.CmacAes.Stream.AArch64.AAfter₁ s₀' St D S L b) _
    (fun a b h => by
      refine agree_of (by rw [h.1.sp, h.2.sp, q6]) fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [h.1.x19, h.2.x19]
      · rw [h.1.x20, h.2.x20, q1]
      · rw [h.1.x21, h.2.x21, q2]
      · rw [h.1.x22, h.2.x22, q2]
      · rw [h.1.x23, h.2.x23]) hB).wp
    (F₁ := VG.Proof.CmacAes.Stream.AArch64.AMid₂ s₀ St D S L R) (F₂ := VG.Proof.CmacAes.Stream.AArch64.AMid₂ s₀' St D S L R) fun a b h => ⟨VG.Proof.CmacAes.Stream.AArch64.chain2_mid hp h.1, VG.Proof.CmacAes.Stream.AArch64.chain2_mid hp' h.2⟩
  have c₂ := (VG.Proof.CmacAes.Stream.AArch64.upd_rel v _ (P := fun a b => VG.Proof.CmacAes.Stream.AArch64.AMid₂ s₀ St D S L R a ∧ VG.Proof.CmacAes.Stream.AArch64.AMid₂ s₀' St D S L R b)
    fun a b h => ⟨h.1.args, by rw [q2]; exact h.2.args, by rw [h.1.sp, h.2.sp, q6]⟩).wp
    (F₁ := VG.Proof.CmacAes.Stream.AArch64.AAfter₂ s₀ St D S L) (F₂ := VG.Proof.CmacAes.Stream.AArch64.AAfter₂ s₀' St D S L) fun a b h =>
      ⟨VG.Proof.CmacAes.Stream.AArch64.call2_after v h.1, VG.Proof.CmacAes.Stream.AArch64.call2_after v h.2⟩
  have p := RelCT.taint (A := taint) (P := fun a b => VG.Proof.CmacAes.Stream.AArch64.AAfter₂ s₀ St D S L a ∧ VG.Proof.CmacAes.Stream.AArch64.AAfter₂ s₀' St D S L b) _
    (fun a b h => by
      refine agree_of (by rw [h.1.sp, h.2.sp, q6]) fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [h.1.x19, h.2.x19]
      · rw [h.1.x21, h.2.x21, q2]
      · rw [h.1.x22, h.2.x22, q2]
      · rw [h.1.x23, h.2.x23]
      · rw [h.1.x24, h.2.x24, q2]) hC
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((c₁.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((m.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((c₂.mono (fun _ _ h => h) fun _ _ h => h.2).seq p)))

theorem absorb_ct (v : Proof.CmacAes.AArch64.UpdateImpl) :
    ConstantTime isa absorbAArch64.pre absorbAArch64.pub (absorb v.callee) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (VG.Proof.CmacAes.Stream.AArch64.absorb_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.Stream.AArch64

end

/-!
# Streaming AES-CMAC on AArch64: `Verified`

Correctness and constant time (for any implementation `v` of AES), a state
satisfying each precondition, and the shared contracts of
`Spec/Cmac/Contract.lean` (with no stack: the calls keep the return address in
`x30`, which each function saves in the scratch buffer).
-/

namespace VG.Proof.CmacAes.Stream.AArch64

open VG VG.AArch64 VG.Impl.CmacAes.Stream.AArch64
open VG.Proof.Aes.AArch64 (Ctr32Impl)
open VG.Proof.CmacAes.AArch64 (update_keepsV subkeys_keepsV finalize_keepsV)

theorem init_keepsV (v : Ctr32Impl) : (init v.expand v.callee v.suffix).allInstrs keepsV = true := by
  simp only [init, Code.allInstrs, v.expandKeepsV, subkeys_keepsV v]; decide +kernel

theorem absorb_keepsV (v : Proof.CmacAes.AArch64.UpdateImpl) : (absorb v.callee).allInstrs keepsV = true := by
  simp only [absorb, absorbPre, absorbPost, held, clamp, fill, copy, chain1, chain2, Code.allInstrs,
    v.keepsV]
  decide +kernel

theorem finish_keepsV (v : Ctr32Impl) : (finish v.callee v.suffix).allInstrs keepsV = true := by
  simp only [finish, finPre, lastLen, Code.allInstrs, finalize_keepsV v]; decide +kernel

theorem init_correct (v : Ctr32Impl) (s : State) (hs : initAArch64.pre s) :
    ∃ t s', Exec isa (init v.expand v.callee v.suffix) s t s' ∧ abiPreserved s s' ∧ initAArch64.post s s' :=
  WP.withPreservedV (VG.Proof.CmacAes.Stream.AArch64.init_wp v hs) (VG.Proof.CmacAes.Stream.AArch64.init_keepsV v)

theorem absorb_correct (v : Proof.CmacAes.AArch64.UpdateImpl) (s : State) (hs : absorbAArch64.pre s) :
    ∃ t s', Exec isa (absorb v.callee) s t s' ∧ abiPreserved s s' ∧ absorbAArch64.post s s' :=
  WP.withPreservedV (VG.Proof.CmacAes.Stream.AArch64.absorb_wp v hs) (VG.Proof.CmacAes.Stream.AArch64.absorb_keepsV v)

theorem finish_correct (v : Ctr32Impl) (s : State) (hs : finishAArch64.pre s) :
    ∃ t s', Exec isa (finish v.callee v.suffix) s t s' ∧ abiPreserved s s' ∧ finishAArch64.post s s' :=
  WP.withPreservedV (VG.Proof.CmacAes.Stream.AArch64.finish_wp v hs) (VG.Proof.CmacAes.Stream.AArch64.finish_keepsV v)

/-- A state satisfying `vg_cmac_aes_init`'s precondition. -/
def initSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x3000 | .x2 => 16 | .x3 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x3000, 16⟩]
  wr := [⟨0x1000, 304⟩, ⟨0x4000, 2304⟩]

theorem init_verified (v : Ctr32Impl) :
    Verified AArch64.target (init v.expand v.callee v.suffix) (initScratchContract AArch64.abi) :=
  Verified.of_correct (VG.Proof.CmacAes.Stream.AArch64.init_correct v) (VG.Proof.CmacAes.Stream.AArch64.init_ct v) (by
    sig_implies [initScratchContract, initScratchSig, Spec.Cmac.aesInitPre, Spec.Cmac.aesInitPost, VG.Proof.CmacAes.Stream.AArch64.initAArch64, AArch64.abi,
      AArch64.argRegs] [initSat] using VG.Proof.CmacAes.Stream.AArch64.initSat)

/-- A state satisfying `vg_cmac_aes_absorb`'s precondition (with no data). -/
def absorbSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x3 => 0x3000 | .x5 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x3000, 0⟩]
  wr := [⟨0x1000, 304⟩, ⟨0x4000, 2304⟩]

theorem absorb_verified (v : Proof.CmacAes.AArch64.UpdateImpl) :
    Verified AArch64.target (absorb v.callee) (absorbScratchContract AArch64.abi) :=
  Verified.of_correct (VG.Proof.CmacAes.Stream.AArch64.absorb_correct v) (VG.Proof.CmacAes.Stream.AArch64.absorb_ct v) (by
    sig_implies [absorbScratchContract, absorbScratchSig, Spec.Cmac.aesAbsorbPre, Spec.Cmac.aesAbsorbPost, VG.Proof.CmacAes.Stream.AArch64.absorbAArch64, AArch64.abi,
      AArch64.argRegs] [absorbSat] using VG.Proof.CmacAes.Stream.AArch64.absorbSat)

/-- A state satisfying `vg_cmac_aes_finish`'s precondition. -/
def finishSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x3 => 0x2000 | .x4 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 304⟩, ⟨0x2000, 16⟩, ⟨0x4000, 2304⟩]

theorem finish_verified (v : Ctr32Impl) :
    Verified AArch64.target (finish v.callee v.suffix) (finishScratchContract AArch64.abi) :=
  Verified.of_correct (VG.Proof.CmacAes.Stream.AArch64.finish_correct v) (VG.Proof.CmacAes.Stream.AArch64.finish_ct v) (by
    sig_implies [finishScratchContract, finishScratchSig, Spec.Cmac.aesFinishPre, Spec.Cmac.aesFinishPost, VG.Proof.CmacAes.Stream.AArch64.finishAArch64, AArch64.abi,
      AArch64.argRegs] [finishSat] using VG.Proof.CmacAes.Stream.AArch64.finishSat)

end VG.Proof.CmacAes.Stream.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacAes.Stream.AArch64.Frame`. -/
section

/-!
# Streaming AES-CMAC on AArch64, with its working space on the stack

The streaming functions run their code, proved with the working space as an
argument (`Verified.lean`), in a frame of 2304 bytes that allocates it
(`Verified.stackScratch`). Their code uses no other stack: their calls keep
the return address in `x30`, which they save in the working space.
-/

namespace VG.Proof.CmacAes.Stream.AArch64

open VG VG.AArch64 VG.Impl.CmacAes.Stream.AArch64
open VG.Proof.Aes.AArch64 (Ctr32Impl)

/-- A state satisfying `vg_cmac_aes_init`'s precondition, without the
working space. -/
def initFrameSat : State := { VG.Proof.CmacAes.Stream.AArch64.initSat with
                                           wr := [⟨0x1000, 304⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Cmac.aesInitContract AArch64.abi 2304).pre s := by
  implies_sat [Spec.Cmac.aesInitContract, Spec.Cmac.aesInitSig, Spec.Cmac.aesInitPre,
    Spec.Cmac.aesInitPost, AArch64.abi, AArch64.argRegs] [initFrameSat, initSat] using VG.Proof.CmacAes.Stream.AArch64.initFrameSat

/-- A state satisfying `vg_cmac_aes_absorb`'s precondition, without the
working space (and with no data). -/
def absorbFrameSat : State := { VG.Proof.CmacAes.Stream.AArch64.absorbSat with
                                               wr := [⟨0x1000, 304⟩] }

theorem absorbFrameSat_pre : ∃ s, (Spec.Cmac.aesAbsorbContract AArch64.abi 2304).pre s := by
  implies_sat [Spec.Cmac.aesAbsorbContract, Spec.Cmac.aesAbsorbSig, Spec.Cmac.aesAbsorbPre,
    Spec.Cmac.aesAbsorbPost, AArch64.abi, AArch64.argRegs] [absorbFrameSat, absorbSat]
    using VG.Proof.CmacAes.Stream.AArch64.absorbFrameSat

/-- A state satisfying `vg_cmac_aes_finish`'s precondition, without the
working space. -/
def finishFrameSat : State := { VG.Proof.CmacAes.Stream.AArch64.finishSat with
                                               wr := [⟨0x1000, 304⟩, ⟨0x2000, 16⟩] }

theorem finishFrameSat_pre : ∃ s, (Spec.Cmac.aesFinishContract AArch64.abi 2304).pre s := by
  implies_sat [Spec.Cmac.aesFinishContract, Spec.Cmac.aesFinishSig, Spec.Cmac.aesFinishPre,
    Spec.Cmac.aesFinishPost, AArch64.abi, AArch64.argRegs] [finishFrameSat, finishSat]
    using VG.Proof.CmacAes.Stream.AArch64.finishFrameSat

theorem init_framed (v : Ctr32Impl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackScratch 2304 .x3 (init v.expand v.callee v.suffix))
      (Spec.Cmac.aesInitContract AArch64.abi 2304) :=
  AArch64.Verified.stackScratch (sig := Spec.Cmac.aesInitSig) (nm := "scratch") (e := .u64)
    (n := 288) (pre := Spec.Cmac.aesInitPre AArch64.abi.ptrBits)
    (post := Spec.Cmac.aesInitPost AArch64.abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 2304) (VG.Proof.CmacAes.Stream.AArch64.init_verified v) (by decide) (by decide) VG.Proof.CmacAes.Stream.AArch64.initFrameSat_pre

theorem absorb_framed (v : Proof.CmacAes.AArch64.UpdateImpl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackScratch 2304 .x5 (absorb v.callee))
      (Spec.Cmac.aesAbsorbContract AArch64.abi 2304) :=
  AArch64.Verified.stackScratch (sig := Spec.Cmac.aesAbsorbSig) (nm := "scratch") (e := .u64)
    (n := 288) (pre := Spec.Cmac.aesAbsorbPre AArch64.abi.ptrBits)
    (post := Spec.Cmac.aesAbsorbPost AArch64.abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 2304) (VG.Proof.CmacAes.Stream.AArch64.absorb_verified v) (by decide) (by decide) VG.Proof.CmacAes.Stream.AArch64.absorbFrameSat_pre

theorem finish_framed (v : Ctr32Impl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackScratch 2304 .x4 (finish v.callee v.suffix))
      (Spec.Cmac.aesFinishContract AArch64.abi 2304) :=
  AArch64.Verified.stackScratch (sig := Spec.Cmac.aesFinishSig) (nm := "scratch") (e := .u64)
    (n := 288) (pre := Spec.Cmac.aesFinishPre AArch64.abi.ptrBits)
    (post := Spec.Cmac.aesFinishPost AArch64.abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 2304) (VG.Proof.CmacAes.Stream.AArch64.finish_verified v) (by decide) (by decide) VG.Proof.CmacAes.Stream.AArch64.finishFrameSat_pre

end VG.Proof.CmacAes.Stream.AArch64

end
