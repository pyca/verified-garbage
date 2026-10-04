import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.CmacAes.AArch64.Variant
import VerifiedGarbage.Proof.CmacAes.AArch64.Verified
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Impl.CmacAes.Stream.AArch64

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

A call of each function the streaming functions call (`vg_aes_expand_key`,
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

theorem UArgs.pre {s : State} {W C D S : Addr} {R n : Nat} (h : UArgs s W C D S R n) :
    updateAArch64.pre (s.callEntry.withRegions [⟨W, 240⟩, ⟨D, 16 * n⟩] [⟨C, 16⟩, ⟨S, 2176⟩]) := by
  have hR := toNat_rounds h.rounds
  have hN := toNat_ofNat (n := n) (by have := h.hn; omega)
  simp only [updateAArch64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, callEntry_x4, callEntry_x5,
    h.x0, h.x1, h.x2, h.x3, h.x4, h.x5, hR, hN]
  exact ⟨trivial, trivial, h.wc, h.ws, h.dc, h.ds, h.cs, h.wrapC, h.wrapD, h.wrapS, h.rounds⟩

theorem upd_call (v : Proof.CmacAes.AArch64.UpdateImpl) (nm : String) {s : State} {W C D S : Addr} {R n : Nat}
    (h : UArgs s W C D S R n) :
    WP isa (.call nm v.callee.code) s (UPost s W C D S R n) := by
  have hR := toNat_rounds h.rounds
  have hN := toNat_ofNat (n := n) (by have := h.hn; omega)
  refine WP.call (k := updateAArch64) v.ok h.pre h.reads h.writes ?_ v.noFrames
  intro s' hrd hwr hsp hf hsaved _ hpost
  refine ⟨hrd, hwr, hsp, hsaved, hf, ?_⟩
  simp only [updateAArch64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, callEntry_x4, h.x0, h.x1, h.x2, h.x3, h.x4,
    hR, hN] at hpost
  exact hpost

theorem upd_rel (v : Proof.CmacAes.AArch64.UpdateImpl) (nm : String) {W C D S : Addr} {R n : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → UArgs s₁ W C D S R n ∧ UArgs s₂ W C D S R n ∧ s₁.sp = s₂.sp) :
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

theorem SArgs.pre {s : State} {W K S : Addr} {R : Nat} (h : SArgs s W K S R) :
    subkeysAArch64.pre (s.callEntry.withRegions [⟨W, 240⟩] [⟨K, 32⟩, ⟨S, 2176⟩]) := by
  have hR := toNat_rounds h.rounds
  simp only [subkeysAArch64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, h.x0, h.x1, h.x2, h.x3, hR]
  exact ⟨trivial, trivial, h.wk, h.ws, h.ks, h.wrapK, h.wrapS, h.rounds⟩

theorem sub_call (v : Ctr32Impl) (nm : String) {s : State} {W K S : Addr} {R : Nat}
    (h : SArgs s W K S R) :
    WP isa (.call nm (Impl.CmacAes.AArch64.subkeys v.callee)) s (SPost s W K S R) := by
  have hR := toNat_rounds h.rounds
  refine WP.call (k := subkeysAArch64) (subkeys_correct v) h.pre h.reads h.writes ?_ (subkeys_noFrames v)
  intro s' hrd hwr hsp hf hsaved _ hpost
  refine ⟨hrd, hwr, hsp, hsaved, hf, ?_⟩
  simp only [subkeysAArch64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    callEntry_x0, callEntry_x1, callEntry_x2, h.x0, h.x1, h.x2, hR] at hpost
  exact hpost

theorem sub_rel (v : Ctr32Impl) (nm : String) {W K S : Addr} {R : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → SArgs s₁ W K S R ∧ SArgs s₂ W K S R ∧ s₁.sp = s₂.sp) :
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

theorem FArgs.pre {s : State} {K St P S : Addr} {L R : Nat} (h : FArgs s K St P S L R) :
    finalizeAArch64.pre (s.callEntry.withRegions [⟨K, 272⟩, ⟨P, L⟩] [⟨St, 16⟩, ⟨S, 2176⟩]) := by
  have hR := toNat_rounds h.rounds
  have hL := toNat_ofNat (n := L) (by have := h.len; omega)
  simp only [finalizeAArch64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, callEntry_x4, callEntry_x5,
    h.x0, h.x1, h.x2, h.x3, h.x4, h.x5, hR, hL]
  exact ⟨trivial, trivial, h.kst, h.ks, h.pst, h.ps, h.sts, h.wrapK, h.wrapSt, h.wrapP, h.wrapS,
    h.rounds, h.len⟩

theorem fin_call (v : Ctr32Impl) (nm : String) {s : State} {K St P S : Addr} {L R : Nat}
    (h : FArgs s K St P S L R) :
    WP isa (.call nm (Impl.CmacAes.AArch64.finalize v.callee)) s (FPost s K St P S L R) := by
  have hR := toNat_rounds h.rounds
  have hL := toNat_ofNat (n := L) (by have := h.len; omega)
  refine WP.call (k := finalizeAArch64) (finalize_correct v) h.pre h.reads h.writes ?_
    (finalize_noFrames v)
  intro s' hrd hwr hsp hf hsaved _ hpost
  refine ⟨hrd, hwr, hsp, hsaved, hf, ?_⟩
  simp only [finalizeAArch64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, callEntry_x4, h.x0, h.x1, h.x2, h.x3, h.x4,
    hR, hL] at hpost
  exact hpost

theorem fin_rel (v : Ctr32Impl) (nm : String) {K St Q S : Addr} {L R : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → FArgs s₁ K St Q S L R ∧ FArgs s₂ K St Q S L R ∧ s₁.sp = s₂.sp) :
    RelCT isa P (.call nm (Impl.CmacAes.AArch64.finalize v.callee)) fun _ _ => True := by
  refine RelCT.call (finalize_correct v) (finalize_ct v) [⟨K, 272⟩, ⟨Q, L⟩] [⟨St, 16⟩, ⟨S, 2176⟩]
    fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes⟩
  simp only [finalizeAArch64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, callEntry_x4, callEntry_x5,
    h₁.x0, h₁.x1, h₁.x2, h₁.x3, h₁.x4, h₁.x5, h₂.x0, h₂.x1, h₂.x2, h₂.x3, h₂.x4, h₂.x5, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## `vg_aes_expand_key` -/

/-- What a call of `vg_aes_expand_key` needs: the key `Kp` of `KL` bytes,
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

/-- What a call of `vg_aes_expand_key` leaves. -/
structure EPost (s : State) (Kp W S : Addr) (KL : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r
  frame : Frame [⟨W, 240⟩, ⟨S, 512⟩] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem W (16 * (Spec.Aes.rounds (KL / 4) + 1)) =
    Spec.Aes.expandKey (Spec.Aes.bytesAt s.mem Kp KL)

theorem EArgs.pre {s : State} {Kp W S : Addr} {KL : Nat} (h : EArgs s Kp W S KL) :
    Proof.Aes.expandKeyAArch64.pre (s.callEntry.withRegions [⟨Kp, KL⟩] [⟨W, 240⟩, ⟨S, 512⟩]) := by
  have hK := toNat_ofNat (n := KL) (by rcases h.klen with h | h | h <;> omega)
  simp only [Proof.Aes.expandKeyAArch64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, h.x0, h.x1, h.x2, h.x3, hK]
  exact ⟨trivial, trivial, h.kw, h.ks, h.ws, h.klen⟩

theorem ek_call (v : Ctr32Impl) {s : State} {Kp W S : Addr} {KL : Nat} (h : EArgs s Kp W S KL) :
    WP isa (.call v.expand.name v.expand.code) s (EPost s Kp W S KL) := by
  have hK := toNat_ofNat (n := KL) (by rcases h.klen with h | h | h <;> omega)
  refine WP.call (k := Proof.Aes.expandKeyAArch64) v.expandOk h.pre h.reads h.writes ?_ v.expandNoFrames
  intro s' hrd hwr hsp hf hsaved _ hpost
  refine ⟨hrd, hwr, hsp, hsaved, hf, ?_⟩
  simp only [Proof.Aes.expandKeyAArch64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    callEntry_x0, callEntry_x1, callEntry_x2, h.x0, h.x1, h.x2, hK] at hpost
  exact hpost

theorem ek_rel (v : Ctr32Impl) {Kp W S : Addr} {KL : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → EArgs s₁ Kp W S KL ∧ EArgs s₂ Kp W S KL ∧ s₁.sp = s₂.sp) :
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
  rw [BitVec.toNat_add, and15, BitVec.toNat_sub]
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
  other : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem copy_ok (s : State) {P C : Addr} {L : Nat} (hL : L < 2 ^ 64) (h7 : s.gpr .x7 = P)
    (h6 : s.gpr .x6 = C) (h8 : s.gpr .x8 = BitVec.ofNat 64 L)
    (hr : ∀ i < L, InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < L, InRegions s.wr (C + BitVec.ofNat 64 i) 1)
    (hdis : (⟨P, L⟩ : Region).Disjoint ⟨C, L⟩) :
    WP isa copy s (Copied s C (Spec.Aes.bytesAt s.mem P L)) := by
  by_cases hL0 : L = 0
  · subst hL0
    refine WP.ite true (by rw [eval_zero hL h8]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    exact ⟨by simp [Spec.Aes.bytesAt, writeBytes_nil], fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
  refine WP.ite false (by rw [eval_zero hL h8]; simp [hL0]) (fun h => by cases h) fun _ => ?_
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
  have ev := eval_nonzero (s := t') (x := L - (i + 1)) (by omega) x8''
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
