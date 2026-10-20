module

import VerifiedGarbage.Proof.CmacTripleDes.AArch64.Verified
public import VerifiedGarbage.Proof.Framework.AArch64.Inline
public import VerifiedGarbage.Impl.CmacTripleDes.AArch64
public import VerifiedGarbage.Proof.CmacTripleDes.AArch64.Contract
import VerifiedGarbage.Proof.CmacTripleDes.AArch64.Lit
import VerifiedGarbage.Proof.CmacTripleDes.AArch64.RoundLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.CmacTripleDes.AArch64.Update

/-!
# Streaming TDEA-CMAC on AArch64: the code of `init`, `update` and `finalize`, inline

Each run of the code of `vg_cmac_triple_des_init`, `_update` and `_finalize`
inside the streaming functions, from its contract (`WP.inline`): what it
needs (`…Args`), and what it leaves (`…Post`, in terms of the memory before
it): it changes memory only in its buffers, and keeps the stack pointer and
the registers the ABI preserves.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.AArch64

open VG VG.AArch64
open VG.Proof.CmacTripleDes.AArch64 (updateAArch64 finalizeAArch64 initAArch64 ciphAt)

theorem toNat_ofNat {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-! ## `update` -/

/-- What a run of `update` needs: the key schedule `W`, the chaining value
`C`, `n` blocks at `D` and the working space `S`. -/
structure UArgs (s : State) (W C D S : Addr) (n : Nat) : Prop where
  x0 : s.gpr .x0 = W
  x1 : s.gpr .x1 = C
  x2 : s.gpr .x2 = D
  x3 : s.gpr .x3 = BitVec.ofNat 64 n
  x4 : s.gpr .x4 = S
  hn : 8 * n < 2 ^ 64
  wc : (⟨W, 384⟩ : Region).Disjoint ⟨C, 8⟩
  ws : (⟨W, 384⟩ : Region).Disjoint ⟨S, 640⟩
  dc : (⟨D, 8 * n⟩ : Region).Disjoint ⟨C, 8⟩
  ds : (⟨D, 8 * n⟩ : Region).Disjoint ⟨S, 640⟩
  cs : (⟨C, 8⟩ : Region).Disjoint ⟨S, 640⟩
  wrapC : C.toNat + 8 ≤ 2 ^ 64
  wrapD : D.toNat + 8 * n ≤ 2 ^ 64
  wrapS : S.toNat + 640 ≤ 2 ^ 64
  reads : Covers ([⟨W, 384⟩, ⟨D, 8 * n⟩] ++ [⟨C, 8⟩, ⟨S, 640⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨C, 8⟩, ⟨S, 640⟩] s.wr

/-- What a run of `update` leaves. -/
structure UPost (s : State) (W C D S : Addr) (n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  frame : Frame [⟨C, 8⟩, ⟨S, 640⟩] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem C 8 =
    Spec.Cmac.chain (ciphAt s.mem W) (Spec.Aes.bytesAt s.mem C 8) (Spec.Cmac.blocksAt s.mem D 8 n)

theorem UArgs.pre {s : State} {W C D S : Addr} {n : Nat} (h : UArgs s W C D S n) :
    updateAArch64.pre (s.withRegions [⟨W, 384⟩, ⟨D, 8 * n⟩] [⟨C, 8⟩, ⟨S, 640⟩]) := by
  have hN := toNat_ofNat (n := n) (by have := h.hn; omega)
  simp only [updateAArch64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, h.x0,
    h.x1, h.x2, h.x3, h.x4, hN]
  exact ⟨trivial, trivial, h.wc, h.ws, h.dc, h.ds, h.cs, h.wrapC, h.wrapD, h.wrapS⟩

theorem upd_wp {s : State} {W C D S : Addr} {n : Nat} (h : UArgs s W C D S n) :
    WP isa Impl.CmacTripleDes.AArch64.update s (UPost s W C D S n) := by
  have hN := toNat_ofNat (n := n) (by have := h.hn; omega)
  refine WP.inline (k := updateAArch64) Proof.CmacTripleDes.AArch64.update_correct h.pre h.reads h.writes
    (fun s' hrd hwr ha hf _ hpost => ⟨hrd, hwr, ha.2.1, ha.1, hf, ?_⟩) (by lit_decide)
  simp only [updateAArch64, State.withRegions_gpr, State.withRegions_mem, h.x0, h.x1, h.x2, h.x3,
    hN] at hpost
  exact hpost

/-! ## `finalize` -/

/-- What a run of `finalize` needs: the key schedule and subkeys `K`, the
state `St`, the `L` last bytes at `P` and the working space `S`. -/
structure FArgs (s : State) (K St P S : Addr) (L : Nat) : Prop where
  x0 : s.gpr .x0 = K
  x1 : s.gpr .x1 = St
  x2 : s.gpr .x2 = P
  x3 : s.gpr .x3 = BitVec.ofNat 64 L
  x4 : s.gpr .x4 = S
  len : L ≤ 8
  kst : (⟨K, 400⟩ : Region).Disjoint ⟨St, 8⟩
  ks : (⟨K, 400⟩ : Region).Disjoint ⟨S, 640⟩
  pst : (⟨P, L⟩ : Region).Disjoint ⟨St, 8⟩
  ps : (⟨P, L⟩ : Region).Disjoint ⟨S, 640⟩
  sts : (⟨St, 8⟩ : Region).Disjoint ⟨S, 640⟩
  wrapK : K.toNat + 400 ≤ 2 ^ 64
  wrapSt : St.toNat + 8 ≤ 2 ^ 64
  wrapP : P.toNat + L ≤ 2 ^ 64
  wrapS : S.toNat + 640 ≤ 2 ^ 64
  reads : Covers ([⟨K, 400⟩, ⟨P, L⟩] ++ [⟨St, 8⟩, ⟨S, 640⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨St, 8⟩, ⟨S, 640⟩] s.wr

/-- What a run of `finalize` leaves. -/
structure FPost (s : State) (K St P S : Addr) (L : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  frame : Frame [⟨St, 8⟩, ⟨S, 640⟩] s.mem s'.mem
  out : let ciph := ciphAt s.mem K
    let ks := Spec.Cmac.subkeys ciph 8
    Spec.Aes.bytesAt s.mem (K + 384) 16 = ks.1 ++ ks.2 →
    ∀ msg : List Byte, msg.length % 8 = 0 → (msg = [] ∨ 0 < L) →
      Spec.Aes.bytesAt s.mem St 8 = Spec.Cmac.chain ciph (Spec.Cmac.zeros 8) (Spec.Cmac.blocks 8 msg) →
      Spec.Aes.bytesAt s'.mem St 8 = Spec.Cmac.macFull ciph 8 (msg ++ Spec.Aes.bytesAt s.mem P L)

theorem FArgs.pre {s : State} {K St P S : Addr} {L : Nat} (h : FArgs s K St P S L) :
    finalizeAArch64.pre (s.withRegions [⟨K, 400⟩, ⟨P, L⟩] [⟨St, 8⟩, ⟨S, 640⟩]) := by
  have hL := toNat_ofNat (n := L) (by have := h.len; omega)
  simp only [finalizeAArch64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, h.x0,
    h.x1, h.x2, h.x3, h.x4, hL]
  exact ⟨trivial, trivial, h.kst, h.ks, h.pst, h.ps, h.sts, h.wrapK, h.wrapSt, h.wrapP, h.wrapS, h.len⟩

theorem fin_wp {s : State} {K St P S : Addr} {L : Nat} (h : FArgs s K St P S L) :
    WP isa Impl.CmacTripleDes.AArch64.finalize s (FPost s K St P S L) := by
  have hL := toNat_ofNat (n := L) (by have := h.len; omega)
  refine WP.inline (k := finalizeAArch64) Proof.CmacTripleDes.AArch64.finalize_correct h.pre h.reads
    h.writes (fun s' hrd hwr ha hf _ hpost => ⟨hrd, hwr, ha.2.1, ha.1, hf, ?_⟩) (by lit_decide)
  simp only [finalizeAArch64, State.withRegions_gpr, State.withRegions_mem, h.x0, h.x1, h.x2, h.x3,
    hL] at hpost
  exact hpost

/-! ## `init` -/

/-- What a run of `init` needs: the key `Kp` of `KL` bytes, the output `O`
and the working space `S`. -/
structure IArgs (s : State) (Kp O S : Addr) (KL : Nat) : Prop where
  x0 : s.gpr .x0 = Kp
  x1 : s.gpr .x1 = BitVec.ofNat 64 KL
  x2 : s.gpr .x2 = O
  x3 : s.gpr .x3 = S
  klen : Spec.TripleDes.validKey KL
  ko : (⟨Kp, KL⟩ : Region).Disjoint ⟨O, 400⟩
  ks : (⟨Kp, KL⟩ : Region).Disjoint ⟨S, 640⟩
  os : (⟨O, 400⟩ : Region).Disjoint ⟨S, 640⟩
  wrapK : Kp.toNat + KL ≤ 2 ^ 64
  wrapO : O.toNat + 400 ≤ 2 ^ 64
  wrapS : S.toNat + 640 ≤ 2 ^ 64
  reads : Covers ([⟨Kp, KL⟩] ++ [⟨O, 400⟩, ⟨S, 640⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨O, 400⟩, ⟨S, 640⟩] s.wr

/-- What a run of `init` leaves. -/
structure IPost (s : State) (Kp O S : Addr) (KL : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  frame : Frame [⟨O, 400⟩, ⟨S, 640⟩] s.mem s'.mem
  out : let k := Spec.TripleDes.expandKey (Spec.TripleDes.bytesAt s.mem Kp KL)
    let ks := Spec.Cmac.subkeys (Spec.Cmac.tdesWith k) 8
    Spec.TripleDes.scheduleAt s'.mem O = k ∧ Spec.Aes.bytesAt s'.mem (O + 384) 16 = ks.1 ++ ks.2

theorem IArgs.pre {s : State} {Kp O S : Addr} {KL : Nat} (h : IArgs s Kp O S KL) :
    initAArch64.pre (s.withRegions [⟨Kp, KL⟩] [⟨O, 400⟩, ⟨S, 640⟩]) := by
  have hK := toNat_ofNat (n := KL) (by rcases h.klen with h | h <;> omega)
  simp only [initAArch64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, h.x0,
    h.x1, h.x2, h.x3, hK]
  exact ⟨trivial, trivial, h.ko, h.ks, h.os, h.wrapK, h.wrapO, h.wrapS, h.klen⟩

theorem init_inline_wp {s : State} {Kp O S : Addr} {KL : Nat} (h : IArgs s Kp O S KL) :
    WP isa Impl.CmacTripleDes.AArch64.init s (IPost s Kp O S KL) := by
  have hK := toNat_ofNat (n := KL) (by rcases h.klen with h | h <;> omega)
  refine WP.inline (k := initAArch64) Proof.CmacTripleDes.AArch64.init_correct h.pre h.reads h.writes
    (fun s' hrd hwr ha hf _ hpost => ⟨hrd, hwr, ha.2.1, ha.1, hf, ?_⟩) (by lit_decide)
  simp only [initAArch64, State.withRegions_gpr, State.withRegions_mem, h.x0, h.x1, h.x2, hK] at hpost
  exact hpost

end VG.Proof.CmacTripleDes.Stream.AArch64
