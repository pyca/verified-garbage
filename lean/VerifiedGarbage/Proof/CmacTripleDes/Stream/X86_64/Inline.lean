module

import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Verified
public import VerifiedGarbage.Proof.Framework.X86_64.Inline
public import Mathlib.Data.List.Induction
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.CmacTripleDes.X86_64
public import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Contract
public import VerifiedGarbage.Proof.CmacTripleDes.X86_64.RoundLit
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.TripleDes.SboxTables
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Lit
meta import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Lit
import VerifiedGarbage.Proof.Aes.Blocks
import VerifiedGarbage.Proof.Cmac.Block
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Implies
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Init
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Update
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.TCB.X86_64.Target

/-!
# Streaming TDEA-CMAC on x86-64: the code of `init`, `update` and `finalize`, inline

Each run of the code of `vg_cmac_triple_des_init`, `_update` and `_finalize`
inside the streaming functions, from its contract (`WP.inline`): what it
needs (`…Args`), and what it leaves (`…Post`, in terms of the memory before
it): it changes memory only in its buffers, and keeps our caller's
callee-saved registers.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.X86_64

open VG VG.X86_64
open VG.Proof.CmacTripleDes.X86_64 (updateX86_64 finalizeX86_64 initX86_64 ciphAt)

theorem toNat_ofNat {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-! ## `update` -/

/-- What a run of `update` needs: the key schedule `W`, the chaining value
`C`, `n` blocks at `D` and the working space `S`. -/
structure UArgs (s : State) (W C D S : Addr) (n : Nat) : Prop where
  rdi : s.gpr .rdi = W
  rsi : s.gpr .rsi = C
  rdx : s.gpr .rdx = D
  rcx : s.gpr .rcx = BitVec.ofNat 64 n
  r8 : s.gpr .r8 = S
  hn : 8 * n < 2 ^ 64
  wc : (⟨W, 384⟩ : Region).Disjoint ⟨C, 8⟩
  ws : (⟨W, 384⟩ : Region).Disjoint ⟨S, 640⟩
  dc : (⟨D, 8 * n⟩ : Region).Disjoint ⟨C, 8⟩
  ds : (⟨D, 8 * n⟩ : Region).Disjoint ⟨S, 640⟩
  cs : (⟨C, 8⟩ : Region).Disjoint ⟨S, 640⟩
  retC : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨C, 8⟩
  retS : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨S, 640⟩
  wrapC : C.toNat + 8 ≤ 2 ^ 64
  wrapD : D.toNat + 8 * n ≤ 2 ^ 64
  wrapS : S.toNat + 640 ≤ 2 ^ 64
  reads : Covers ([⟨W, 384⟩, ⟨D, 8 * n⟩] ++ [⟨C, 8⟩, ⟨S, 640⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨C, 8⟩, ⟨S, 640⟩] s.wr

/-- What a run of `update` leaves. -/
structure UPost (s : State) (W C D S : Addr) (n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨C, 8⟩, ⟨S, 640⟩] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem C 8 =
    Spec.Cmac.chain (ciphAt s.mem W) (Spec.Aes.bytesAt s.mem C 8) (Spec.Cmac.blocksAt s.mem D 8 n)

theorem UArgs.pre {s : State} {W C D S : Addr} {n : Nat} (h : UArgs s W C D S n) :
    updateX86_64.pre (s.withRegions [⟨W, 384⟩, ⟨D, 8 * n⟩] [⟨C, 8⟩, ⟨S, 640⟩]) := by
  have hN := toNat_ofNat (n := n) (by have := h.hn; omega)
  simp only [updateX86_64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, h.rdi,
    h.rsi, h.rdx, h.rcx, h.r8, hN]
  exact ⟨trivial, trivial, h.wc, h.ws, h.dc, h.ds, h.cs, h.retC, h.retS, h.wrapC, h.wrapD, h.wrapS⟩

theorem upd_wp {s : State} {W C D S : Addr} {n : Nat} (h : UArgs s W C D S n) :
    WP isa Impl.CmacTripleDes.X86_64.update s (UPost s W C D S n) := by
  have hN := toNat_ofNat (n := n) (by have := h.hn; omega)
  refine WP.inline (k := updateX86_64) Proof.CmacTripleDes.X86_64.update_correct h.pre h.reads h.writes
    (fun s' hrd hwr ha hf _ hpost => ⟨hrd, hwr, ha.1, hf, ?_⟩) (by lit_decide)
  simp only [updateX86_64, State.withRegions_gpr, State.withRegions_mem, h.rdi, h.rsi, h.rdx, h.rcx,
    hN] at hpost
  exact hpost

/-! ## `finalize` -/

/-- What a run of `finalize` needs: the key schedule and subkeys `K`, the
state `St`, the `L` last bytes at `P` and the working space `S`. -/
structure FArgs (s : State) (K St P S : Addr) (L : Nat) : Prop where
  rdi : s.gpr .rdi = K
  rsi : s.gpr .rsi = St
  rdx : s.gpr .rdx = P
  rcx : s.gpr .rcx = BitVec.ofNat 64 L
  r8 : s.gpr .r8 = S
  len : L ≤ 8
  kst : (⟨K, 400⟩ : Region).Disjoint ⟨St, 8⟩
  ks : (⟨K, 400⟩ : Region).Disjoint ⟨S, 640⟩
  pst : (⟨P, L⟩ : Region).Disjoint ⟨St, 8⟩
  ps : (⟨P, L⟩ : Region).Disjoint ⟨S, 640⟩
  sts : (⟨St, 8⟩ : Region).Disjoint ⟨S, 640⟩
  retSt : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨St, 8⟩
  retS : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨S, 640⟩
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
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨St, 8⟩, ⟨S, 640⟩] s.mem s'.mem
  out : let ciph := ciphAt s.mem K
    let ks := Spec.Cmac.subkeys ciph 8
    Spec.Aes.bytesAt s.mem (K + 384) 16 = ks.1 ++ ks.2 →
    ∀ msg : List Byte, msg.length % 8 = 0 → (msg = [] ∨ 0 < L) →
      Spec.Aes.bytesAt s.mem St 8 = Spec.Cmac.chain ciph (Spec.Cmac.zeros 8) (Spec.Cmac.blocks 8 msg) →
      Spec.Aes.bytesAt s'.mem St 8 = Spec.Cmac.macFull ciph 8 (msg ++ Spec.Aes.bytesAt s.mem P L)

theorem FArgs.pre {s : State} {K St P S : Addr} {L : Nat} (h : FArgs s K St P S L) :
    finalizeX86_64.pre (s.withRegions [⟨K, 400⟩, ⟨P, L⟩] [⟨St, 8⟩, ⟨S, 640⟩]) := by
  have hL := toNat_ofNat (n := L) (by have := h.len; omega)
  simp only [finalizeX86_64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, h.rdi,
    h.rsi, h.rdx, h.rcx, h.r8, hL]
  exact ⟨trivial, trivial, h.kst, h.ks, h.pst, h.ps, h.sts, h.retSt, h.retS, h.wrapK, h.wrapSt, h.wrapP,
    h.wrapS, h.len⟩

theorem fin_wp {s : State} {K St P S : Addr} {L : Nat} (h : FArgs s K St P S L) :
    WP isa Impl.CmacTripleDes.X86_64.finalize s (FPost s K St P S L) := by
  have hL := toNat_ofNat (n := L) (by have := h.len; omega)
  refine WP.inline (k := finalizeX86_64) Proof.CmacTripleDes.X86_64.finalize_correct h.pre h.reads
    h.writes (fun s' hrd hwr ha hf _ hpost => ⟨hrd, hwr, ha.1, hf, ?_⟩) (by lit_decide)
  simp only [finalizeX86_64, State.withRegions_gpr, State.withRegions_mem, h.rdi, h.rsi, h.rdx, h.rcx,
    hL] at hpost
  exact hpost

/-! ## `init` -/

/-- What a run of `init` needs: the key `Kp` of `KL` bytes, the output `O`
and the working space `S`. -/
structure IArgs (s : State) (Kp O S : Addr) (KL : Nat) : Prop where
  rdi : s.gpr .rdi = Kp
  rsi : s.gpr .rsi = BitVec.ofNat 64 KL
  rdx : s.gpr .rdx = O
  rcx : s.gpr .rcx = S
  klen : Spec.TripleDes.validKey KL
  ko : (⟨Kp, KL⟩ : Region).Disjoint ⟨O, 400⟩
  ks : (⟨Kp, KL⟩ : Region).Disjoint ⟨S, 640⟩
  os : (⟨O, 400⟩ : Region).Disjoint ⟨S, 640⟩
  retO : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨O, 400⟩
  retS : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨S, 640⟩
  wrapK : Kp.toNat + KL ≤ 2 ^ 64
  wrapO : O.toNat + 400 ≤ 2 ^ 64
  wrapS : S.toNat + 640 ≤ 2 ^ 64
  reads : Covers ([⟨Kp, KL⟩] ++ [⟨O, 400⟩, ⟨S, 640⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨O, 400⟩, ⟨S, 640⟩] s.wr

/-- What a run of `init` leaves. -/
structure IPost (s : State) (Kp O S : Addr) (KL : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨O, 400⟩, ⟨S, 640⟩] s.mem s'.mem
  out : let k := Spec.TripleDes.expandKey (Spec.TripleDes.bytesAt s.mem Kp KL)
    let ks := Spec.Cmac.subkeys (Spec.Cmac.tdesWith k) 8
    Spec.TripleDes.scheduleAt s'.mem O = k ∧ Spec.Aes.bytesAt s'.mem (O + 384) 16 = ks.1 ++ ks.2

theorem IArgs.pre {s : State} {Kp O S : Addr} {KL : Nat} (h : IArgs s Kp O S KL) :
    initX86_64.pre (s.withRegions [⟨Kp, KL⟩] [⟨O, 400⟩, ⟨S, 640⟩]) := by
  have hK := toNat_ofNat (n := KL) (by rcases h.klen with h | h <;> omega)
  simp only [initX86_64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, h.rdi,
    h.rsi, h.rdx, h.rcx, hK]
  exact ⟨trivial, trivial, h.ko, h.ks, h.os, h.retO, h.retS, h.wrapK, h.wrapO, h.wrapS, h.klen⟩

theorem init_inline_wp {s : State} {Kp O S : Addr} {KL : Nat} (h : IArgs s Kp O S KL) :
    WP isa Impl.CmacTripleDes.X86_64.init s (IPost s Kp O S KL) := by
  have hK := toNat_ofNat (n := KL) (by rcases h.klen with h | h <;> omega)
  refine WP.inline (k := initX86_64) Proof.CmacTripleDes.X86_64.init_correct h.pre h.reads h.writes
    (fun s' hrd hwr ha hf _ hpost => ⟨hrd, hwr, ha.1, hf, ?_⟩) (by lit_decide)
  simp only [initX86_64, State.withRegions_gpr, State.withRegions_mem, h.rdi, h.rsi, h.rdx, hK] at hpost
  exact hpost

end VG.Proof.CmacTripleDes.Stream.X86_64
