module

import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Contract
public import VerifiedGarbage.Impl.ChaCha20Poly1305.PPC64LE
public import VerifiedGarbage.Proof.ChaCha20.PPC64LE.Xor
public import VerifiedGarbage.Proof.Poly1305.PPC64LE.Shared
public import VerifiedGarbage.Proof.Poly1305.PPC64LE.Init
public import VerifiedGarbage.Proof.Poly1305.PPC64LE.Finalize
public import VerifiedGarbage.Proof.Framework.PPC64LE.CallAny
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Spec.ChaCha20
public import VerifiedGarbage.Spec.Poly1305
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.PPC64LE.Isa
import VerifiedGarbage.Proof.ChaCha20.PPC64LE.Block
public import VerifiedGarbage.Proof.Poly1305.Contract

/-!
# ChaCha20-Poly1305 on PPC64LE: the calls

Each call of a verified function, from its proof (`WP.call`, or
`WP.callAny` for `vg_poly1305_blocks`, which allocates a frame): what it
needs of the state it is called from, and what holds when it returns. A
call (`bl`) stores nothing in memory, so the callee changes memory only
within the regions it may write (and its frame below the stack pointer).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.PPC64LE

open VG VG.PPC64LE
open VG.Spec.Poly1305 (Repr Buffered bytesAt mac)
open VG.Spec.ChaCha20 (stateAt keystream)

/-- `s'` differs from `s` only in memory within `rs` and in registers that
are not callee-saved. -/
structure Kept (rs : List Region) (s s' : State) : Prop where
  cs : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame rs s.mem s'.mem

theorem Kept.trans {rs : List Region} {s₁ s₂ s₃ : State} (h₁ : Kept rs s₁ s₂) (h₂ : Kept rs s₂ s₃) :
    Kept rs s₁ s₃ :=
  ⟨fun r hr => by rw [h₂.cs r hr, h₁.cs r hr], by rw [h₂.sp, h₁.sp], by rw [h₂.rd, h₁.rd],
    by rw [h₂.wr, h₁.wr], h₁.frame.trans h₂.frame⟩

theorem Kept.sub {rs rs' : List Region} {s s' : State} (h : Kept rs s s')
    (hs : ∀ r ∈ rs, ∃ r' ∈ rs', Region.Sub r r') : Kept rs' s s' :=
  ⟨h.cs, h.sp, h.rd, h.wr, h.frame.sub hs⟩

/-! ## `vg_chacha20_block` -/

theorem block_call {s : State} {S B : Addr} (h3 : s.gpr .r3 = S) (h4 : s.gpr .r4 = B)
    (hdj : (⟨B, 256⟩ : Region).Disjoint ⟨S, 64⟩)
    (hc : Covers ([⟨S, 64⟩] ++ [⟨B, 256⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨B, 256⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨B, 256⟩] s s' →
      stateAt s'.mem B = Spec.ChaCha20.block (stateAt s.mem S) → Q s') :
    WP isa (.call "vg_chacha20_block" Impl.ChaCha20.PPC64LE.block) s Q := by
  refine WP.call (k := Proof.ChaCha20.blockPPC64LE) Proof.ChaCha20.PPC64LE.block_verified.1
    (rd := [⟨S, 64⟩]) (wr := [⟨B, 256⟩]) ?_ hc hw ?_
  · simp only [Proof.ChaCha20.blockPPC64LE, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_gpr s (by decide : Reg.r3 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r4 ∉ linkRegs), h3, h4]
    exact ⟨trivial, trivial, hdj⟩
  · intro s' hrd hwr hsp hf hcs _ hpost
    refine hQ s' ⟨hcs, hsp, hrd, hwr, hf⟩ ?_
    simpa only [Proof.ChaCha20.blockPPC64LE, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, State.callEntry_gpr s (by decide : Reg.r3 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r4 ∉ linkRegs), h3, h4] using hpost

/-! ## `vg_chacha20_xor` -/

theorem xor_call {s : State} {S D B : Addr} {n : Nat} (h3 : s.gpr .r3 = S) (h4 : s.gpr .r4 = D)
    (h5 : s.gpr .r5 = BitVec.ofNat 64 n) (h6 : s.gpr .r6 = B) (hn : n < 2 ^ 64)
    (hSD : (⟨S, 64⟩ : Region).Disjoint ⟨D, n⟩)
    (hSB : (⟨S, 64⟩ : Region).Disjoint ⟨B, 320⟩)
    (hDB : (⟨D, n⟩ : Region).Disjoint ⟨B, 320⟩) (hD : D.toNat + n ≤ 2 ^ 64)
    (hc : Covers ([] ++ [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩] s s' →
      Spec.ChaCha20.bytesAt s'.mem D n =
        List.zipWith (· ^^^ ·) (Spec.ChaCha20.bytesAt s.mem D n)
          (keystream (stateAt s.mem S) n) → Q s') :
    WP isa (.call "vg_chacha20_xor" Impl.ChaCha20.PPC64LE.Xor.xor) s Q := by
  have hn' : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn
  refine WP.call (k := Proof.ChaCha20.xorPPC64LE) Proof.ChaCha20.PPC64LE.Xor.xor_correct
    (rd := []) (wr := [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩]) ?_ hc hw ?_
  · simp only [Proof.ChaCha20.xorPPC64LE, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_gpr s (by decide : Reg.r3 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r4 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r5 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r6 ∉ linkRegs), h3, h4, h5, h6, hn']
    exact ⟨trivial, trivial, hSD, hSB, hDB, hD⟩
  · intro s' hrd hwr hsp hf hcs _ hpost
    simp only [Proof.ChaCha20.xorPPC64LE, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, State.callEntry_gpr s (by decide : Reg.r3 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r4 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r5 ∉ linkRegs), h3, h4, h5, hn'] at hpost
    exact hQ s' ⟨hcs, hsp, hrd, hwr, hf⟩ hpost

/-! ## `vg_poly1305_init` -/

theorem init_call {s : State} {P K : Addr} (h3 : s.gpr .r3 = P) (h4 : s.gpr .r4 = K)
    (hdj : (⟨P, 128⟩ : Region).Disjoint ⟨K, 32⟩)
    (hc : Covers ([⟨K, 32⟩] ++ [⟨P, 128⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨P, 128⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨P, 128⟩] s s' → Repr s'.mem P (bytesAt s.mem K 32) [] → Q s') :
    WP isa (.call "vg_poly1305_init" Impl.Poly1305.PPC64LE.init) s Q := by
  refine WP.call (k := Proof.Poly1305.initPPC64LE) Proof.Poly1305.PPC64LE.init_verified.1
    (rd := [⟨K, 32⟩]) (wr := [⟨P, 128⟩]) ?_ hc hw ?_
  · simp only [Proof.Poly1305.initPPC64LE, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_gpr s (by decide : Reg.r3 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r4 ∉ linkRegs), h3, h4]
    exact ⟨trivial, trivial, hdj⟩
  · intro s' hrd hwr hsp hf hcs _ hpost
    refine hQ s' ⟨hcs, hsp, hrd, hwr, hf⟩ ?_
    simpa only [Proof.Poly1305.initPPC64LE, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, State.callEntry_gpr s (by decide : Reg.r3 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r4 ∉ linkRegs), h3, h4] using hpost

/-! ## `vg_poly1305_blocks`, in its frame -/

theorem blocks_call {s : State} {P p : Addr} {n : Nat} (h3 : s.gpr .r3 = P) (h4 : s.gpr .r4 = p)
    (h5 : s.gpr .r5 = BitVec.ofNat 64 n) (hn : 16 * n < 2 ^ 64) (hsp : 160 ≤ s.sp.toNat)
    (hdj : (⟨P, 128⟩ : Region).Disjoint ⟨p, 16 * n⟩)
    (hbP : (⟨s.sp - 160, 160⟩ : Region).Disjoint ⟨P, 128⟩)
    (hbp : (⟨s.sp - 160, 160⟩ : Region).Disjoint ⟨p, 16 * n⟩)
    (hP : P.toNat + 128 ≤ 2 ^ 64) (hp : p.toNat + 16 * n ≤ 2 ^ 64)
    (hc : Covers ([⟨p, 16 * n⟩] ++ [⟨P, 128⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨P, 128⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨P, 128⟩, ⟨s.sp - 160, 160⟩] s s' →
      (∀ key msg, Repr s.mem P key msg → Repr s'.mem P key (msg ++ bytesAt s.mem p (16 * n))) →
      Q s') :
    WP isa (.call "vg_poly1305_blocks" Impl.ChaCha20Poly1305.PPC64LE.blocksCode) s Q := by
  have hn' : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  refine WP.callAny (k := Proof.Poly1305.blocksContract PPC64LE.abi 160)
    Proof.Poly1305.PPC64LE.Shared.blocks.1
    (rd := [⟨p, 16 * n⟩]) (wr := [⟨P, 128⟩]) ?_ hc hw ?_
  · sig_pre [Proof.Poly1305.blocksContract, Proof.Poly1305.blocksSig, PPC64LE.abi, PPC64LE.argRegs]
    simp only [h3, h4, h5, hn', Nat.mul_comm n 16]
    exact ⟨hsp, trivial, trivial, hdj, hbP, hbp, hP, hp⟩
  · intro s' hrd hwr hsp' hf hcs hpost
    refine hQ s' ⟨hcs, hsp', hrd, hwr, ?_⟩ fun key msg hr => ?_
    · refine hf.sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
    · sig_post [Proof.Poly1305.blocksContract, Proof.Poly1305.blocksSig, Proof.Poly1305.blocksPost,
        PPC64LE.abi, PPC64LE.argRegs] at hpost
      simp only [h3, h4, h5, hn'] at hpost
      exact hpost key msg hr

/-! ## `vg_poly1305_finalize_scratch` -/

theorem finalize_call {s : State} {P O Sc : Addr} {c : BitVec 64} (h3 : s.gpr .r3 = P)
    (h4 : s.gpr .r4 = c) (h5 : s.gpr .r5 = O) (h6 : s.gpr .r6 = Sc)
    (hPO : (⟨P, 128⟩ : Region).Disjoint ⟨O, 16⟩) (hPS : (⟨P, 128⟩ : Region).Disjoint ⟨Sc, 128⟩)
    (hOS : (⟨O, 16⟩ : Region).Disjoint ⟨Sc, 128⟩)
    (hc : Covers ([] ++ [⟨P, 128⟩, ⟨O, 16⟩, ⟨Sc, 128⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨P, 128⟩, ⟨O, 16⟩, ⟨Sc, 128⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨P, 128⟩, ⟨O, 16⟩, ⟨Sc, 128⟩] s s' →
      (∀ key msg, Buffered s.mem P key msg → c.toNat % 16 = msg.length % 16 →
        bytesAt s'.mem O 16 = mac key msg) → Q s') :
    WP isa (.call "vg_poly1305_finalize_scratch" Impl.Poly1305.PPC64LE.finalize) s Q := by
  refine WP.call (k := Proof.Poly1305.finalizePPC64LE) Proof.Poly1305.PPC64LE.finalize_verified.1
    (rd := []) (wr := [⟨P, 128⟩, ⟨O, 16⟩, ⟨Sc, 128⟩]) ?_ hc hw ?_
  · simp only [Proof.Poly1305.finalizePPC64LE, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_gpr s (by decide : Reg.r3 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r5 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r6 ∉ linkRegs), h3, h5, h6]
    exact ⟨trivial, trivial, hPO, hPS, hOS⟩
  · intro s' hrd hwr hsp hf hcs _ hpost
    refine hQ s' ⟨hcs, hsp, hrd, hwr, hf⟩ ?_
    simpa only [Proof.Poly1305.finalizePPC64LE, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, State.callEntry_gpr s (by decide : Reg.r3 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r4 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r5 ∉ linkRegs), h3, h4, h5] using hpost

end VG.Proof.ChaCha20Poly1305.PPC64LE
