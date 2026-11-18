module

import VerifiedGarbage.Proof.GcmSiv.Ctr
public import VerifiedGarbage.Proof.Cmac.Block32
public import VerifiedGarbage.Proof.AesGcmSiv.X86.Run
public import VerifiedGarbage.Proof.GcmSiv.Spec
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.AesGcm.X86.Flush
import VerifiedGarbage.Proof.AesGcm.X86.Cmp
import VerifiedGarbage.Proof.AesGcm.X86.Loops
meta import VerifiedGarbage.Proof.AesGcmSiv.X86.Run
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd

/-! ### `AesGcmSiv.X86.Callee`, which this module and modules that import it used -/

section

/-!
# AES-GCM-SIV on x86: the functions called

Untrusted: everything here is checked by Lean. The calls of `vg_aes_ctr32_to`,
`vg_ghash` and `vg_aes_expand_key` are AES-GCM's (`Proof.AesGcm.X86`'s
`ctr_call`, `gh_call`, `key_call`), with `ebp` moved to the callee's working
space around them (`callCtr_ok`, `callGh_ok`, `callKey_ok`). Their arguments
are built from the environment:

* `vg_aes_ctr32_to`: a key schedule (`KeyOk`: the key-generating key's, or the
  encryption key's at `W + 512`), the counter block's copy at `W + 112`,
  `n` blocks at `D` (`Dst`), and the working space at `W + 768`;
* `vg_ghash`: GHASH's key at `W + 64`, the accumulator at `W + 80`, `n` (at
  most 64) reversed blocks at `W + 768` and the working space at
  `W + 1792`;
* `vg_aes_expand_key`: the encryption key at `W + 32`, its schedule at
  `W + 512` and the working space at `W + 768`.

Each call writes only parts of `mutR`, so `Env` holds after it.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcmSiv.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (blockAt blocksAt ctr32 aesWith ghashFrom)
open VG.Impl.AesGcm.X86 (imm)
open VG.Proof.AesGcm.X86 (w64 toNat_ofNat32 toNat_add32 w64_add covers_left covers_cons covers_nil CtrCall CtrPost
  GhCall GhPost KeyCall KeyPost GcmImpl gpr_setMem CT)

/-! ## `vg_aes_ctr32_to` -/

/-- A key schedule of 240 bytes at `Q`, which the code may read, apart from
the counter block's copy at `W + 112`, the working space at `W + 768` and
the stack the calls use. -/
structure KeyOk (p : Prm) (s : State) (Q : BitVec 32) : Prop where
  rd : Covers [⟨w64 Q, 240⟩] (s.rd ++ s.wr)
  wrap : Q.toNat + 240 ≤ 2 ^ 32
  kc : (⟨w64 Q, 240⟩ : Region).Disjoint ⟨w64 p.W + BitVec.ofNat 64 112, 16⟩
  ks : (⟨w64 Q, 240⟩ : Region).Disjoint ⟨w64 p.W + BitVec.ofNat 64 768, 2048⟩
  stk : (stk p).Disjoint ⟨w64 Q, 240⟩

theorem KeyOk.of_eq {p : Prm} {s s' : State} {Q : BitVec 32} (h : KeyOk p s Q) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : KeyOk p s' Q :=
  { h with rd := by rw [hrd, hwr]; exact h.rd }

/-- The key-generating key's schedule. -/
theorem keyK {p : Prm} {s : State} (L : Lay p) (P : Perm p s) : KeyOk p s p.K :=
  ⟨P.k, L.kw, L.k_w' (by decide), L.k_w' (by decide), L.bk⟩

/-- The encryption key's schedule at `W + 512`. -/
theorem keyS {p : Prm} {s : State} (L : Lay p) (P : Perm p s) : KeyOk p s (p.W + BitVec.ofNat 32 512) where
  rd := by rw [L.aW (by decide)]; exact P.wCR (by decide)
  wrap := by rw [L.nW (by decide)]; have := L.ww; omega_arith
  kc := by rw [L.aW (by decide)]; exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  ks := by rw [L.aW (by decide)]; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  stk := by rw [L.aW (by decide)]; exact L.bw' (by decide)

/-- `k` bytes at `D` that `vg_aes_ctr32_to` may write: apart from the key
schedule at `Q`, the counter block's copy, the working space and the stack
the calls use. -/
structure Dst (p : Prm) (s : State) (Q D : BitVec 32) (k : Nat) : Prop where
  wr : Covers [⟨w64 D, k⟩] s.wr
  wrap : D.toNat + k ≤ 2 ^ 32
  dk : (⟨w64 Q, 240⟩ : Region).Disjoint ⟨w64 D, k⟩
  dc : (⟨w64 D, k⟩ : Region).Disjoint ⟨w64 p.W + BitVec.ofNat 64 112, 16⟩
  ds : (⟨w64 D, k⟩ : Region).Disjoint ⟨w64 p.W + BitVec.ofNat 64 768, 2048⟩
  stk : (stk p).Disjoint ⟨w64 D, k⟩

theorem Dst.of_eq {p : Prm} {s s' : State} {Q D : BitVec 32} {k : Nat} (h : Dst p s Q D k) (hwr : s'.wr = s.wr) :
    Dst p s' Q D k :=
  { h with wr := by rw [hwr]; exact h.wr }

/-- A block of `W` as `vg_aes_ctr32_to`'s data, with the key schedule `Q`. -/
theorem dstW {p : Prm} {s : State} (L : Lay p) (P : Perm p s) {Q : BitVec 32} {q : Nat}
    (hq : q + 16 ≤ 128 ∧ (q + 16 ≤ 112 ∨ 128 ≤ q) ∨ 224 ≤ q ∧ q + 16 ≤ 256)
    (hk : (⟨w64 Q, 240⟩ : Region).Disjoint ⟨w64 p.W + BitVec.ofNat 64 q, 16⟩) :
    Dst p s Q (p.W + BitVec.ofNat 32 q) 16 where
  wr := by rw [L.aW (o := q) (by omega_arith)]; exact P.wC (by omega_arith)
  wrap := by rw [L.nW (o := q) (by omega_arith)]; have := L.ww; omega_arith
  dk := by rw [L.aW (o := q) (by omega_arith)]; exact hk
  dc := by rw [L.aW (o := q) (by omega_arith)]; exact Lay.w_w (by omega_arith) (by omega_arith) (by decide)
  ds := by rw [L.aW (o := q) (by omega_arith)]; exact Lay.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
  stk := by rw [L.aW (o := q) (by omega_arith)]; exact L.bw' (by omega_arith)

/-- The arguments of `vg_aes_ctr32_to`: the key schedule at `Q`, the counter
block's copy at `W + 112`, `n` blocks at `D`, and the working space at
`W + 768` (where `ebp` is moved). -/
theorem cargs {p : Prm} {s : State} (L : Lay p) (esp : s.gpr .esp = p.SP) (P : Perm p s) {Q D : BitVec 32}
    {n : Nat} (hQ : KeyOk p s Q) (hD : Dst p s Q D (16 * n)) (eax : s.gpr .eax = Q)
    (ecx : s.gpr .ecx = BitVec.ofNat 32 p.R) (edx : s.gpr .edx = p.W + BitVec.ofNat 32 112)
    (ebx : s.gpr .ebx = D) (edi : s.gpr .edi = BitVec.ofNat 32 n)
    (ebp : s.gpr .ebp = p.W + BitVec.ofNat 32 768) :
    CtrCall s Q (p.W + BitVec.ofNat 32 112) D (p.W + BitVec.ofNat 32 768) p.R n := by
  have hsp := L.sp
  refine ⟨eax, ecx, edx, ebx, edi, ebp, L.rounds3, by rw [esp]; omega_arith, ?_, hD.dk, ?_, ?_, ?_, hD.ds.sub_right ?_,
    ?_, ?_, ?_, ?_, hQ.wrap, ?_, hD.wrap, ?_, hQ.rd, ?_⟩
  · rw [L.aW (by decide)]; exact hQ.kc
  · rw [L.aW (by decide)]; exact hQ.ks
  · rw [L.aW (by decide)]; exact hD.dc.symm
  · rw [L.aW (by decide), L.aW (by decide)]; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · rw [L.aW (by decide)]; exact fun _ h => h
  · rw [esp]; exact hQ.stk
  · rw [esp, L.aW (by decide)]; exact L.bw' (by decide)
  · rw [esp]; exact hD.stk
  · rw [esp, L.aW (by decide)]; exact L.bw' (by decide)
  · rw [L.nW (by decide)]; have := L.ww; omega_arith
  · rw [L.nW (by decide)]; have := L.ww; omega_arith
  · rw [L.aW (by decide), L.aW (by decide)]
    exact covers_cons (P.wC (by decide)) (covers_cons hD.wr (covers_cons (P.wC (by decide)) covers_nil))

/-- What a call of `vg_aes_ctr32_to` leaves. -/
structure CtrOut (p : Prm) (s : State) (Q D : BitVec 32) (n : Nat) (s' : State) : Prop where
  env : Env p s'
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ [Reg.ebx, .esi, .edi], s'.gpr r = s.gpr r
  frame : Frame [⟨w64 p.W + BitVec.ofNat 64 112, 16⟩, ⟨w64 D, 16 * n⟩,
    ⟨w64 p.W + BitVec.ofNat 64 768, 2048⟩, stk p] s.mem s'.mem
  out : blocksAt s'.mem (w64 D) n =
    ctr32 (aesWith p.R (bytesAt s.mem (w64 Q) (16 * (p.R + 1)))) (blockAt s.mem (w64 p.W + BitVec.ofNat 64 112))
      (blocksAt s.mem (w64 D) n)

/-- A call of `vg_aes_ctr32_to` on `n` blocks at `D`, which must lie in `mutR`,
from the counter block's copy at `W + 112`, under the key schedule `Q`. -/
theorem callCtr_ok (v : GcmImpl) {p : Prm} {s : State} (L : Lay p) (E : Env p s) {Q D : BitVec 32} {n : Nat}
    (hQ : KeyOk p s Q) (hD : Dst p s Q D (16 * n)) (hm : ∃ r' ∈ mutR p, Region.Sub ⟨w64 D, 16 * n⟩ r')
    (eax : s.gpr .eax = Q) (ecx : s.gpr .ecx = BitVec.ofNat 32 p.R) (edx : s.gpr .edx = p.W + BitVec.ofNat 32 112)
    (ebx : s.gpr .ebx = D) (edi : s.gpr .edi = BitVec.ofNat 32 n) :
    WP isa (callCtr v.callees) s (CtrOut p s Q D n) := by
  -- `ebp := W + 768`.
  refine WP.seq (WP.of_runBlock ⟨_, by grun [], ?_⟩)
  -- The call.
  have e768 : s.gpr .ebp + BitVec.ofNat 32 768 = p.W + BitVec.ofNat 32 768 := by rw [E.ebp]
  refine WP.seq (WP.mono (Proof.AesGcm.X86.ctr_call v (cargs L (by gregs [E.esp])
    (E.perm.of_eq (by gmems []) (by gmems [])) (hQ.of_eq (by gmems []) (by gmems [])) (hD.of_eq (by gmems []))
    (by gregs [eax]) (by gregs [ecx]) (by gregs [edx]) (by gregs [ebx]) (by gregs [edi]) (by gregs [e768])))
    fun s₂ P => ?_)
  -- `ebp := W`.
  have hbp₂ : s₂.gpr .ebp = p.W + BitVec.ofNat 32 768 := by
    rw [P.saved _ (by decide)]; gregs [E.ebp]
  have hsp₂ : s₂.gpr .esp = p.SP := by rw [P.saved _ (by decide)]; gregs [E.esp]
  have f : Frame [⟨w64 p.W + BitVec.ofNat 64 112, 16⟩, ⟨w64 D, 16 * n⟩,
      ⟨w64 p.W + BitVec.ofNat 64 768, 2048⟩, stk p] s.mem s₂.mem := by
    have f := P.frame
    rw [L.aW (by decide), L.aW (by decide)] at f
    simp only [mem_setReg, mem_arithFlags] at f
    refine f.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · refine ⟨stk p, by simp, ?_⟩
      simpa [gpr_setReg_of_ne, E.esp] using L.stkSub (k := 32) (by decide)
  have fm : Frame (mutR p) s.mem s₂.mem := frame_toMut f fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact inMut_w p (d := 112) (k := 16) (.inl (by decide))
    · exact hm
    · exact inMut_w p (d := 768) (k := 2048) (.inr (.inr (.inr ⟨by decide, by decide⟩)))
    · exact inMut_stk p
  refine WP.of_runBlock ⟨_, by grun [hbp₂], ?_⟩
  refine ⟨E.mut L (by gregs [hbp₂]; exact BitVec.add_sub_cancel _ _) (by gregs [hsp₂]) (by gmems [P.rd])
    (by gmems [P.wr]) (by gmems []; exact fm), by gmems [P.rd], by gmems [P.wr], ?_, by gmems []; exact f, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> (gregs []; rw [P.saved _ (by decide)]; gregs [])
  · have o := P.out
    rw [L.aW (by decide)] at o
    gmems []
    exact o

/-- Calls of `vg_aes_ctr32_to` with the same arguments are constant time. -/
theorem callCtr_ct (v : GcmImpl) {p : Prm} (L : Lay p) {Q D : BitVec 32} {n : Nat} {I : State → Prop}
    (hI : ∀ s, I s → Env p s ∧ KeyOk p s Q ∧ Dst p s Q D (16 * n) ∧ s.gpr .eax = Q ∧
      s.gpr .ecx = BitVec.ofNat 32 p.R ∧ s.gpr .edx = p.W + BitVec.ofNat 32 112 ∧ s.gpr .ebx = D ∧
      s.gpr .edi = BitVec.ofNat 32 n) :
    CT I (callCtr v.callees) := by
  -- The state after `ebp := W + 768`, as `CtrCall` needs it.
  have call : ∀ s, I s → ∀ s', runBlock isa [.alu .add .ebp (imm scrO)] s = some s' →
      CtrCall s' Q (p.W + BitVec.ofNat 32 112) D (p.W + BitVec.ofNat 32 768) p.R n ∧ s'.gpr .esp = p.SP := by
    intro s hs s' run
    obtain ⟨E, hQ, hD, eax, ecx, edx, ebx, edi⟩ := hI s hs
    have e := run
    simp (disch := first | decide | omega_arith) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
      imm, scrO, Option.bind_some, Option.some.injEq] at e
    subst e
    have e768 : s.gpr .ebp + BitVec.ofNat 32 768 = p.W + BitVec.ofNat 32 768 := by rw [E.ebp]
    exact ⟨cargs L (by gregs [E.esp]) (E.perm.of_eq (by gmems []) (by gmems [])) (hQ.of_eq (by gmems []) (by gmems []))
      (hD.of_eq (by gmems [])) (by gregs [eax]) (by gregs [ecx]) (by gregs [edx]) (by gregs [ebx]) (by gregs [edi])
      (by gregs [e768]), by gregs [E.esp]⟩
  refine CT.seq (J := fun s' => ∃ s, I s ∧ runBlock isa [.alu .add .ebp (imm scrO)] s = some s')
    (CT.taint [.ebp] (pin_ebp fun s h => (hI s h).1.ebp) (by taint_decide))
    (fun s hs => WP.of_runBlock ⟨_, by grun [], s, hs, by grun []⟩) ?_
  refine CT.seq (J := fun s => s.gpr .ebp = p.W + BitVec.ofNat 32 768)
    (Proof.AesGcm.X86.ctr_ct v (E := p.SP) fun s ⟨s₀, h₀, run⟩ => call s₀ h₀ s run)
    (fun s ⟨s₀, h₀, run⟩ => WP.mono (Proof.AesGcm.X86.ctr_call v (call s₀ h₀ s run).1) fun s₁ g => by
      rw [g.saved .ebp (by decide), (call s₀ h₀ s run).1.ebp]) ?_
  exact CT.taint [.ebp] (pin_ebp fun _ h => h) (by taint_decide)

/-! ## `vg_ghash` -/

/-- The arguments of `vg_ghash`: GHASH's key at `W + 64`, the accumulator at
`W + 80`, `n ≤ 64` blocks at `W + 768`, and the working space at `W + 1792`
(where `ebp` is moved). -/
theorem gargs {p : Prm} {s : State} (L : Lay p) (esp : s.gpr .esp = p.SP) (P : Perm p s) {n : Nat} (hn : n ≤ 64)
    (eax : s.gpr .eax = p.W + BitVec.ofNat 32 64) (edx : s.gpr .edx = p.W + BitVec.ofNat 32 80)
    (ebx : s.gpr .ebx = p.W + BitVec.ofNat 32 768) (edi : s.gpr .edi = BitVec.ofNat 32 n)
    (ebp : s.gpr .ebp = p.W + BitVec.ofNat 32 1792) :
    GhCall s (p.W + BitVec.ofNat 32 64) (p.W + BitVec.ofNat 32 80) (p.W + BitVec.ofNat 32 768)
      (p.W + BitVec.ofNat 32 1792) n := by
  have hsp := L.sp
  have b24 := L.stkSub (k := 24) (by decide)
  have ww := L.ww
  refine ⟨eax, edx, ebx, edi, ebp, by rw [esp]; omega_arith, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [L.aW (show 64 < 2816 by decide), L.aW (show 80 < 2816 by decide), L.aW (show 768 < 2816 by decide),
      L.aW (show 1792 < 2816 by decide), L.nW (show 64 < 2816 by decide), L.nW (show 80 < 2816 by decide),
      L.nW (show 768 < 2816 by decide), L.nW (show 1792 < 2816 by decide), esp]
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inl (by omega_arith)) (by decide) (by omega_arith)
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
  · exact (L.bw' (by decide)).sub_left b24
  · exact (L.bw' (by decide)).sub_left b24
  · exact (L.bw' (by omega_arith)).sub_left b24
  · exact (L.bw' (by decide)).sub_left b24
  · omega_arith
  · omega_arith
  · omega_arith
  · omega_arith
  · exact covers_cons (P.wCR (by decide)) (covers_cons (P.wCR (by omega_arith)) covers_nil)
  · exact covers_cons (P.wC (by decide)) (covers_cons (P.wC (by decide)) covers_nil)

/-- What a call of `vg_ghash` leaves. -/
structure GhOut (p : Prm) (s : State) (n : Nat) (s' : State) : Prop where
  env : Env p s'
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ [Reg.ebx, .esi, .edi], s'.gpr r = s.gpr r
  frame : Frame [⟨w64 p.W + BitVec.ofNat 64 80, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 1792, 256⟩, stk p] s.mem s'.mem
  out : blockAt s'.mem (w64 p.W + BitVec.ofNat 64 80) =
    ghashFrom (blockAt s.mem (w64 p.W + BitVec.ofNat 64 64)) (blockAt s.mem (w64 p.W + BitVec.ofNat 64 80))
      (blocksAt s.mem (w64 p.W + BitVec.ofNat 64 768) n)

/-- A call of `vg_ghash` on the `n ≤ 64` blocks at `W + 768`. -/
theorem callGh_ok (v : GcmImpl) {p : Prm} {s : State} (L : Lay p) (E : Env p s) {n : Nat} (hn : n ≤ 64)
    (eax : s.gpr .eax = p.W + BitVec.ofNat 32 64) (edx : s.gpr .edx = p.W + BitVec.ofNat 32 80)
    (ebx : s.gpr .ebx = p.W + BitVec.ofNat 32 768) (edi : s.gpr .edi = BitVec.ofNat 32 n) :
    WP isa (callGh v.callees) s (GhOut p s n) := by
  refine WP.seq (WP.of_runBlock ⟨_, by grun [], ?_⟩)
  have e1792 : s.gpr .ebp + BitVec.ofNat 32 1792 = p.W + BitVec.ofNat 32 1792 := by rw [E.ebp]
  refine WP.seq (WP.mono (Proof.AesGcm.X86.gh_call v (gargs L (by gregs [E.esp])
    (E.perm.of_eq (by gmems []) (by gmems [])) hn (by gregs [eax]) (by gregs [edx]) (by gregs [ebx]) (by gregs [edi])
    (by gregs [e1792]))) fun s₂ P => ?_)
  have hbp₂ : s₂.gpr .ebp = p.W + BitVec.ofNat 32 1792 := by
    rw [P.saved _ (by decide)]; gregs [E.ebp]
  have hsp₂ : s₂.gpr .esp = p.SP := by rw [P.saved _ (by decide)]; gregs [E.esp]
  have f : Frame [⟨w64 p.W + BitVec.ofNat 64 80, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 1792, 256⟩, stk p] s.mem s₂.mem := by
    have f := P.frame
    rw [L.aW (by decide), L.aW (by decide)] at f
    simp only [mem_setReg, mem_arithFlags] at f
    refine f.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · refine ⟨stk p, by simp, ?_⟩
      simpa [gpr_setReg_of_ne, E.esp] using L.stkSub (k := 24) (by decide)
  have fm : Frame (mutR p) s.mem s₂.mem := frame_toMut f fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact inMut_w p (d := 80) (k := 16) (.inl (by decide))
    · exact inMut_w p (d := 1792) (k := 256) (.inr (.inr (.inr ⟨by decide, by decide⟩)))
    · exact inMut_stk p
  refine WP.of_runBlock ⟨_, by grun [hbp₂], ?_⟩
  refine ⟨E.mut L (by gregs [hbp₂]; exact BitVec.add_sub_cancel _ _) (by gregs [hsp₂]) (by gmems [P.rd])
    (by gmems [P.wr]) (by gmems []; exact fm), by gmems [P.rd], by gmems [P.wr], ?_, by gmems []; exact f, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> (gregs []; rw [P.saved _ (by decide)]; gregs [])
  · have o := P.out
    rw [L.aW (by decide), L.aW (by decide), L.aW (by decide)] at o
    gmems []
    exact o

/-- Calls of `vg_ghash` on the `n ≤ 64` blocks at `W + 768` are constant
time. -/
theorem callGh_ct (v : GcmImpl) {p : Prm} (L : Lay p) {n : Nat} (hn : n ≤ 64) {I : State → Prop}
    (hI : ∀ s, I s → Env p s ∧ s.gpr .eax = p.W + BitVec.ofNat 32 64 ∧ s.gpr .edx = p.W + BitVec.ofNat 32 80 ∧
      s.gpr .ebx = p.W + BitVec.ofNat 32 768 ∧ s.gpr .edi = BitVec.ofNat 32 n) :
    CT I (callGh v.callees) := by
  have call : ∀ s, I s → ∀ s', runBlock isa [.alu .add .ebp (imm ghO)] s = some s' →
      GhCall s' (p.W + BitVec.ofNat 32 64) (p.W + BitVec.ofNat 32 80) (p.W + BitVec.ofNat 32 768)
        (p.W + BitVec.ofNat 32 1792) n ∧ s'.gpr .esp = p.SP := by
    intro s hs s' run
    obtain ⟨E, eax, edx, ebx, edi⟩ := hI s hs
    have e := run
    simp (disch := first | decide | omega_arith) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
      imm, ghO, Option.bind_some, Option.some.injEq] at e
    subst e
    have e1792 : s.gpr .ebp + BitVec.ofNat 32 1792 = p.W + BitVec.ofNat 32 1792 := by rw [E.ebp]
    exact ⟨gargs L (by gregs [E.esp]) (E.perm.of_eq (by gmems []) (by gmems [])) hn (by gregs [eax]) (by gregs [edx])
      (by gregs [ebx]) (by gregs [edi]) (by gregs [e1792]), by gregs [E.esp]⟩
  refine CT.seq (J := fun s' => ∃ s, I s ∧ runBlock isa [.alu .add .ebp (imm ghO)] s = some s')
    (CT.taint [.ebp] (pin_ebp fun s h => (hI s h).1.ebp) (by taint_decide))
    (fun s hs => WP.of_runBlock ⟨_, by grun [], s, hs, by grun []⟩) ?_
  refine CT.seq (J := fun s => s.gpr .ebp = p.W + BitVec.ofNat 32 1792)
    (Proof.AesGcm.X86.gh_ct v (E := p.SP) fun s ⟨s₀, h₀, run⟩ => call s₀ h₀ s run)
    (fun s ⟨s₀, h₀, run⟩ => WP.mono (Proof.AesGcm.X86.gh_call v (call s₀ h₀ s run).1) fun s₁ g => by
      rw [g.saved .ebp (by decide), (call s₀ h₀ s run).1.ebp]) ?_
  exact CT.taint [.ebp] (pin_ebp fun _ h => h) (by taint_decide)

/-! ## `vg_aes_expand_key` -/

/-- The key length of `R` rounds, as the code computes it. -/
theorem keyLen_eq {R : Nat} (hR : R = 10 ∨ R = 14) :
    (BitVec.ofNat 32 R - BitVec.ofNat 32 6 + (BitVec.ofNat 32 R - BitVec.ofNat 32 6) +
      (BitVec.ofNat 32 R - BitVec.ofNat 32 6 + (BitVec.ofNat 32 R - BitVec.ofNat 32 6))) =
      BitVec.ofNat 32 (Spec.GcmSiv.keyLen R) := by
  rcases hR with rfl | rfl <;> decide

/-- The arguments of `vg_aes_expand_key`: the encryption key at `W + 32`,
its schedule at `W + 512` and the working space at `W + 768` (where `ebp`
is moved). -/
theorem kargs {p : Prm} {s : State} (L : Lay p) (esp : s.gpr .esp = p.SP) (P : Perm p s)
    (eax : s.gpr .eax = p.W + BitVec.ofNat 32 32) (ecx : s.gpr .ecx = BitVec.ofNat 32 (Spec.GcmSiv.keyLen p.R))
    (edx : s.gpr .edx = p.W + BitVec.ofNat 32 512) (ebp : s.gpr .ebp = p.W + BitVec.ofNat 32 768) :
    KeyCall s (p.W + BitVec.ofNat 32 32) (p.W + BitVec.ofNat 32 512) (p.W + BitVec.ofNat 32 768)
      (Spec.GcmSiv.keyLen p.R) := by
  have hsp := L.sp
  have b20 := L.stkSub (k := 20) (by decide)
  have ww := L.ww
  have hk : Spec.GcmSiv.keyLen p.R = 16 ∨ Spec.GcmSiv.keyLen p.R = 32 := by
    rcases L.rounds with h | h <;> rw [h] <;> decide
  have hk32 : Spec.GcmSiv.keyLen p.R ≤ 32 := by omega_arith
  refine ⟨eax, ecx, edx, ebp, by omega_arith, by rw [esp]; omega_arith, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [L.aW (show 32 < 2816 by decide), L.aW (show 512 < 2816 by decide), L.aW (show 768 < 2816 by decide),
      L.nW (show 32 < 2816 by decide), L.nW (show 512 < 2816 by decide), L.nW (show 768 < 2816 by decide), esp]
  · exact Lay.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
  · exact Lay.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.bw' (by omega_arith)).sub_left b20
  · exact (L.bw' (by decide)).sub_left b20
  · exact (L.bw' (by decide)).sub_left b20
  · omega_arith
  · omega_arith
  · omega_arith
  · exact covers_cons (P.wCR (by omega_arith)) covers_nil
  · exact covers_cons (P.wC (by decide)) (covers_cons (P.wC (by decide)) covers_nil)

/-- What a call of `vg_aes_expand_key` leaves. -/
structure KeyOut (p : Prm) (s : State) (s' : State) : Prop where
  env : Env p s'
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ [Reg.ebx, .esi, .edi], s'.gpr r = s.gpr r
  frame : Frame [⟨w64 p.W + BitVec.ofNat 64 512, 240⟩, ⟨w64 p.W + BitVec.ofNat 64 768, 512⟩, stk p] s.mem s'.mem
  out : bytesAt s'.mem (w64 p.W + BitVec.ofNat 64 512) (16 * (Spec.Aes.rounds (Spec.GcmSiv.keyLen p.R / 4) + 1)) =
    Spec.Aes.expandKey (bytesAt s.mem (w64 p.W + BitVec.ofNat 64 32) (Spec.GcmSiv.keyLen p.R))

/-- The call of `vg_aes_expand_key` on the encryption key. -/
theorem callKey_ok (v : GcmImpl) {p : Prm} {s : State} (L : Lay p) (E : Env p s)
    (eax : s.gpr .eax = p.W + BitVec.ofNat 32 32) (ecx : s.gpr .ecx = BitVec.ofNat 32 (Spec.GcmSiv.keyLen p.R))
    (edx : s.gpr .edx = p.W + BitVec.ofNat 32 512) :
    WP isa (callKey v.callees) s (KeyOut p s) := by
  refine WP.seq (WP.of_runBlock ⟨_, by grun [], ?_⟩)
  have e768 : s.gpr .ebp + BitVec.ofNat 32 768 = p.W + BitVec.ofNat 32 768 := by rw [E.ebp]
  refine WP.seq (WP.mono (Proof.AesGcm.X86.key_call v (kargs L (by gregs [E.esp])
    (E.perm.of_eq (by gmems []) (by gmems [])) (by gregs [eax]) (by gregs [ecx]) (by gregs [edx]) (by gregs [e768])))
    fun s₂ P => ?_)
  have hbp₂ : s₂.gpr .ebp = p.W + BitVec.ofNat 32 768 := by
    rw [P.saved _ (by decide)]; gregs [E.ebp]
  have hsp₂ : s₂.gpr .esp = p.SP := by rw [P.saved _ (by decide)]; gregs [E.esp]
  have f : Frame [⟨w64 p.W + BitVec.ofNat 64 512, 240⟩, ⟨w64 p.W + BitVec.ofNat 64 768, 512⟩, stk p]
      s.mem s₂.mem := by
    have f := P.frame
    rw [L.aW (by decide), L.aW (by decide)] at f
    simp only [mem_setReg, mem_arithFlags] at f
    refine f.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · refine ⟨stk p, by simp, ?_⟩
      simpa [gpr_setReg_of_ne, E.esp] using L.stkSub (k := 20) (by decide)
  have fm : Frame (mutR p) s.mem s₂.mem := frame_toMut f fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact inMut_w p (d := 512) (k := 240) (.inr (.inr (.inr ⟨by decide, by decide⟩)))
    · exact inMut_w p (d := 768) (k := 512) (.inr (.inr (.inr ⟨by decide, by decide⟩)))
    · exact inMut_stk p
  refine WP.of_runBlock ⟨_, by grun [hbp₂], ?_⟩
  refine ⟨E.mut L (by gregs [hbp₂]; exact BitVec.add_sub_cancel _ _) (by gregs [hsp₂]) (by gmems [P.rd])
    (by gmems [P.wr]) (by gmems []; exact fm), by gmems [P.rd], by gmems [P.wr], ?_, by gmems []; exact f, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> (gregs []; rw [P.saved _ (by decide)]; gregs [])
  have o := P.out
  rw [L.aW (by decide), L.aW (by decide)] at o
  gmems []
  exact o

/-- The call of `vg_aes_expand_key` on the encryption key is constant time. -/
theorem callKey_ct (v : GcmImpl) {p : Prm} (L : Lay p) {I : State → Prop}
    (hI : ∀ s, I s → Env p s ∧ s.gpr .eax = p.W + BitVec.ofNat 32 32 ∧
      s.gpr .ecx = BitVec.ofNat 32 (Spec.GcmSiv.keyLen p.R) ∧ s.gpr .edx = p.W + BitVec.ofNat 32 512) :
    CT I (callKey v.callees) := by
  have call : ∀ s, I s → ∀ s', runBlock isa [.alu .add .ebp (imm scrO)] s = some s' →
      KeyCall s' (p.W + BitVec.ofNat 32 32) (p.W + BitVec.ofNat 32 512) (p.W + BitVec.ofNat 32 768)
        (Spec.GcmSiv.keyLen p.R) ∧ s'.gpr .esp = p.SP := by
    intro s hs s' run
    obtain ⟨E, eax, ecx, edx⟩ := hI s hs
    have e := run
    simp (disch := first | decide | omega_arith) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
      imm, scrO, Option.bind_some, Option.some.injEq] at e
    subst e
    have e768 : s.gpr .ebp + BitVec.ofNat 32 768 = p.W + BitVec.ofNat 32 768 := by rw [E.ebp]
    exact ⟨kargs L (by gregs [E.esp]) (E.perm.of_eq (by gmems []) (by gmems [])) (by gregs [eax]) (by gregs [ecx])
      (by gregs [edx]) (by gregs [e768]), by gregs [E.esp]⟩
  refine CT.seq (J := fun s' => ∃ s, I s ∧ runBlock isa [.alu .add .ebp (imm scrO)] s = some s')
    (CT.taint [.ebp] (pin_ebp fun s h => (hI s h).1.ebp) (by taint_decide))
    (fun s hs => WP.of_runBlock ⟨_, by grun [], s, hs, by grun []⟩) ?_
  refine CT.seq (J := fun s => s.gpr .ebp = p.W + BitVec.ofNat 32 768)
    (Proof.AesGcm.X86.key_ct v (E := p.SP) fun s ⟨s₀, h₀, run⟩ => call s₀ h₀ s run)
    (fun s ⟨s₀, h₀, run⟩ => WP.mono (Proof.AesGcm.X86.key_call v (call s₀ h₀ s run).1) fun s₁ g => by
      rw [g.saved .ebp (by decide), (call s₀ h₀ s run).1.ebp]) ?_
  exact CT.taint [.ebp] (pin_ebp fun _ h => h) (by taint_decide)

end VG.Proof.AesGcmSiv.X86

end

end

/-!
# AES-GCM-SIV on x86: the message keys (`derive`)

Untrusted: everything here is checked by Lean. Each step of `derive` writes
`little_endian_uint32(i) ‖ nonce` at `W + 112` and a zero block at
`W + 224` (`derArgs_ok`), on which `vg_aes_ctr32_to` leaves
`CIPH_K(little_endian_uint32(i) ‖ nonce)`, of which the first 8 bytes are
kept at `W + 16 + 8 i` (`derPost_ok`): after the loop, the halves of
`derive_keys` (`derive_ok`, `DInv.keys`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcmSiv.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac (le4)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4)
open VG.Proof.AesGcm.X86 (w64 toNat_ofNat32 toNat_add32 slotv slotv_eq zero4_fold zero4_bytes' length_bytesAt
  GcmImpl CT readW_writeW_off)

/-! ## Arithmetic -/

theorem ofNat_add32 (a b : Nat) : BitVec.ofNat 32 a + BitVec.ofNat 32 b = BitVec.ofNat 32 (a + b) := by
  rw [BitVec.ofNat_add]

/-- The offset of the 8 bytes a step keeps, as the code computes it. -/
theorem eaKeep {W : BitVec 32} {i k : Nat} (hw : W.toNat + 2816 ≤ 2 ^ 32) (hi : 8 * i + k < 2816) :
    w64 (BitVec.ofNat 32 i + BitVec.ofNat 32 i + (BitVec.ofNat 32 i + BitVec.ofNat 32 i) +
      (BitVec.ofNat 32 i + BitVec.ofNat 32 i + (BitVec.ofNat 32 i + BitVec.ofNat 32 i)) + W + BitVec.ofNat 32 k) =
      w64 W + BitVec.ofNat 64 (k + 8 * i) := by
  simp only [ofNat_add32]
  rw [BitVec.add_comm (BitVec.ofNat 32 _) W, BitVec.add_assoc, ofNat_add32]
  exact Proof.AesGcm.X86.w64_add (by omega_arith) |>.trans (by congr 2; omega_arith)

/-- A block as its four words. -/
theorem bytesAt_words (m : Mem) (p : Addr) (d : Nat) :
    bytesAt m (p + BitVec.ofNat 64 d) 16 = le4 (m.readW (p + BitVec.ofNat 64 d) 32) ++
      le4 (m.readW (p + BitVec.ofNat 64 (d + 4)) 32) ++ le4 (m.readW (p + BitVec.ofNat 64 (d + 8)) 32) ++
      le4 (m.readW (p + BitVec.ofNat 64 (d + 12)) 32) := by
  rw [Proof.Cmac.bytesAt_split4, add_ofNat_assoc, add_ofNat_assoc, add_ofNat_assoc, Proof.Cmac.le4_readW,
    Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW]

/-! ## A step's block -/

/-- The memory after a step's block. -/
def derMem (m : Mem) (W N : Addr) (i : Nat) : Mem :=
  Proof.Cmac.zero4 ((((m.writeW (W + BitVec.ofNat 64 116) (m.readW N 32)).writeW (W + BitVec.ofNat 64 120)
      (m.readW (N + BitVec.ofNat 64 4) 32)).writeW (W + BitVec.ofNat 64 124) (m.readW (N + BitVec.ofNat 64 8) 32)).writeW
    (W + BitVec.ofNat 64 112) (BitVec.ofNat 32 i)) (W + BitVec.ofNat 64 224)

/-- The arguments of a step: the counter block and a zero block. -/
theorem derArgs_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {i : Nat}
    (hi : slotv t.mem p.W iO = BitVec.ofNat 32 i) :
    ∃ t₁ : State, runBlock isa deriveBlock t = some t₁ ∧ t₁.mem = derMem t.mem (w64 p.W) (w64 p.N) i ∧
      t₁.gpr .eax = p.K ∧ t₁.gpr .ecx = BitVec.ofNat 32 p.R ∧ t₁.gpr .edx = p.W + BitVec.ofNat 32 112 ∧
      t₁.gpr .ebx = p.W + BitVec.ofNat 32 224 ∧ t₁.gpr .edi = BitVec.ofNat 32 1 ∧
      t₁.gpr .ebp = p.W ∧ t₁.gpr .esp = p.SP ∧ t₁.gpr .esi = t.gpr .esi ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have S := E.slots
  obtain n₀ := E.perm.nR (d := 0) (k := 4) (by decide)
  obtain n₄ := E.perm.nR (d := 4) (k := 4) (by decide)
  obtain n₈ := E.perm.nR (d := 8) (k := 4) (by decide)
  obtain hz := zero4_fold (t.mem.writeW (w64 p.W + BitVec.ofNat 64 116) (t.mem.readW (w64 p.N) 32) |>.writeW
      (w64 p.W + BitVec.ofNat 64 120) (t.mem.readW (w64 p.N + BitVec.ofNat 64 4) 32) |>.writeW
      (w64 p.W + BitVec.ofNat 64 124) (t.mem.readW (w64 p.N + BitVec.ofNat 64 8) 32) |>.writeW
      (w64 p.W + BitVec.ofNat 64 112) (BitVec.ofNat 32 i)) p.W 224
  simp only [Nat.reduceAdd] at hz
  simp only [slotv_eq] at hi
  have hN := S.nonce
  have hK := S.ctx
  have hR := S.rounds
  simp only [slotv_eq, nonceO, ctxO, roundsO, iO] at hN hK hR hi
  refine ⟨_, by simp only [deriveBlock, zero4]; grun [E.ebp, L.aW, L.aN, E.perm.wW, E.perm.wR, hN, n₀, n₄, n₈],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · gmems [hi, BitVec.add_zero, hz, derMem]
  · gregs [hK]
  · gregs [hR]
  · gregs [E.ebp]
  · gregs [E.ebp]
  · gregs []
  · gregs [E.ebp]
  · gregs [E.esp]
  · gregs []
  all_goals rfl

/-- The counter block of a step: `little_endian_uint32(i) ‖ nonce`. -/
theorem derBlock_bytes (m : Mem) (W N : Addr) (i : Nat) :
    bytesAt (derMem m W N i) (W + BitVec.ofNat 64 112) 16 = Spec.GcmSiv.le32 i ++ bytesAt m N 12 := by
  rw [derMem, Proof.Cmac.zero4, Proof.AesGcm.X86.bytesAt_frame (Proof.Cmac.frame_store4 _ _ _ _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)) (by decide),
    bytesAt_words]
  simp (disch := decide) only [Nat.reduceAdd, Mem.readW_writeW_self32, readW_writeW_off]
  rw [GcmSiv.le4_ofNat, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW,
    show (12 : Nat) = 4 + (4 + 4) from rfl, Proof.Cmac.bytesAt_add, Proof.Cmac.bytesAt_add, add_ofNat_assoc]
  simp only [List.append_assoc]

/-- The zero block of a step. -/
theorem derZero_block (W N : Addr) (m : Mem) (i : Nat) :
    Spec.Gcm.blockAt (derMem m W N i) (W + BitVec.ofNat 64 224) = 0 := by
  rw [derMem, Spec.Gcm.blockAt, Proof.Cmac.zero4_bytes]
  decide

theorem derMem_frame (m : Mem) (W N : Addr) (i : Nat) :
    Frame [⟨W + BitVec.ofNat 64 112, 16⟩, ⟨W + BitVec.ofNat 64 224, 16⟩] m (derMem m W N i) := by
  obtain c : ∀ d, 112 ≤ d → d + 4 ≤ 128 → (⟨W + BitVec.ofNat 64 112, 16⟩ : Region).Contains (W + BitVec.ofNat 64 d)
      (32 / 8) := fun d h₁ h₂ => Offset.contains W (by omega_arith) (by omega_arith) (by omega_arith)
  have mem₀ : (⟨W + BitVec.ofNat 64 112, 16⟩ : Region) ∈
      [(⟨W + BitVec.ofNat 64 112, 16⟩ : Region), ⟨W + BitVec.ofNat 64 224, 16⟩] := List.mem_cons_self
  refine (((((Frame.refl _ _).writeW mem₀ _ (c 116 (by decide) (by decide))).writeW mem₀ _
    (c 120 (by decide) (by decide))).writeW mem₀ _ (c 124 (by decide) (by decide))).writeW mem₀ _
    (c 112 (by decide) (by decide))).trans ((Proof.Cmac.frame_store4 _ _ _ _ _).mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_of_mem _ List.mem_cons_self)

/-! ## After a step's call -/

/-- What the code after the call of a step writes: the 8 bytes kept, and
the next `i`. -/
def postMem (m : Mem) (W : Addr) (i : Nat) : Mem :=
  ((m.writeW (W + BitVec.ofNat 64 (16 + 8 * i)) (m.readW (W + BitVec.ofNat 64 224) 32)).writeW
    (W + BitVec.ofNat 64 (20 + 8 * i)) (m.readW (W + BitVec.ofNat 64 228) 32)).writeW (W + BitVec.ofNat 64 180)
    (BitVec.ofNat 32 (i + 1))

/-- The code after the call of a step. -/
theorem derPost_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {i : Nat} (hi : i < p.R / 2 - 1)
    (hix : slotv t.mem p.W iO = BitVec.ofNat 32 i) :
    ∃ t' : State, runBlock isa derivePost t = some t' ∧ t'.mem = postMem t.mem (w64 p.W) i ∧
      t'.zf = some (decide (i + 1 = p.R / 2 - 1)) ∧ t'.gpr .ebp = p.W ∧ t'.gpr .esp = p.SP ∧
      t'.gpr .esi = t.gpr .esi ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have hR := L.rounds
  have S := E.slots
  have hRs := S.rounds
  simp only [slotv_eq, iO, roundsO] at hix hRs
  obtain hi6 : i ≤ 5 := by rcases hR with h | h <;> rw [h] at hi <;> omega_arith
  obtain ea₀ := eaKeep (W := p.W) (i := i) (k := 16) L.ww (by omega_arith)
  obtain ea₁ := eaKeep (W := p.W) (i := i) (k := 20) L.ww (by omega_arith)
  obtain wo₀ := E.perm.wW (d := 16 + 8 * i) (n := 4) (by omega_arith)
  obtain wo₁ := E.perm.wW (d := 20 + 8 * i) (n := 4) (by omega_arith)
  obtain r224 : (t.mem.writeW (w64 p.W + BitVec.ofNat 64 (16 + 8 * i)) (t.mem.readW (w64 p.W + BitVec.ofNat 64 224) 32)).readW
      (w64 p.W + BitVec.ofNat 64 228) 32 = t.mem.readW (w64 p.W + BitVec.ofNat 64 228) 32 :=
    readW_writeW_off _ _ _ (by omega_arith) (by decide) (by omega_arith)
  obtain rI : ((t.mem.writeW (w64 p.W + BitVec.ofNat 64 (16 + 8 * i)) (t.mem.readW (w64 p.W + BitVec.ofNat 64 224) 32)).writeW
      (w64 p.W + BitVec.ofNat 64 (20 + 8 * i)) (t.mem.readW (w64 p.W + BitVec.ofNat 64 228) 32)).readW
      (w64 p.W + BitVec.ofNat 64 180) 32 = t.mem.readW (w64 p.W + BitVec.ofNat 64 180) 32 := by
    rw [readW_writeW_off _ _ _ (by omega_arith) (by decide) (by omega_arith), readW_writeW_off _ _ _ (by omega_arith) (by decide) (by omega_arith)]
  obtain rR : ∀ v, (((t.mem.writeW (w64 p.W + BitVec.ofNat 64 (16 + 8 * i)) (t.mem.readW (w64 p.W + BitVec.ofNat 64 224) 32)).writeW
      (w64 p.W + BitVec.ofNat 64 (20 + 8 * i)) (t.mem.readW (w64 p.W + BitVec.ofNat 64 228) 32)).writeW
      (w64 p.W + BitVec.ofNat 64 180) v).readW (w64 p.W + BitVec.ofNat 64 148) 32 =
      t.mem.readW (w64 p.W + BitVec.ofNat 64 148) 32 := fun v => by
    rw [readW_writeW_off _ _ _ (by decide) (by decide) (by decide), readW_writeW_off _ _ _ (by omega_arith) (by decide) (by omega_arith),
      readW_writeW_off _ _ _ (by omega_arith) (by decide) (by omega_arith)]
  refine ⟨_, by simp only [derivePost]; grun [E.ebp, L.aW, E.perm.wW, E.perm.wR, hix, ea₀, ea₁, wo₀, wo₁, r224, rI, rR,
    hRs], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · gmems [hix, ofNat_add32, postMem]
  · gmems [hix, hRs, rR, ofNat_add32]
    rw [ofNat_lsr32 L.R_lt, Nat.pow_one, show BitVec.ofNat 32 (p.R / 2) - BitVec.ofNat 32 1 =
      BitVec.ofNat 32 (p.R / 2 - 1) by rcases hR with h | h <;> rw [h] <;> decide,
      Proof.AesGcm.X86.sub_beq32 (by omega_arith) (by rcases hR with h | h <;> rw [h] <;> decide)]
  · gregs [E.ebp]
  · gregs [E.esp]
  · gregs []
  all_goals rfl

theorem postMem_frame (m : Mem) (W : Addr) (i : Nat) (hi : 8 * i + 24 < 2 ^ 64) :
    Frame [⟨W + BitVec.ofNat 64 (16 + 8 * i), 8⟩, ⟨W + BitVec.ofNat 64 180, 4⟩] m (postMem m W i) := by
  obtain c₀ : (⟨W + BitVec.ofNat 64 (16 + 8 * i), 8⟩ : Region).Contains (W + BitVec.ofNat 64 (16 + 8 * i)) (32 / 8) :=
    Offset.contains W (by omega_arith) (by omega_arith) (by omega_arith)
  obtain c₁ : (⟨W + BitVec.ofNat 64 (16 + 8 * i), 8⟩ : Region).Contains (W + BitVec.ofNat 64 (20 + 8 * i)) (32 / 8) :=
    Offset.contains W (by omega_arith) (by omega_arith) (by omega_arith)
  unfold postMem
  exact (((Frame.refl _ _).writeW List.mem_cons_self _ c₀).writeW List.mem_cons_self _ c₁).writeW
    (List.mem_cons_of_mem _ List.mem_cons_self) _ (Region.contains_self _ _)

/-- The 8 bytes a step keeps: the first 8 of the block at `W + 224`. -/
theorem postMem_bytes (m : Mem) (W : Addr) {i : Nat} (hi : i ≤ 5) :
    bytesAt (postMem m W i) (W + BitVec.ofNat 64 (16 + 8 * i)) 8 = bytesAt m (W + BitVec.ofNat 64 224) 8 := by
  obtain e : W + BitVec.ofNat 64 (20 + 8 * i) = W + BitVec.ofNat 64 (16 + 8 * i) + BitVec.ofNat 64 4 := by
    rw [add_ofNat_assoc]; congr 2; omega_arith
  obtain d : (⟨W + BitVec.ofNat 64 (16 + 8 * i), 4⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 (20 + 8 * i), 4⟩ :=
    Offset.disjoint W (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
  obtain d₁ : (⟨W + BitVec.ofNat 64 180, 4⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 (16 + 8 * i), 4⟩ :=
    Offset.disjoint W (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
  obtain d₂ : (⟨W + BitVec.ofNat 64 180, 4⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 (20 + 8 * i), 4⟩ :=
    Offset.disjoint W (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
  rw [show (8 : Nat) = 4 + 4 from rfl, Proof.Cmac.bytesAt_add, Proof.Cmac.bytesAt_add, ← e,
    ← Proof.Cmac.le4_readW, ← Proof.Cmac.le4_readW, ← Proof.Cmac.le4_readW, ← Proof.Cmac.le4_readW, postMem,
    Proof.Cmac.readW_writeW_disj _ d₁, Proof.Cmac.readW_writeW_disj _ d₂,
    Proof.Cmac.readW_writeW_disj _ d.symm, Mem.readW_writeW_self32, Mem.readW_writeW_self32, add_ofNat_assoc]

/-! ## The loop -/

/-- What `derive` writes. -/
abbrev derR (p : Prm) : List Region :=
  [⟨w64 p.W + BitVec.ofNat 64 16, 48⟩, ⟨w64 p.W + BitVec.ofNat 64 112, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 176, 8⟩,
    ⟨w64 p.W + BitVec.ofNat 64 224, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 768, 2048⟩, stk p]

theorem inMut_derR (p : Prm) : InMut p (derR p) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact inMut_w p (.inl (by decide))
  · exact inMut_w p (.inl (by decide))
  · exact inMut_w p (.inr (.inl ⟨by decide, by decide⟩))
  · exact inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩)))
  · exact inMut_w p (.inr (.inr (.inr ⟨by decide, by decide⟩)))
  · exact inMut_stk p

/-- After `i` steps of `derive` from `σ`: the first `8 i` bytes of the halves
at `W + 16`. -/
structure DInv (p : Prm) (σ : State) (i : Nat) (t : State) : Prop where
  env : Env p t
  ix : slotv t.mem p.W iO = BitVec.ofNat 32 i
  le : i ≤ p.R / 2 - 1
  esi : t.gpr .esi = σ.gpr .esi
  rd : t.rd = σ.rd
  wr : t.wr = σ.wr
  frame : Frame (derR p) σ.mem t.mem
  out : bytesAt t.mem (w64 p.W + BitVec.ofNat 64 16) (8 * i) =
    GcmSiv.halves (Spec.GcmSiv.ctxCiph σ.mem (w64 p.K) p.R) (bytesAt σ.mem (w64 p.N) 12) i

/-- A step of `derive`. -/
theorem derStep_ok (v : GcmImpl) {p : Prm} (L : Lay p) {σ : State} {i : Nat} (hi : i < p.R / 2 - 1) {t : State}
    (I : DInv p σ i t) :
    WP isa (.seq (.block deriveBlock) (.seq (callCtr v.callees) (.block derivePost))) t fun t' =>
      DInv p σ (i + 1) t' ∧ t'.zf = some (decide (i + 1 = p.R / 2 - 1)) := by
  have hR := L.rounds
  have hw := L.ww
  obtain hi6 : i ≤ 5 := by rcases hR with h | h <;> rw [h] at hi <;> omega_arith
  obtain fm := frame_toMut I.frame (inMut_derR p)
  obtain eN : bytesAt t.mem (w64 p.N) 12 = bytesAt σ.mem (w64 p.N) 12 := nonce_mut L fm
  obtain eK := ciph_mut L fm
  obtain ⟨t₁, run₁, hm₁, eax, ecx, edx, ebx, edi, ebp₁, esp₁, esi₁, rd₁, wr₁⟩ := derArgs_ok L I.env I.ix
  obtain f₁ : Frame [⟨w64 p.W + BitVec.ofNat 64 112, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 224, 16⟩] t.mem t₁.mem := by
    rw [hm₁]; exact derMem_frame _ _ _ _
  obtain E₁ : Env p t₁ := I.env.mut L ebp₁ esp₁ rd₁ wr₁ (frame_toMut f₁ fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact inMut_w p (.inl (by decide))
    · exact inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩))))
  obtain hb₁ : bytesAt t₁.mem (w64 p.W + BitVec.ofNat 64 112) 16 =
      Spec.GcmSiv.le32 i ++ bytesAt t.mem (w64 p.N) 12 := by
    rw [hm₁]; exact derBlock_bytes _ _ _ _
  obtain hz₁ : Spec.Gcm.blockAt t₁.mem (w64 p.W + BitVec.ofNat 64 224) = 0 := by
    rw [hm₁]; exact derZero_block _ _ _ _
  obtain hD : Dst p t₁ p.K (p.W + BitVec.ofNat 32 224) (16 * 1) :=
    dstW L E₁.perm (q := 224) (.inr ⟨by decide, by decide⟩) (L.k_w' (by decide))
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (callCtr_ok v L E₁ (keyK L E₁.perm) hD
    (by rw [L.aW (by decide)]; exact inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩)))) eax ecx edx ebx edi)
    fun t₂ P => ?_)
  have E₂ := P.env
  obtain hix₂ : slotv t₂.mem p.W iO = BitVec.ofNat 32 i := by
    have := I.ix
    rw [← this]
    refine (P.frame.readW (r := ⟨w64 p.W + BitVec.ofNat 64 180, 4⟩) (Region.contains_self _ _) (fun r hr => ?_)
      (by decide)).trans (f₁.readW (r := ⟨w64 p.W + BitVec.ofNat 64 180, 4⟩) (Region.contains_self _ _)
      (fun r hr => ?_) (by decide))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · rw [L.aW (by decide)]; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.bw' (by decide)).symm
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  have fc := P.frame
  have hout := P.out
  rw [L.aW (show 224 < 2816 by decide)] at fc hout
  obtain ⟨t₃, run₃, hm₃, z₃, ebp₃, esp₃, esi₃, rd₃, wr₃⟩ := derPost_ok L E₂ hi hix₂
  obtain f₃ : Frame [⟨w64 p.W + BitVec.ofNat 64 (16 + 8 * i), 8⟩, ⟨w64 p.W + BitVec.ofNat 64 180, 4⟩] t₂.mem t₃.mem := by
    rw [hm₃]; exact postMem_frame _ _ _ (by omega_arith)
  obtain E₃ : Env p t₃ := E₂.mut L ebp₃ esp₃ rd₃ wr₃ (frame_toMut f₃ fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact inMut_w p (.inl (by omega_arith))
    · exact inMut_w p (.inr (.inl ⟨by decide, by decide⟩)))
  refine WP.of_runBlock ⟨t₃, run₃, ⟨E₃, ?_, by omega_arith, ?_, ?_, ?_, ?_, ?_⟩, z₃⟩
  · -- The next `i`.
    rw [slotv_eq, hm₃, postMem, Mem.readW_writeW_self32]
  · rw [esi₃, P.saved _ (by decide), esi₁, I.esi]
  · rw [rd₃, P.rd, rd₁, I.rd]
  · rw [wr₃, P.wr, wr₁, I.wr]
  · -- The frame.
    obtain mem : ∀ {r : Region}, r ∈ derR p → ∃ r' ∈ derR p, Region.Sub r r' := fun {r} h => ⟨r, h, fun _ h => h⟩
    refine ((I.frame.trans (f₁.sub fun r hr => ?_)).trans (fc.sub fun r hr => ?_)).trans (f₃.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact mem (by simp)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact mem (by simp)
      · simp only [Nat.mul_one]; exact mem (by simp)
      · exact mem (by simp)
      · exact mem (by simp)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, Offset.sub _ (by omega_arith) (by omega_arith)⟩
      · exact ⟨⟨w64 p.W + BitVec.ofNat 64 176, 8⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  · -- The bytes.
    obtain dW : ∀ {d k : Nat}, d + k ≤ 2816 → 16 + 8 * i ≤ d ∨ d + k ≤ 16 →
        (⟨w64 p.W + BitVec.ofNat 64 16, 8 * i⟩ : Region).Disjoint ⟨w64 p.W + BitVec.ofNat 64 d, k⟩ :=
      fun h₁ h₂ => Lay.w_w (by omega_arith) (by omega_arith) h₁
    obtain keep : bytesAt t₃.mem (w64 p.W + BitVec.ofNat 64 16) (8 * i) =
        bytesAt t.mem (w64 p.W + BitVec.ofNat 64 16) (8 * i) := by
      rw [Proof.AesGcm.X86.bytesAt_frame f₃ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact dW (by omega_arith) (by omega_arith)
          · exact dW (by decide) (by omega_arith)) (by omega_arith),
        Proof.AesGcm.X86.bytesAt_frame fc (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · exact dW (by decide) (by omega_arith)
          · simp only [Nat.mul_one]; exact dW (by decide) (by omega_arith)
          · exact dW (by decide) (by omega_arith)
          · exact (L.bw' (by omega_arith)).symm) (by omega_arith),
        Proof.AesGcm.X86.bytesAt_frame f₁ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> exact dW (by decide) (by omega_arith)) (by omega_arith)]
    simp only [Spec.Gcm.blocksAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero,
      hz₁, Proof.Cmac.ctr32_one, List.cons.injEq, and_true] at hout
    obtain last : bytesAt t₃.mem (w64 p.W + BitVec.ofNat 64 (16 + 8 * i)) 8 =
        (Spec.GcmSiv.ctxCiph σ.mem (w64 p.K) p.R
          (Spec.GcmSiv.le32 i ++ bytesAt σ.mem (w64 p.N) 12)).take 8 := by
      obtain e16 : bytesAt t₂.mem (w64 p.W + BitVec.ofNat 64 224) 16 =
          bytesAt t₂.mem (w64 p.W + BitVec.ofNat 64 224) 8 ++
            bytesAt t₂.mem (w64 p.W + BitVec.ofNat 64 224 + BitVec.ofNat 64 8) 8 :=
        Proof.Cmac.bytesAt_add _ _ 8 8
      obtain ek₁ : Spec.GcmSiv.ctxCiph t₁.mem (w64 p.K) p.R = Spec.GcmSiv.ctxCiph t.mem (w64 p.K) p.R := by
        unfold Spec.GcmSiv.ctxCiph
        rw [Proof.AesGcm.X86.bytesAt_frame f₁ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> exact (L.k_w' (by decide)).sub_left (Region.sub_prefix L.rounds_le))
          (by omega_arith)]
      rw [hm₃, postMem_bytes _ _ hi6,
        show bytesAt t₂.mem (w64 p.W + BitVec.ofNat 64 224) 8 =
          (bytesAt t₂.mem (w64 p.W + BitVec.ofNat 64 224) 16).take 8 by
          rw [e16, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)],
        Proof.Cmac.bytesAt_blockAt, hout, Spec.Gcm.blockAt, hb₁,
        Proof.Cmac.aesWith_bytes _ _ (by rw [List.length_append, Proof.Cmac.bytesAt_length]; rfl),
        ← GcmSiv.aesWith_eq, show Spec.GcmSiv.aesWith p.R (bytesAt t₁.mem (w64 p.K) (16 * (p.R + 1))) =
          Spec.GcmSiv.ctxCiph t₁.mem (w64 p.K) p.R from rfl, ek₁, eK, eN]
    rw [show 8 * (i + 1) = 8 * i + 8 by omega_arith, Proof.Cmac.bytesAt_add, GcmSiv.halves_succ, ← I.out, keep,
      add_ofNat_assoc, last]

/-- The start of `derive`: `i = 0`. -/
theorem derive0_ok {p : Prm} (L : Lay p) {σ : State} (E : Env p σ) :
    ∃ t₀, runBlock isa [.mov .eax (imm 0), .store (at_ .ebp iO) .eax] σ = some t₀ ∧ DInv p σ 0 t₀ := by
  refine ⟨_, by grun [E.ebp, L.aW, E.perm.wW], ?_⟩
  obtain f : Frame [⟨w64 p.W + BitVec.ofNat 64 180, 4⟩] σ.mem
      (σ.mem.writeW (w64 p.W + BitVec.ofNat 64 180) (BitVec.ofNat 32 0)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain f' : Frame (derR p) σ.mem (σ.mem.writeW (w64 p.W + BitVec.ofNat 64 180) (BitVec.ofNat 32 0)) :=
    f.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨w64 p.W + BitVec.ofNat 64 176, 8⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  refine ⟨E.mut L (by gregs [E.ebp]) (by gregs [E.esp]) (by gmems []) (by gmems [])
      (by gmems []; exact frame_toMut f' (inMut_derR p)),
    by gmems [slotv_eq], Nat.zero_le _, by gregs [], by gmems [], by gmems [], by gmems []; exact f', ?_⟩
  simp [GcmSiv.halves, bytesAt]

/-- `derive`: the halves of `derive_keys` at `W + 16`. -/
theorem derive_ok (v : GcmImpl) {p : Prm} (L : Lay p) {σ : State} (E : Env p σ) :
    WP isa (derive v.callees) σ (DInv p σ (p.R / 2 - 1)) := by
  have hR := L.rounds
  obtain ⟨t₀, run₀, I₀⟩ := derive0_ok L E
  unfold derive
  refine WP.seq (WP.of_runBlock ⟨t₀, run₀, ?_⟩)
  refine WP.loop (M := isa) (fun m t => ∃ i, m = (p.R / 2 - 1) - i ∧ i < p.R / 2 - 1 ∧ DInv p σ i t) ?_
    ((p.R / 2 - 1) - 0) _ ⟨0, rfl, by rcases hR with h | h <;> rw [h] <;> decide, I₀⟩
  rintro m t ⟨i, rfl, hi, I⟩
  refine WP.mono (derStep_ok v L hi I) fun t' ⟨I', hz⟩ => ?_
  obtain ev := eval_ne hz
  by_cases he : i + 1 = p.R / 2 - 1
  · left; exact ⟨ev.trans (by simp [he]), he ▸ I'⟩
  · right; exact ⟨ev.trans (by simp [he]), (p.R / 2 - 1) - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, I'⟩

/-- After `derive`, the message keys: the authentication key at `W + 16`, the
encryption key at `W + 32`. -/
theorem DInv.keys {p : Prm} (L : Lay p) {σ t : State} (I : DInv p σ (p.R / 2 - 1) t) :
    Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph σ.mem (w64 p.K) p.R) (Spec.GcmSiv.keyLen p.R)
        (bytesAt σ.mem (w64 p.N) 12) =
      (bytesAt t.mem (w64 p.W + BitVec.ofNat 64 16) 16,
        bytesAt t.mem (w64 p.W + BitVec.ofNat 64 32) (Spec.GcmSiv.keyLen p.R)) := by
  have hR := L.rounds
  obtain hk : Spec.GcmSiv.keyLen p.R / 8 + 2 = p.R / 2 - 1 := by unfold Spec.GcmSiv.keyLen; omega_arith
  obtain hl : 8 * (p.R / 2 - 1) = 16 + Spec.GcmSiv.keyLen p.R := by unfold Spec.GcmSiv.keyLen; omega_arith
  have e := I.out
  rw [hl, Proof.Cmac.bytesAt_add, add_ofNat_assoc] at e
  rw [GcmSiv.deriveKeys_eq (GcmSiv.ctxCiph_length σ.mem _ p.R), hk, ← e,
    List.take_left' (Proof.Cmac.bytesAt_length _ _ _), List.drop_left' (Proof.Cmac.bytesAt_length _ _ _)]

end VG.Proof.AesGcmSiv.X86
