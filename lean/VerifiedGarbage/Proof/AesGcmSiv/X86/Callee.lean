import VerifiedGarbage.Proof.AesGcmSiv.X86.Entry
import VerifiedGarbage.Proof.AesGcm.X86.Callee

/-!
# AES-GCM-SIV on x86: the functions called

Untrusted: everything here is checked by Lean. The calls of `vg_aes_ctr32`,
`vg_ghash` and `vg_aes_expand_key` are AES-GCM's (`Proof.AesGcm.X86`'s
`ctr_call`, `gh_call`, `key_call`), with `ebp` moved to the callee's working
space around them (`callCtr_ok`, `callGh_ok`, `callKey_ok`). Their arguments
are built from the environment:

* `vg_aes_ctr32`: a key schedule (`KeyOk`: the key-generating key's, or the
  encryption key's at `W + 512`), the counter block's copy at `W + 112`,
  `n` blocks at `D` (`Dst`), and the working space at `W + 768`;
* `vg_ghash`: GHASH's key at `W + 64`, the accumulator at `W + 80`, `n` (at
  most 64) reversed blocks at `W + 768` and the working space at
  `W + 1792`;
* `vg_aes_expand_key`: the encryption key at `W + 32`, its schedule at
  `W + 512` and the working space at `W + 768`.

Each call writes only parts of `mutR`, so `Env` holds after it.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcmSiv.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (blockAt blocksAt ctr32 aesWith ghashFrom)
open VG.Impl.AesGcm.X86 (imm)
open VG.Proof.AesGcm.X86 (w64 toNat_ofNat32 toNat_add32 w64_add covers_left covers_cons covers_nil CtrCall CtrPost
  GhCall GhPost KeyCall KeyPost GcmImpl gpr_setMem CT)

/-! ## `vg_aes_ctr32` -/

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
  wrap := by rw [L.nW (by decide)]; have := L.ww; omega
  kc := by rw [L.aW (by decide)]; exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  ks := by rw [L.aW (by decide)]; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  stk := by rw [L.aW (by decide)]; exact L.bw' (by decide)

/-- `k` bytes at `D` that `vg_aes_ctr32` may write: apart from the key
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

/-- A block of `W` as `vg_aes_ctr32`'s data, with the key schedule `Q`. -/
theorem dstW {p : Prm} {s : State} (L : Lay p) (P : Perm p s) {Q : BitVec 32} {q : Nat}
    (hq : q + 16 ≤ 128 ∧ (q + 16 ≤ 112 ∨ 128 ≤ q) ∨ 224 ≤ q ∧ q + 16 ≤ 256)
    (hk : (⟨w64 Q, 240⟩ : Region).Disjoint ⟨w64 p.W + BitVec.ofNat 64 q, 16⟩) :
    Dst p s Q (p.W + BitVec.ofNat 32 q) 16 where
  wr := by rw [L.aW (o := q) (by omega)]; exact P.wC (by omega)
  wrap := by rw [L.nW (o := q) (by omega)]; have := L.ww; omega
  dk := by rw [L.aW (o := q) (by omega)]; exact hk
  dc := by rw [L.aW (o := q) (by omega)]; exact Lay.w_w (by omega) (by omega) (by decide)
  ds := by rw [L.aW (o := q) (by omega)]; exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  stk := by rw [L.aW (o := q) (by omega)]; exact L.bw' (by omega)

/-- The arguments of `vg_aes_ctr32`: the key schedule at `Q`, the counter
block's copy at `W + 112`, `n` blocks at `D`, and the working space at
`W + 768` (where `ebp` is moved). -/
theorem cargs {p : Prm} {s : State} (L : Lay p) (esp : s.gpr .esp = p.SP) (P : Perm p s) {Q D : BitVec 32}
    {n : Nat} (hQ : KeyOk p s Q) (hD : Dst p s Q D (16 * n)) (eax : s.gpr .eax = Q)
    (ecx : s.gpr .ecx = BitVec.ofNat 32 p.R) (edx : s.gpr .edx = p.W + BitVec.ofNat 32 112)
    (ebx : s.gpr .ebx = D) (edi : s.gpr .edi = BitVec.ofNat 32 n)
    (ebp : s.gpr .ebp = p.W + BitVec.ofNat 32 768) :
    CtrCall s Q (p.W + BitVec.ofNat 32 112) D (p.W + BitVec.ofNat 32 768) p.R n := by
  have hsp := L.sp
  refine ⟨eax, ecx, edx, ebx, edi, ebp, L.rounds3, by rw [esp]; omega, ?_, hD.dk, ?_, ?_, ?_, hD.ds.sub_right ?_,
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
  · rw [L.nW (by decide)]; have := L.ww; omega
  · rw [L.nW (by decide)]; have := L.ww; omega
  · rw [L.aW (by decide), L.aW (by decide)]
    exact covers_cons (P.wC (by decide)) (covers_cons hD.wr (covers_cons (P.wC (by decide)) covers_nil))

/-- What a call of `vg_aes_ctr32` leaves. -/
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

/-- A call of `vg_aes_ctr32` on `n` blocks at `D`, which must lie in `mutR`,
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
      simpa [gpr_setReg_of_ne, E.esp] using L.stkSub (k := 28) (by decide)
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

/-- Calls of `vg_aes_ctr32` with the same arguments are constant time. -/
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
    simp (disch := first | decide | omega) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
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
  refine ⟨eax, edx, ebx, edi, ebp, by rw [esp]; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [L.aW (show 64 < 2816 by decide), L.aW (show 80 < 2816 by decide), L.aW (show 768 < 2816 by decide),
      L.aW (show 1792 < 2816 by decide), L.nW (show 64 < 2816 by decide), L.nW (show 80 < 2816 by decide),
      L.nW (show 768 < 2816 by decide), L.nW (show 1792 < 2816 by decide), esp]
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inl (by omega)) (by decide) (by omega)
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (L.bw' (by decide)).sub_left b24
  · exact (L.bw' (by decide)).sub_left b24
  · exact (L.bw' (by omega)).sub_left b24
  · exact (L.bw' (by decide)).sub_left b24
  · omega
  · omega
  · omega
  · omega
  · exact covers_cons (P.wCR (by decide)) (covers_cons (P.wCR (by omega)) covers_nil)
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
    simp (disch := first | decide | omega) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
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
  have hk32 : Spec.GcmSiv.keyLen p.R ≤ 32 := by omega
  refine ⟨eax, ecx, edx, ebp, by omega, by rw [esp]; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [L.aW (show 32 < 2816 by decide), L.aW (show 512 < 2816 by decide), L.aW (show 768 < 2816 by decide),
      L.nW (show 32 < 2816 by decide), L.nW (show 512 < 2816 by decide), L.nW (show 768 < 2816 by decide), esp]
  · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.bw' (by omega)).sub_left b20
  · exact (L.bw' (by decide)).sub_left b20
  · exact (L.bw' (by decide)).sub_left b20
  · omega
  · omega
  · omega
  · exact covers_cons (P.wCR (by omega)) covers_nil
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
    simp (disch := first | decide | omega) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
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
