import VerifiedGarbage.Proof.AesCcm.X86.Run
import VerifiedGarbage.Proof.CmacAes.Stream.X86.Call

/-!
# AES-CCM on x86: the functions called

Untrusted: everything here is checked by Lean. The calls of
`vg_cmac_aes_update` are those of streaming AES-CMAC
(`Proof.CmacAes.Stream.X86.upd_call`), and those of `vg_aes_ctr32` those of
AES-GCM (`Proof.AesGcm.X86.ctr_call`, whose frame and call depend only on
the implementation of `vg_aes_ctr32`), with `ebp` moved to the working space
around them (`ctrCall_ok`). Their arguments are built from the
environment: the key schedule, a block of `W` as the state or the counter
block, the data or blocks of `W` as the data (`Src`), and the working space
at `W + 384`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesCcm.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (blockAt blocksAt ctr32 aesWith)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (imm)
open VG.Proof.AesGcm.X86 (w64 toNat_ofNat32 toNat_add32 w64_add covers_left covers_cons covers_nil CtrCall CtrPost
  GcmImpl GhashImpl gpr_setMem)
open VG.Proof.CmacAes.Stream.X86 (UArgs UPost)

theorem below_sub56 {SP : BitVec 32} {k : Nat} (hk : k ≤ 56) (hs : 56 ≤ SP.toNat) :
    Region.Sub (below SP k) (below SP 56) :=
  VG.X86.below_sub hk hs

/-! ## Data for a call -/

/-- `k` bytes at `Q`, which the code may read, apart from the parts of `W`
from `384` on and the stack below `SP`. -/
structure Src (W SP : BitVec 32) (s : State) (Q : BitVec 32) (k : Nat) : Prop where
  rd : Covers [⟨w64 Q, k⟩] (s.rd ++ s.wr)
  wrap : Q.toNat + k ≤ 2 ^ 32
  qs : (⟨w64 Q, k⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 384, 2176⟩
  stk : (below SP 56).Disjoint ⟨w64 Q, k⟩

/-- Bytes of `W` below 384 as data. -/
theorem srcW {K W SP : BitVec 32} {s : State} (L : Lay K W SP) (P : Perm K W s) {t k : Nat} (hk : t + k ≤ 384) :
    Src W SP s (W + BitVec.ofNat 32 t) k where
  rd := by rw [L.aW (o := t) (by omega)]; exact covers_left (P.wC (by omega))
  wrap := by rw [L.nW (by omega)]; have := L.fw; omega
  qs := by rw [L.aW (o := t) (by omega)]; exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  stk := by rw [L.aW (o := t) (by omega)]; exact L.stk_w' (by omega)

/-- A buffer as data. -/
theorem srcBuf {W SP : BitVec 32} {s : State} {Q : BitVec 32} {k : Nat} (h : Buf W SP s Q k) : Src W SP s Q k :=
  ⟨h.rd, h.wrap, h.w.sub_right (Lay.wSub (by decide)), h.stk⟩

theorem Src.of_eq {W SP : BitVec 32} {s s' : State} {Q : BitVec 32} {k : Nat} (h : Src W SP s Q k)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Src W SP s' Q k :=
  { h with rd := by rw [hrd, hwr]; exact h.rd }

/-! ## `vg_cmac_aes_update` -/

/-- `W + d`, as the 64-bit address it is. -/
theorem wAddr {K W SP : BitVec 32} (L : Lay K W SP) {d : Nat} (hd : d < 2560) :
    (W + BitVec.ofNat 32 d).setWidth 64 = w64 W + BitVec.ofNat 64 d := L.aW hd

/-- The arguments of `vg_cmac_aes_update`: the key schedule, the state at
`W + y`, `n` blocks at `Q`, and the working space at `W + 384`. -/
theorem uargs {K W SP : BitVec 32} {s : State} (L : Lay K W SP) (E : Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {y : Nat} (hy : y + 16 ≤ 384) {Q : BitVec 32} {n : Nat}
    (hq : Src W SP s Q (16 * n)) (hqy : (⟨w64 Q, 16 * n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 y, 16⟩)
    (hn : 16 * n < 2 ^ 32) (eax : s.gpr .eax = K) (ecx : s.gpr .ecx = BitVec.ofNat 32 R)
    (edx : s.gpr .edx = W + BitVec.ofNat 32 y) (ebx : s.gpr .ebx = Q) (esi : s.gpr .esi = BitVec.ofNat 32 n)
    (edi : s.gpr .edi = W + BitVec.ofNat 32 384) :
    UArgs s K (W + BitVec.ofNat 32 y) Q (W + BitVec.ofNat 32 384) R n where
  eax := eax
  ecx := ecx
  edx := edx
  ebx := ebx
  esi := esi
  edi := edi
  rounds := hR
  esp := by rw [E.esp]; exact L.sp
  hn := hn
  wc := by rw [wAddr L (by omega)]; simpa using L.k_w' (a := 0) (n := 240) (d := y) (k := 16) (by decide) (by omega)
  ws := by rw [wAddr L (by omega)]; simpa using L.k_w' (a := 0) (n := 240) (d := 384) (k := 2176) (by decide) (by decide)
  dc := by rw [wAddr L (by omega)]; exact hqy
  ds := by rw [wAddr L (by omega)]; exact hq.qs
  cs := by rw [wAddr L (by omega), wAddr L (by omega)]; exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  bW := by rw [E.esp]; exact L.stk_k
  bD := by rw [E.esp]; exact hq.stk
  bC := by rw [E.esp, wAddr L (by omega)]; exact L.stk_w' (by omega)
  bS := by rw [E.esp, wAddr L (by omega)]; exact L.stk_w' (by decide)
  fW := by have := L.fk; omega
  fC := by rw [L.nW (by omega)]; have := L.fw; omega
  fD := hq.wrap
  fS := by rw [L.nW (by omega)]; have := L.fw; omega
  reads := covers_cons E.perm.k (covers_cons hq.rd covers_nil)
  writes := by
    rw [wAddr L (by omega), wAddr L (by omega)]
    exact covers_cons (E.perm.wC (by omega)) (covers_cons (E.perm.wC (by decide)) covers_nil)

/-- A call of `vg_cmac_aes_update`, with its arguments (`uargs`). -/
theorem updCall_ok (v : Ctr32Impl) {K W SP : BitVec 32} {s : State} (L : Lay K W SP) (E : Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {y : Nat} (hy : y + 16 ≤ 384) {Q : BitVec 32} {n : Nat}
    (hq : Src W SP s Q (16 * n)) (hqy : (⟨w64 Q, 16 * n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 y, 16⟩)
    (hn : 16 * n < 2 ^ 32) (eax : s.gpr .eax = K) (ecx : s.gpr .ecx = BitVec.ofNat 32 R)
    (edx : s.gpr .edx = W + BitVec.ofNat 32 y) (ebx : s.gpr .ebx = Q) (esi : s.gpr .esi = BitVec.ofNat 32 n)
    (edi : s.gpr .edi = W + BitVec.ofNat 32 384) :
    WP isa (updCall v.callee v.suffix) s fun s' => Env K W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      Frame [⟨w64 W + BitVec.ofNat 64 y, 16⟩, ⟨w64 W + BitVec.ofNat 64 384, 2176⟩, below SP 56] s.mem s'.mem ∧
      bytesAt s'.mem (w64 W + BitVec.ofNat 64 y) 16 =
        Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem (w64 K) R) (bytesAt s.mem (w64 W + BitVec.ofNat 64 y) 16)
          (Spec.Cmac.blocksAt s.mem (w64 Q) 16 n) := by
  refine WP.mono (Proof.CmacAes.Stream.X86.upd_call v (uargs L E hR hy hq hqy hn eax ecx edx ebx esi edi))
    fun s' h => ⟨E.keep (h.saved _ (by decide)) (h.saved _ (by decide)) h.rd h.wr, h.rd, h.wr, h.saved, ?_, ?_⟩
  · have f := h.frame
    rw [wAddr L (by omega), wAddr L (by omega), E.esp] at f
    exact f
  · have o := h.out
    rw [wAddr L (by omega)] at o
    exact o

/-! ## `vg_aes_ctr32` -/

/-- The frame and call of `vg_aes_ctr32`: AES-GCM's, with any implementation
of `vg_aes_ghash` beside it. -/
theorem ctrFrame_ok (v : Ctr32Impl) {s : State} {K C D S : BitVec 32} {R n : Nat} (h : CtrCall s K C D S R n) :
    WP isa (.frame (.push [.ebp, .edi, .ebx, .edx, .ecx, .eax]) (.call v.callee.name v.callee.code) (.pop .eax 6)) s
      (CtrPost s K C D S R n) :=
  Proof.AesGcm.X86.ctr_call ⟨v, .scalar⟩ h

/-- A call of `vg_aes_ctr32` on `n` blocks at `Q`, from the counter block at
`W + c`, with its working space at `W + 384`. -/
theorem ctrCall_ok (v : Ctr32Impl) {K W SP : BitVec 32} {s : State} (L : Lay K W SP) (E : Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {c : Nat} (hc : c + 16 ≤ 384) {Q : BitVec 32} {n : Nat}
    (hq : Src W SP s Q (16 * n)) (hqc : (⟨w64 Q, 16 * n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 c, 16⟩)
    (hqk : (⟨w64 K, 240⟩ : Region).Disjoint ⟨w64 Q, 16 * n⟩) (hqw : Covers [⟨w64 Q, 16 * n⟩] s.wr)
    (eax : s.gpr .eax = K) (ecx : s.gpr .ecx = BitVec.ofNat 32 R) (edx : s.gpr .edx = W + BitVec.ofNat 32 c)
    (ebx : s.gpr .ebx = Q) (edi : s.gpr .edi = BitVec.ofNat 32 n) :
    WP isa (ctrCall v.callee) s fun s' => Env K W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ [Reg.ebx, .esi, .edi], s'.gpr r = s.gpr r) ∧
      Frame [⟨w64 W + BitVec.ofNat 64 c, 16⟩, ⟨w64 Q, 16 * n⟩, ⟨w64 W + BitVec.ofNat 64 384, 2048⟩, below SP 56]
        s.mem s'.mem ∧
      blocksAt s'.mem (w64 Q) n = ctr32 (aesWith R (bytesAt s.mem (w64 K) (16 * (R + 1))))
        (blockAt s.mem (w64 W + BitVec.ofNat 64 c)) (blocksAt s.mem (w64 Q) n) := by
  have hsp := L.sp
  have b28 : Region.Sub (below SP 28) (below SP 56) := below_sub56 (by decide) hsp
  -- `ebp := W + 384`.
  refine WP.seq (WP.of_runBlock ⟨_, by crun [], ?_⟩)
  -- The call.
  refine WP.seq (WP.mono (ctrFrame_ok v (K := K) (C := W + BitVec.ofNat 32 c) (D := Q)
    (S := W + BitVec.ofNat 32 384) (R := R) (n := n) ?_) fun s₂ P => ?_)
  · have e384 : s.gpr .ebp + BitVec.ofNat 32 384 = W + BitVec.ofNat 32 384 := by rw [E.ebp]
    refine ⟨by cregs [eax], by cregs [ecx], by cregs [edx], by cregs [ebx], by cregs [edi], by cregs [e384], hR,
      by cregs [E.esp]; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [L.aW (o := c) (by omega)]; simpa using L.k_w' (a := 0) (n := 240) (d := c) (k := 16) (by decide) (by omega)
    · exact hqk
    · rw [L.aW (o := 384) (by omega)]
      simpa using L.k_w' (a := 0) (n := 240) (d := 384) (k := 2048) (by decide) (by decide)
    · rw [L.aW (o := c) (by omega)]; exact hqc.symm
    · rw [L.aW (o := c) (by omega), L.aW (o := 384) (by omega)]; exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
    · rw [L.aW (o := 384) (by omega)]; exact hq.qs.sub_right (Region.sub_prefix (by decide))
    · cregs [E.esp]; exact L.stk_k.sub_left b28
    · cregs [E.esp]; rw [L.aW (o := c) (by omega)]; exact (L.stk_w' (by omega)).sub_left b28
    · cregs [E.esp]; exact hq.stk.sub_left b28
    · cregs [E.esp]; rw [L.aW (o := 384) (by omega)]; exact (L.stk_w' (by decide)).sub_left b28
    · have := L.fk; omega
    · rw [L.nW (by omega)]; have := L.fw; omega
    · exact hq.wrap
    · rw [L.nW (by omega)]; have := L.fw; omega
    · cmems []; exact covers_cons E.perm.k covers_nil
    · cmems []; rw [L.aW (o := c) (by omega), L.aW (o := 384) (by omega)]
      exact covers_cons (E.perm.wC (by omega)) (covers_cons hqw (covers_cons (E.perm.wC (by decide)) covers_nil))
  -- `ebp := W`.
  have hbp₂ : s₂.gpr .ebp = W + BitVec.ofNat 32 384 := by
    rw [P.saved _ (by decide)]; cregs [E.ebp]
  have hsp₂ : s₂.gpr .esp = SP := by rw [P.saved _ (by decide)]; cregs [E.esp]
  refine WP.of_runBlock ⟨_, by crun [hbp₂], ?_⟩
  refine ⟨⟨by cregs [hbp₂]; exact BitVec.add_sub_cancel _ _, by cregs [hsp₂],
    E.perm.of_eq (by cmems [P.rd]) (by cmems [P.wr])⟩, by cmems [P.rd], by cmems [P.wr], ?_, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> (cregs []; rw [P.saved _ (by decide)]; cregs [])
  · have f := P.frame
    rw [L.aW (o := c) (by omega), L.aW (o := 384) (by omega)] at f
    cmems []
    refine f.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · refine ⟨below SP 56, by simp, ?_⟩
      have : (s.gpr .ebp + BitVec.ofNat 32 384).setWidth 64 = (W + BitVec.ofNat 32 384).setWidth 64 := by rw [E.ebp]
      simpa [gpr_setReg_of_ne, E.esp] using b28
  · have o := P.out
    rw [L.aW (o := c) (by omega)] at o
    cmems []
    exact o

end VG.Proof.AesCcm.X86
