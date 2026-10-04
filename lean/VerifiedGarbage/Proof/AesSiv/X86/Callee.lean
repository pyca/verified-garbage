import VerifiedGarbage.Proof.AesSiv.X86.Run
import VerifiedGarbage.Proof.AesSiv.X86.FinRaw

/-!
# AES-SIV on x86: the functions called

Untrusted: everything here is checked by Lean. The calls of
`vg_cmac_aes_update` are those of streaming AES-CMAC
(`Proof.CmacAes.Stream.X86.upd_call`), those of `vg_cmac_aes_finalize` from
any subkeys (`finr_call`), and those of `vg_aes_ctr32` those of AES-GCM
(`Proof.AesGcm.X86.ctr_call`), with `ebp` moved to the working space around
them (`ctrCall_ok`). Their arguments are built from the environment: the key
context, a block of `W` as the state or the counter block, the data or
blocks of `W` as the data (`Src`), and the working space at `W + 256`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesSiv.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (blockAt blocksAt ctr32 aesWith)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (imm)
open VG.Proof.AesGcm.X86 (w64 toNat_ofNat32 toNat_add32 w64_add covers_left covers_cons covers_nil CtrCall CtrPost
  GcmImpl gpr_setMem CT)
open VG.Proof.CmacAes.Stream.X86 (UArgs UPost FArgs)

theorem below_sub56 {SP : BitVec 32} {k : Nat} (hk : k ≤ 56) (hs : 56 ≤ SP.toNat) :
    Region.Sub (below SP k) (below SP 56) :=
  VG.X86.below_sub hk hs

/-- Where a state may be in `W`: below the working space of the functions
called, or above it (`D`). -/
abbrev StOk (y : Nat) : Prop := y + 16 ≤ 256 ∨ (2432 ≤ y ∧ y + 16 ≤ 2576)

theorem stOk_scr {W : BitVec 32} {y : Nat} (h : StOk y) :
    (⟨w64 W + BitVec.ofNat 64 y, 16⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 256, 2176⟩ := by
  rcases h with h | h
  · exact Lay.w_w (.inl h) (by omega) (by decide)
  · exact Lay.w_w (.inr (by omega)) (by omega) (by decide)

/-! ## Data for a call -/

/-- `k` bytes at `Q`, which the code may read, apart from the working space
of the functions called and the stack below `SP`. -/
structure Src (W SP : BitVec 32) (s : State) (Q : BitVec 32) (k : Nat) : Prop where
  rd : Covers [⟨w64 Q, k⟩] (s.rd ++ s.wr)
  wrap : Q.toNat + k ≤ 2 ^ 32
  qs : (⟨w64 Q, k⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 256, 2176⟩
  stk : (below SP 56).Disjoint ⟨w64 Q, k⟩

/-- Bytes of `W` below 256 as data. -/
theorem srcW {C W SP : BitVec 32} {s : State} (L : Lay C W SP) (P : Perm C W s) {t k : Nat} (hk : t + k ≤ 256) :
    Src W SP s (W + BitVec.ofNat 32 t) k where
  rd := by rw [L.aW (o := t) (by omega)]; exact covers_left (P.wC (by omega))
  wrap := by rw [L.nW (o := t) (by omega)]; have := L.fw; omega
  qs := by rw [L.aW (o := t) (by omega)]; exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  stk := by rw [L.aW (o := t) (by omega)]; exact L.stk_w' (by omega)

/-- A buffer as data. -/
theorem srcBuf {W SP : BitVec 32} {s : State} {Q : BitVec 32} {k : Nat} (h : Buf W SP s Q k) : Src W SP s Q k :=
  ⟨h.rd, h.wrap, h.w.sub_right (Lay.wSub (by decide)), h.stk⟩

theorem Src.of_eq {W SP : BitVec 32} {s s' : State} {Q : BitVec 32} {k : Nat} (h : Src W SP s Q k)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Src W SP s' Q k :=
  { h with rd := by rw [hrd, hwr]; exact h.rd }

theorem Src.take {W SP : BitVec 32} {s : State} {Q : BitVec 32} {k j : Nat} (h : Src W SP s Q k) (hj : j ≤ k) :
    Src W SP s Q j where
  rd := fun a m ⟨r, hr, hc⟩ => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.rd a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩
  wrap := by have := h.wrap; omega
  qs := h.qs.sub_left (Region.sub_prefix hj)
  stk := h.stk.sub_right (Region.sub_prefix hj)

/-! ## `vg_cmac_aes_update` -/

/-- The arguments of `vg_cmac_aes_update`: `K1`'s schedule, the state at
`W + y`, `n` blocks at `Q`, and the working space at `W + 256`. -/
theorem uargs {C W SP : BitVec 32} {s : State} (L : Lay C W SP) (E : Env C W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {y : Nat} (hy : StOk y) {Q : BitVec 32} {n : Nat}
    (hq : Src W SP s Q (16 * n)) (hqy : (⟨w64 Q, 16 * n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 y, 16⟩)
    (hn : 16 * n < 2 ^ 32) (eax : s.gpr .eax = C) (ecx : s.gpr .ecx = BitVec.ofNat 32 R)
    (edx : s.gpr .edx = W + BitVec.ofNat 32 y) (ebx : s.gpr .ebx = Q) (esi : s.gpr .esi = BitVec.ofNat 32 n)
    (edi : s.gpr .edi = W + BitVec.ofNat 32 256) :
    UArgs s C (W + BitVec.ofNat 32 y) Q (W + BitVec.ofNat 32 256) R n where
  eax := eax
  ecx := ecx
  edx := edx
  ebx := ebx
  esi := esi
  edi := edi
  rounds := hR
  esp := by rw [E.esp]; exact L.sp
  hn := hn
  wc := by
    rw [L.sW (o := y) (by omega)]
    simpa using L.c_w' (a := 0) (n := 240) (d := y) (k := 16) (by decide) (by omega)
  ws := by rw [L.sW (o := 256) (by omega)]; simpa using L.c_w' (a := 0) (n := 240) (d := 256) (k := 2176) (by decide) (by decide)
  dc := by rw [L.sW (o := y) (by omega)]; exact hqy
  ds := by rw [L.sW (o := 256) (by omega)]; exact hq.qs
  cs := by rw [L.sW (o := y) (by omega), L.sW (o := 256) (by omega)]; exact stOk_scr hy
  bW := by rw [E.esp]; simpa using L.stk_c' (a := 0) (n := 240) (by decide)
  bD := by rw [E.esp]; exact hq.stk
  bC := by rw [E.esp, L.sW (o := y) (by omega)]; exact L.stk_w' (by omega)
  bS := by rw [E.esp, L.sW (o := 256) (by omega)]; exact L.stk_w' (by decide)
  fW := by have := L.fc; omega
  fC := by rw [L.nW (o := y) (by omega)]; have := L.fw; omega
  fD := hq.wrap
  fS := by rw [L.nW (o := 256) (by omega)]; have := L.fw; omega
  reads := by
    refine covers_cons ?_ (covers_cons hq.rd covers_nil)
    simpa using E.perm.cC (d := 0) (n := 240) (by decide)
  writes := by
    rw [L.sW (o := y) (by omega), L.sW (o := 256) (by omega)]
    exact covers_cons (E.perm.wC (by omega)) (covers_cons (E.perm.wC (by decide)) covers_nil)

/-- A call of `vg_cmac_aes_update`, with its arguments (`uargs`). -/
theorem updCall_ok (v : Ctr32Impl) {C W SP : BitVec 32} {s : State} (L : Lay C W SP) (E : Env C W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {y : Nat} (hy : StOk y) {Q : BitVec 32} {n : Nat}
    (hq : Src W SP s Q (16 * n)) (hqy : (⟨w64 Q, 16 * n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 y, 16⟩)
    (hn : 16 * n < 2 ^ 32) (eax : s.gpr .eax = C) (ecx : s.gpr .ecx = BitVec.ofNat 32 R)
    (edx : s.gpr .edx = W + BitVec.ofNat 32 y) (ebx : s.gpr .ebx = Q) (esi : s.gpr .esi = BitVec.ofNat 32 n)
    (edi : s.gpr .edi = W + BitVec.ofNat 32 256) :
    WP isa (updCall v.callee v.suffix) s fun s' => Env C W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      Frame [⟨w64 W + BitVec.ofNat 64 y, 16⟩, ⟨w64 W + BitVec.ofNat 64 256, 2176⟩, below SP 56] s.mem s'.mem ∧
      bytesAt s'.mem (w64 W + BitVec.ofNat 64 y) 16 =
        Spec.Cmac.chain (Spec.Cmac.aesWith R (bytesAt s.mem (w64 C) (16 * (R + 1))))
          (bytesAt s.mem (w64 W + BitVec.ofNat 64 y) 16) (Spec.Cmac.blocksAt s.mem (w64 Q) 16 n) := by
  refine WP.mono (Proof.CmacAes.Stream.X86.upd_call v (uargs L E hR hy hq hqy hn eax ecx edx ebx esi edi))
    fun s' h => ⟨E.keep (h.saved _ (by decide)) (h.saved _ (by decide)) h.rd h.wr, h.rd, h.wr, h.saved, ?_, ?_⟩
  · have f := h.frame
    rw [L.sW (o := y) (by omega), L.sW (o := 256) (by omega), E.esp] at f
    exact f
  · have o := h.out
    rw [L.sW (o := y) (by omega)] at o
    exact o

/-- Calls of `vg_cmac_aes_update` with the same arguments are constant time. -/
theorem updCall_ct (v : Ctr32Impl) {C W SP : BitVec 32} (L : Lay C W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {y : Nat} (hy : StOk y) {Q : BitVec 32} {n : Nat} (hn : 16 * n < 2 ^ 32) {I : State → Prop}
    (hI : ∀ s, I s → Env C W SP s ∧ Src W SP s Q (16 * n) ∧
      (⟨w64 Q, 16 * n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 y, 16⟩ ∧ s.gpr .eax = C ∧
      s.gpr .ecx = BitVec.ofNat 32 R ∧ s.gpr .edx = W + BitVec.ofNat 32 y ∧ s.gpr .ebx = Q ∧
      s.gpr .esi = BitVec.ofNat 32 n ∧ s.gpr .edi = W + BitVec.ofNat 32 256) :
    CT I (updCall v.callee v.suffix) :=
  Proof.CmacAes.Stream.X86.upd_rel v (E := SP) fun s₁ s₂ ⟨h₁, h₂⟩ => by
    obtain ⟨E₁, q₁, y₁, a₁, c₁, d₁, b₁, i₁, j₁⟩ := hI s₁ h₁
    obtain ⟨E₂, q₂, y₂, a₂, c₂, d₂, b₂, i₂, j₂⟩ := hI s₂ h₂
    exact ⟨uargs L E₁ hR hy q₁ y₁ hn a₁ c₁ d₁ b₁ i₁ j₁, uargs L E₂ hR hy q₂ y₂ hn a₂ c₂ d₂ b₂ i₂ j₂, E₁.esp, E₂.esp⟩

/-! ## `vg_cmac_aes_finalize` -/

/-- The arguments of `vg_cmac_aes_finalize`: the key context (`K1`'s
schedule and its subkeys), the state at `W + y`, the last `l ≤ 16` bytes at
`P`, and the working space at `W + 256`. -/
theorem fargs {C W SP : BitVec 32} {s : State} (L : Lay C W SP) (E : Env C W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {y : Nat} (hy : StOk y) {P : BitVec 32} {l : Nat} (hl : l ≤ 16)
    (hp : Src W SP s P l) (hpy : (⟨w64 P, l⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 y, 16⟩)
    (eax : s.gpr .eax = C) (ecx : s.gpr .ecx = BitVec.ofNat 32 R)
    (edx : s.gpr .edx = W + BitVec.ofNat 32 y) (ebx : s.gpr .ebx = P) (esi : s.gpr .esi = BitVec.ofNat 32 l)
    (edi : s.gpr .edi = W + BitVec.ofNat 32 256) :
    FArgs s C (W + BitVec.ofNat 32 y) P (W + BitVec.ofNat 32 256) l R where
  eax := eax
  ecx := ecx
  edx := edx
  ebx := ebx
  esi := esi
  edi := edi
  rounds := hR
  len := hl
  esp := by rw [E.esp]; exact L.sp
  kst := by
    rw [L.sW (o := y) (by omega)]
    simpa using L.c_w' (a := 0) (n := 272) (d := y) (k := 16) (by decide) (by omega)
  ks := by rw [L.sW (o := 256) (by omega)]; simpa using L.c_w' (a := 0) (n := 272) (d := 256) (k := 2176) (by decide) (by decide)
  pst := by rw [L.sW (o := y) (by omega)]; exact hpy
  ps := by rw [L.sW (o := 256) (by omega)]; exact hp.qs
  sts := by rw [L.sW (o := y) (by omega), L.sW (o := 256) (by omega)]; exact stOk_scr hy
  bK := by rw [E.esp]; simpa using L.stk_c' (a := 0) (n := 272) (by decide)
  bP := by rw [E.esp]; exact hp.stk
  bSt := by rw [E.esp, L.sW (o := y) (by omega)]; exact L.stk_w' (by omega)
  bS := by rw [E.esp, L.sW (o := 256) (by omega)]; exact L.stk_w' (by decide)
  fK := by have := L.fc; omega
  fSt := by rw [L.nW (o := y) (by omega)]; have := L.fw; omega
  fP := hp.wrap
  fS := by rw [L.nW (o := 256) (by omega)]; have := L.fw; omega
  reads := by
    refine covers_cons ?_ (covers_cons hp.rd covers_nil)
    simpa using E.perm.cC (d := 0) (n := 272) (by decide)
  writes := by
    rw [L.sW (o := y) (by omega), L.sW (o := 256) (by omega)]
    exact covers_cons (E.perm.wC (by omega)) (covers_cons (E.perm.wC (by decide)) covers_nil)

/-- A call of `vg_cmac_aes_finalize`, with its arguments (`fargs`): the state
becomes `CIPH_K1(C ⊕ Mₙ)` for the last block `Mₙ` made with the context's
subkeys. -/
theorem finCall_ok (v : Ctr32Impl) {C W SP : BitVec 32} {s : State} (L : Lay C W SP) (E : Env C W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {y : Nat} (hy : StOk y) {P : BitVec 32} {l : Nat} (hl : l ≤ 16)
    (hp : Src W SP s P l) (hpy : (⟨w64 P, l⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 y, 16⟩)
    (eax : s.gpr .eax = C) (ecx : s.gpr .ecx = BitVec.ofNat 32 R)
    (edx : s.gpr .edx = W + BitVec.ofNat 32 y) (ebx : s.gpr .ebx = P) (esi : s.gpr .esi = BitVec.ofNat 32 l)
    (edi : s.gpr .edi = W + BitVec.ofNat 32 256) :
    WP isa (finCall v.callee v.suffix) s fun s' => Env C W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      Frame [⟨w64 W + BitVec.ofNat 64 y, 16⟩, ⟨w64 W + BitVec.ofNat 64 256, 2176⟩, below SP 56] s.mem s'.mem ∧
      bytesAt s'.mem (w64 W + BitVec.ofNat 64 y) 16 =
        Spec.Cmac.aesWith R (bytesAt s.mem (w64 C) (16 * (R + 1)))
          (Spec.Cmac.xor (Spec.Cmac.lastBlock 16 (bytesAt s.mem (w64 C + BitVec.ofNat 64 240) 16)
              (bytesAt s.mem (w64 C + BitVec.ofNat 64 256) 16) (bytesAt s.mem (w64 P) l))
            (bytesAt s.mem (w64 W + BitVec.ofNat 64 y) 16)) := by
  refine WP.mono (finr_call v (fargs L E hR hy hl hp hpy eax ecx edx ebx esi edi))
    fun s' h => ⟨E.keep (h.saved _ (by decide)) (h.saved _ (by decide)) h.rd h.wr, h.rd, h.wr, h.saved, ?_, ?_⟩
  · have f := h.frame
    rw [L.sW (o := y) (by omega), L.sW (o := 256) (by omega), E.esp] at f
    exact f
  · have o := h.out
    rw [L.sW (o := y) (by omega)] at o
    exact o

/-- Calls of `vg_cmac_aes_finalize` with the same arguments are constant time. -/
theorem finCall_ct (v : Ctr32Impl) {C W SP : BitVec 32} (L : Lay C W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {y : Nat} (hy : StOk y) {P : BitVec 32} {l : Nat} (hl : l ≤ 16) {I : State → Prop}
    (hI : ∀ s, I s → Env C W SP s ∧ Src W SP s P l ∧
      (⟨w64 P, l⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 y, 16⟩ ∧ s.gpr .eax = C ∧
      s.gpr .ecx = BitVec.ofNat 32 R ∧ s.gpr .edx = W + BitVec.ofNat 32 y ∧ s.gpr .ebx = P ∧
      s.gpr .esi = BitVec.ofNat 32 l ∧ s.gpr .edi = W + BitVec.ofNat 32 256) :
    CT I (finCall v.callee v.suffix) :=
  Proof.CmacAes.Stream.X86.fin_rel v (E := SP) fun s₁ s₂ ⟨h₁, h₂⟩ => by
    obtain ⟨E₁, q₁, y₁, a₁, c₁, d₁, b₁, i₁, j₁⟩ := hI s₁ h₁
    obtain ⟨E₂, q₂, y₂, a₂, c₂, d₂, b₂, i₂, j₂⟩ := hI s₂ h₂
    exact ⟨fargs L E₁ hR hy hl q₁ y₁ a₁ c₁ d₁ b₁ i₁ j₁, fargs L E₂ hR hy hl q₂ y₂ a₂ c₂ d₂ b₂ i₂ j₂, E₁.esp, E₂.esp⟩

/-! ## `vg_aes_ctr32` -/

/-- The frame and call of `vg_aes_ctr32`: AES-GCM's, with any implementation
of `vg_aes_ghash` beside it. -/
theorem ctrFrame_ok (v : Ctr32Impl) {s : State} {K C D S : BitVec 32} {R n : Nat} (h : CtrCall s K C D S R n) :
    WP isa (.frame (.push [.ebp, .edi, .ebx, .edx, .ecx, .eax]) (.call v.callee.name v.callee.code) (.pop .eax 6)) s
      (CtrPost s K C D S R n) :=
  Proof.AesGcm.X86.ctr_call ⟨v, .scalar⟩ h

/-- The arguments of `vg_aes_ctr32`: `K2`'s schedule at `C + 272`, the
counter block at `W + c`, one block at `W + q`, and the working space at
`W + 256` (where `ebp` is moved). -/
theorem cargs {C W SP : BitVec 32} {s : State} (L : Lay C W SP) (P : Perm C W s) (esp : s.gpr .esp = SP) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {c q : Nat} (hc : c + 16 ≤ 256) (hq : q + 16 ≤ 256)
    (hqc : q + 16 ≤ c ∨ c + 16 ≤ q) (eax : s.gpr .eax = C + BitVec.ofNat 32 272)
    (ecx : s.gpr .ecx = BitVec.ofNat 32 R) (edx : s.gpr .edx = W + BitVec.ofNat 32 c)
    (ebx : s.gpr .ebx = W + BitVec.ofNat 32 q) (edi : s.gpr .edi = BitVec.ofNat 32 1)
    (ebp : s.gpr .ebp = W + BitVec.ofNat 32 256) :
    CtrCall s (C + BitVec.ofNat 32 272) (W + BitVec.ofNat 32 c) (W + BitVec.ofNat 32 q) (W + BitVec.ofNat 32 256)
      R 1 := by
  have hsp := L.sp
  have b28 : Region.Sub (below SP 28) (below SP 56) := below_sub56 (by decide) hsp
  refine ⟨eax, ecx, edx, ebx, edi, ebp, hR, by rw [esp]; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · rw [L.aC (o := 272) (by omega), L.aW (o := c) (by omega)]; exact L.c_w' (by decide) (by omega)
  · rw [L.aC (o := 272) (by omega), L.aW (o := q) (by omega)]; exact L.c_w' (by decide) (by omega)
  · rw [L.aC (o := 272) (by omega), L.aW (o := 256) (by omega)]; exact L.c_w' (by decide) (by decide)
  · rw [L.aW (o := c) (by omega), L.aW (o := q) (by omega)]; exact Lay.w_w (by omega) (by omega) (by omega)
  · rw [L.aW (o := c) (by omega), L.aW (o := 256) (by omega)]
    exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  · rw [L.aW (o := q) (by omega), L.aW (o := 256) (by omega)]
    exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  · rw [esp, L.aC (o := 272) (by omega)]; exact (L.stk_c' (by decide)).sub_left b28
  · rw [esp, L.aW (o := c) (by omega)]; exact (L.stk_w' (by omega)).sub_left b28
  · rw [esp, L.aW (o := q) (by omega)]; exact (L.stk_w' (by omega)).sub_left b28
  · rw [esp, L.aW (o := 256) (by omega)]; exact (L.stk_w' (by decide)).sub_left b28
  · rw [L.nC (o := 272) (by omega)]; have := L.fc; omega
  · rw [L.nW (o := c) (by omega)]; have := L.fw; omega
  · rw [L.nW (o := q) (by omega)]; have := L.fw; omega
  · rw [L.nW (o := 256) (by omega)]; have := L.fw; omega
  · rw [L.aC (o := 272) (by omega)]; exact P.cC (by decide)
  · rw [L.aW (o := c) (by omega), L.aW (o := q) (by omega), L.aW (o := 256) (by omega)]
    exact covers_cons (P.wC (by omega)) (covers_cons (P.wC (by omega)) (covers_cons (P.wC (by decide)) covers_nil))

/-- A call of `vg_aes_ctr32` on the block at `W + q`, from the counter block
at `W + c`, under `K2`. -/
theorem ctrCall_ok (v : Ctr32Impl) {C W SP : BitVec 32} {s : State} (L : Lay C W SP) (E : Env C W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {c q : Nat} (hc : c + 16 ≤ 256) (hq : q + 16 ≤ 256)
    (hqc : q + 16 ≤ c ∨ c + 16 ≤ q) (eax : s.gpr .eax = C + BitVec.ofNat 32 272)
    (ecx : s.gpr .ecx = BitVec.ofNat 32 R) (edx : s.gpr .edx = W + BitVec.ofNat 32 c)
    (ebx : s.gpr .ebx = W + BitVec.ofNat 32 q) (edi : s.gpr .edi = BitVec.ofNat 32 1) :
    WP isa (ctrCall v.callee) s fun s' => Env C W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ [Reg.ebx, .esi, .edi], s'.gpr r = s.gpr r) ∧
      Frame [⟨w64 W + BitVec.ofNat 64 c, 16⟩, ⟨w64 W + BitVec.ofNat 64 q, 16⟩,
        ⟨w64 W + BitVec.ofNat 64 256, 2048⟩, below SP 56] s.mem s'.mem ∧
      blocksAt s'.mem (w64 W + BitVec.ofNat 64 q) 1 =
        ctr32 (aesWith R (bytesAt s.mem (w64 C + BitVec.ofNat 64 272) (16 * (R + 1))))
          (blockAt s.mem (w64 W + BitVec.ofNat 64 c)) (blocksAt s.mem (w64 W + BitVec.ofNat 64 q) 1) := by
  have hsp := L.sp
  have b28 : Region.Sub (below SP 28) (below SP 56) := below_sub56 (by decide) hsp
  -- `ebp := W + 256`.
  refine WP.seq (WP.of_runBlock ⟨_, by crun [], ?_⟩)
  -- The call.
  have e256 : s.gpr .ebp + BitVec.ofNat 32 256 = W + BitVec.ofNat 32 256 := by rw [E.ebp]
  refine WP.seq (WP.mono (ctrFrame_ok v (cargs L (E.perm.of_eq (by cmems []) (by cmems [])) (by cregs [E.esp]) hR hc
    hq hqc (by cregs [eax]) (by cregs [ecx]) (by cregs [edx]) (by cregs [ebx]) (by cregs [edi]) (by cregs [e256])))
    fun s₂ P => ?_)
  -- `ebp := W`.
  have hbp₂ : s₂.gpr .ebp = W + BitVec.ofNat 32 256 := by
    rw [P.saved _ (by decide)]; cregs [E.ebp]
  have hsp₂ : s₂.gpr .esp = SP := by rw [P.saved _ (by decide)]; cregs [E.esp]
  refine WP.of_runBlock ⟨_, by crun [hbp₂], ?_⟩
  refine ⟨⟨by cregs [hbp₂]; exact BitVec.add_sub_cancel _ _, by cregs [hsp₂],
    E.perm.of_eq (by cmems [P.rd]) (by cmems [P.wr])⟩, by cmems [P.rd], by cmems [P.wr], ?_, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> (cregs []; rw [P.saved _ (by decide)]; cregs [])
  · have f := P.frame
    rw [L.aW (o := c) (by omega), L.aW (o := q) (by omega), L.aW (o := 256) (by omega)] at f
    cmems []
    refine f.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · refine ⟨below SP 56, by simp, ?_⟩
      simpa [gpr_setReg_of_ne, E.esp] using b28
  · have o := P.out
    rw [L.aW (o := c) (by omega), L.aW (o := q) (by omega), L.aC (o := 272) (by omega)] at o
    cmems []
    exact o

/-- Calls of `vg_aes_ctr32` with the same arguments are constant time. -/
theorem ctrCall_ct (v : Ctr32Impl) {C W SP : BitVec 32} (L : Lay C W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {c q : Nat} (hc : c + 16 ≤ 256) (hq : q + 16 ≤ 256) (hqc : q + 16 ≤ c ∨ c + 16 ≤ q) {I : State → Prop}
    (hI : ∀ s, I s → Env C W SP s ∧ s.gpr .eax = C + BitVec.ofNat 32 272 ∧
      s.gpr .ecx = BitVec.ofNat 32 R ∧ s.gpr .edx = W + BitVec.ofNat 32 c ∧ s.gpr .ebx = W + BitVec.ofNat 32 q ∧
      s.gpr .edi = BitVec.ofNat 32 1) :
    CT I (ctrCall v.callee) := by
  -- The state after `ebp := W + 256`, as `CtrCall` needs it.
  have call : ∀ s, I s → ∀ s', runBlock isa [.alu .add .ebp (imm csOff)] s = some s' →
      CtrCall s' (C + BitVec.ofNat 32 272) (W + BitVec.ofNat 32 c) (W + BitVec.ofNat 32 q) (W + BitVec.ofNat 32 256)
        R 1 ∧ s'.gpr .esp = SP := by
    intro s hs s' run
    obtain ⟨E, eax, ecx, edx, ebx, edi⟩ := hI s hs
    have e := run
    simp (disch := first | decide | omega) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
      imm, csOff, Option.bind_some, Option.some.injEq] at e
    subst e
    have e256 : s.gpr .ebp + BitVec.ofNat 32 256 = W + BitVec.ofNat 32 256 := by rw [E.ebp]
    exact ⟨cargs L (E.perm.of_eq (by cmems []) (by cmems [])) (by cregs [E.esp]) hR hc hq hqc (by cregs [eax])
      (by cregs [ecx]) (by cregs [edx]) (by cregs [ebx]) (by cregs [edi]) (by cregs [e256]), by cregs [E.esp]⟩
  refine CT.seq (J := fun s' => ∃ s, I s ∧ runBlock isa [.alu .add .ebp (imm csOff)] s = some s')
    (CT.taint [.ebp] (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [(hI _ h₁).1.ebp, (hI _ h₂).1.ebp]) (by taint_decide))
    (fun s hs => WP.of_runBlock ⟨_, by crun [], s, hs, by crun []⟩) ?_
  refine CT.seq (J := fun s => s.gpr .ebp = W + BitVec.ofNat 32 256)
    ((Proof.AesGcm.X86.ctr_ct ⟨v, .scalar⟩ (E := SP) fun s ⟨s₀, h₀, run⟩ => call s₀ h₀ s run :
      CT _ (.frame (.push [.ebp, .edi, .ebx, .edx, .ecx, .eax]) (.call v.callee.name v.callee.code) (.pop .eax 6))))
    (fun s ⟨s₀, h₀, run⟩ => WP.mono (ctrFrame_ok v (call s₀ h₀ s run).1) fun s₁ g => by
      rw [g.saved .ebp (by decide), (call s₀ h₀ s run).1.ebp]) ?_
  exact CT.taint [.ebp] (fun s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁, h₂]) (by taint_decide)

end VG.Proof.AesSiv.X86
