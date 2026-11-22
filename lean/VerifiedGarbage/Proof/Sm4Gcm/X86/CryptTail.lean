module

public import VerifiedGarbage.Proof.AesGcm.X86.Loops
public import VerifiedGarbage.Proof.Cmac.Block32
import VerifiedGarbage.Proof.AesGcm.X86.Flush
meta import VerifiedGarbage.Proof.AesGcm.X86.Loops
meta import VerifiedGarbage.Proof.Cmac.Block32
meta import VerifiedGarbage.Proof.AesGcm.X86.Flush
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Impl.Sm4Gcm.X86
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.X86.Call
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.TCB.X86.Isa
meta import VerifiedGarbage.TCB.X86.State
import VerifiedGarbage.Proof.AesGcm.X86.Absorb
meta import VerifiedGarbage.Proof.AesGcm.X86.Absorb
public import VerifiedGarbage.Proof.Sm4Gcm.X86.CtrCall
public import VerifiedGarbage.Proof.Gcm.Ctr
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sm4Gcm.X86.CtrCall
meta import VerifiedGarbage.Proof.Gcm.Ctr
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `Sm4Gcm.X86.Crypt`, which this module and modules that import it used -/

section

/-!
# SM4-GCM on x86: counter mode over a piece (`crypt`), the definitions

Untrusted: everything here is checked by Lean. `crypt` XORs the keystream,
from byte `P` of the text on, into the `nO` bytes at `dO`, where `bO` is
`P mod 16` and the state holds the counter block (`St + 48`) and the
keystream block (`St + 64`) for `P` bytes (`Proof.Gcm.Ctr`). What holds
before (`CrIn`), part of the way (`CrMid`, `CrAt`) and after (`CrOut`), and
the regions it writes (`crFrame`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.Sm4Gcm.X86 VG.WriteBytes VG.Proof.AesGcm.X86
open VG.Impl.AesGcm.X86 hiding ctrCall keyCall ctrArgs cryptWhole cryptTail crypt tag init cryptEntry
  streamEncrypt streamDecrypt finEntry finTag streamFinish streamVerify oneEntry oneTag oneCrypt «seal» «open»
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt)
open VG.Proof.Gcm (Ctr xorKs)

/-- The counter and keystream blocks of the state at `St`, for `P` bytes. -/
abbrev CtrS (m : Mem) (St : BitVec 32) (ciph : Block → Block) (icb : Block) (P : Nat) : Prop :=
  Ctr m (w64 St + BitVec.ofNat 64 48) (w64 St + BitVec.ofNat 64 64) ciph icb P

/-- A buffer of `n` bytes at `D` that the code may read and write, apart from
the context, the state, `W` and the stack below `SP`. -/
structure DataW (Ctx St W SP : BitVec 32) (K : Nat) (s : State) (D : BitVec 32) (n : Nat) : Prop where
  ok : DataOk St W SP K s D n
  wr : Covers [⟨w64 D, n⟩] s.wr
  ctx : (⟨w64 Ctx, 256⟩ : Region).Disjoint ⟨w64 D, n⟩

theorem DataW.of_eq {Ctx St W SP : BitVec 32} {K : Nat} {s s' : State} {D : BitVec 32} {n : Nat}
    (h : DataW Ctx St W SP K s D n) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : DataW Ctx St W SP K s' D n :=
  ⟨h.ok.of_eq hrd hwr, by rw [hwr]; exact h.wr, h.ctx⟩

theorem DataW.take {Ctx St W SP : BitVec 32} {K : Nat} {s : State} {D : BitVec 32} {n : Nat}
    (h : DataW Ctx St W SP K s D n) {k : Nat} (hk : k ≤ n) : DataW Ctx St W SP K s D k :=
  ⟨h.ok.take hk, fun a m ⟨r, hr, hc⟩ => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.wr a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega_using [hk, hc]⟩,
   h.ctx.sub_right (Region.sub_prefix hk)⟩

/-- The bytes `[j, j + k)`, writable and apart from the context. -/
theorem DataW.part {Ctx St W SP : BitVec 32} {K : Nat} {s : State} {D : BitVec 32} {n : Nat}
    (h : DataW Ctx St W SP K s D n) {j k : Nat} (hk : j + k ≤ n) :
    Covers [⟨w64 D + BitVec.ofNat 64 j, k⟩] s.wr ∧
      (⟨w64 Ctx, 256⟩ : Region).Disjoint ⟨w64 D + BitVec.ofNat 64 j, k⟩ :=
  ⟨covers_off h.wr hk h.ok.n_lt, h.ctx.sub_right (Offset.sub_base _ hk)⟩

/-- `[D, D + j)` and `[D + j, D + j + l)` are apart. -/
theorem split_disj {D : Addr} {j l : Nat} (hn : j + l < 2 ^ 64) :
    (⟨D, j⟩ : Region).Disjoint ⟨D + BitVec.ofNat 64 j, l⟩ := by
  have := Offset.disjoint D (d := 0) (n := j) (e := j) (k := l) (.inl (by omega_using [])) (by omega_using [hn]) (by omega_using [hn])
  simpa using this

/-- The bytes done so far and the next ones. -/
theorem done_append {m m₀ : Mem} {ciph : Block → Block} {icb : Block} {P : Nat} {D : Addr} {j l : Nat}
    (h₁ : bytesAt m D j = xorKs ciph icb P (bytesAt m₀ D j))
    (h₂ : bytesAt m (D + BitVec.ofNat 64 j) l = xorKs ciph icb (P + j) (bytesAt m₀ (D + BitVec.ofNat 64 j) l)) :
    bytesAt m D (j + l) = xorKs ciph icb P (bytesAt m₀ D (j + l)) := by
  rw [bytesAt_add, bytesAt_add, Proof.Gcm.xorKs_append, h₁, h₂, length_bytesAt]

theorem ofBytes_zeros : Spec.Gcm.ofBytes (Spec.Gcm.zeros 16) = 0 := by decide

/-- The regions `crypt` writes. -/
abbrev crFrame (St W SP : BitVec 32) (K : Nat) (D : BitVec 32) (n : Nat) : List Region :=
  [⟨w64 D, n⟩, ⟨w64 St + BitVec.ofNat 64 48, 32⟩, wsR W, below SP K]

/-- Before `crypt`: `P` bytes of text so far, `n` bytes at `D` to go. -/
structure CrIn (Ctx St W SP : BitVec 32) (K : Nat) (D : BitVec 32) (n P : Nat) (s : State) : Prop where
  env : Env Ctx St W SP s
  dO : slotv s.mem W dO = D
  nO : slotv s.mem W nO = BitVec.ofNat 32 n
  bO : slotv s.mem W bO = BitVec.ofNat 32 (P % 16)
  nlt : n < 2 ^ 32
  data : DataW Ctx St W SP K s D n

/-- What holds part of the way, `j` bytes done, from `m₀`, but the slots. -/
structure CrAt (Ctx St W SP : BitVec 32) (K : Nat) (icb : Block) (D : BitVec 32) (n P : Nat) (m₀ : Mem)
    (j : Nat) (s : State) : Prop where
  env : Env Ctx St W SP s
  le : j ≤ n
  nlt : n < 2 ^ 32
  data : DataW Ctx St W SP K s D n
  ctr : CtrS m₀ St (ciphOf m₀ Ctx) icb P → CtrS s.mem St (ciphOf m₀ Ctx) icb (P + j)
  done : CtrS m₀ St (ciphOf m₀ Ctx) icb P →
    bytesAt s.mem (w64 D) j = xorKs (ciphOf m₀ Ctx) icb P (bytesAt m₀ (w64 D) j)
  rest : bytesAt s.mem (w64 D + BitVec.ofNat 64 j) (n - j) = bytesAt m₀ (w64 D + BitVec.ofNat 64 j) (n - j)
  whole : n - j = 0 ∨ (P + j) % 16 = 0
  frame : Frame (crFrame St W SP K D n) m₀ s.mem

/-- Part of the way: `j` bytes done, from `m₀`. -/
structure CrMid (Ctx St W SP : BitVec 32) (K : Nat) (icb : Block) (D : BitVec 32) (n P : Nat) (m₀ : Mem)
    (j : Nat) (s : State) : Prop where
  at_ : CrAt Ctx St W SP K icb D n P m₀ j s
  dO : slotv s.mem W dO = D + BitVec.ofNat 32 j
  nO : slotv s.mem W nO = BitVec.ofNat 32 (n - j)

/-- After `crypt`. -/
structure CrOut (Ctx St W SP : BitVec 32) (K : Nat) (icb : Block) (D : BitVec 32) (n P : Nat) (m₀ : Mem)
    (s : State) : Prop where
  env : Env Ctx St W SP s
  ctr : CtrS m₀ St (ciphOf m₀ Ctx) icb P → CtrS s.mem St (ciphOf m₀ Ctx) icb (P + n)
  out : CtrS m₀ St (ciphOf m₀ Ctx) icb P →
    bytesAt s.mem (w64 D) n = xorKs (ciphOf m₀ Ctx) icb P (bytesAt m₀ (w64 D) n)
  frame : Frame (crFrame St W SP K D n) m₀ s.mem

section
variable {Ctx St W SP : BitVec 32} {K : Nat} (L : Lay4 Ctx St W SP K)
include L

theorem ctx_crFrame {s : State} {D : BitVec 32} {n : Nat} (hd : DataW Ctx St W SP K s D n) :
    ∀ r ∈ crFrame St W SP K D n, (⟨w64 Ctx, 256⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hd.ctx
  · exact L.cs.sub_right (Lay.stSub (by decide))
  · exact L.cw.sub_right (Lay.wSub (by decide))
  · exact L.kc.symm

theorem kept_crFrame {s : State} {D : BitVec 32} {n : Nat} (hd : DataW Ctx St W SP K s D n) :
    ∀ r ∈ crFrame St W SP K D n, (keptR W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (hd.ok.w.sub_right (Lay.wSub (by decide))).symm
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

/-- The context's slot is apart from `crFrame`. -/
theorem ctxSlot_crFrame {s : State} {D : BitVec 32} {n : Nat} (hd : DataW Ctx St W SP K s D n) :
    ∀ r ∈ crFrame St W SP K D n, (⟨w64 W + BitVec.ofNat 64 ctxO, 4⟩ : Region).Disjoint r :=
  fun r hr => (kept_crFrame L hd r hr).sub_left (Offset.sub _ (by decide) (by decide))

theorem env_crFrame {s s' : State} {D : BitVec 32} {n : Nat} (hd : DataW Ctx St W SP K s D n)
    (he : Env Ctx St W SP s) (hf : Frame (crFrame St W SP K D n) s.mem s'.mem)
    (hbp : s'.gpr .ebp = s.gpr .ebp) (hsi : s'.gpr .esi = s.gpr .esi) (hsp : s'.gpr .esp = s.gpr .esp)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Env Ctx St W SP s' :=
  he.keep hbp hsi hsp hrd hwr (slot_frame hf (ctxSlot_crFrame L hd))

theorem ciph_crFrame {s : State} {D : BitVec 32} {n : Nat} (hd : DataW Ctx St W SP K s D n) {m m' : Mem}
    (hf : Frame (crFrame St W SP K D n) m m') :
    ciphOf m' Ctx = ciphOf m Ctx :=
  ciph_frame hf (ctx_crFrame L hd)

omit L in
/-- The pieces' slots are within `crFrame`. -/
theorem pslot_crFrame {D : BitVec 32} {n : Nat} {m m' : Mem} (h : Frame [pslotR W] m m') :
    Frame (crFrame St W SP K D n) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, by simp, pslot_ws W⟩

omit L in
/-- `[D + j, D + j + k)` is within `crFrame`. -/
theorem part_crFrame {D : BitVec 32} {n j k : Nat} (hk : j + k ≤ n) {m m' : Mem}
    (h : Frame [⟨w64 D + BitVec.ofNat 64 j, k⟩] m m') : Frame (crFrame St W SP K D n) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_self .., Offset.sub_base _ hk⟩

/-- `CrAt` after code that writes only the slots. -/
theorem CrAt.pslot {icb : Block} {D : BitVec 32} {n P : Nat} {m₀ : Mem} {j : Nat} {s s' : State}
    (h : CrAt Ctx St W SP K icb D n P m₀ j s) (hf : Frame [pslotR W] s.mem s'.mem)
    (hbp : s'.gpr .ebp = s.gpr .ebp) (hsi : s'.gpr .esi = s.gpr .esi) (hsp : s'.gpr .esp = s.gpr .esp)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : CrAt Ctx St W SP K icb D n P m₀ j s' := by
  have pS : ∀ {a k : Nat}, a + k ≤ 80 → ∀ r ∈ [pslotR W], (⟨w64 St + BitVec.ofNat 64 a, k⟩ : Region).Disjoint r :=
    fun hak r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.st_w hak (.inr ⟨by decide, by decide⟩)
  have pD : ∀ {a k : Nat}, a + k ≤ n → ∀ r ∈ [pslotR W], (⟨w64 D + BitVec.ofNat 64 a, k⟩ : Region).Disjoint r :=
    fun hak r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.data.ok.w.sub_left (Offset.sub_base _ hak)).sub_right (Lay.wSub (by decide))
  refine ⟨env_crFrame L h.data h.env (pslot_crFrame hf) hbp hsi hsp hrd hwr, h.le, h.nlt, h.data.of_eq hrd hwr,
    fun hc => (h.ctr hc).congr (blockAt_frame hf (pS (by decide))) (blockAt_frame hf (pS (by decide))),
    fun hc => ?_, ?_, h.whole, h.frame.trans (pslot_crFrame hf)⟩
  · have := pD (a := 0) (k := j) (by have := h.le; omega_using [this])
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at this
    rw [bytesAt_frame hf this (by have := h.le; have := h.nlt; omega_arith)]; exact h.done hc
  · rw [bytesAt_frame hf (pD (by have := h.le; omega_using [this])) (by have := h.nlt; omega_using [this])]; exact h.rest

end

end VG.Proof.Sm4Gcm.X86

end

end

/-! ### `Sm4Gcm.X86.CryptWhole`, which only this module used -/

section

/-!
# SM4-GCM on x86: whole blocks of the text (`cryptWhole`)

Untrusted: everything here is checked by Lean. From a block boundary,
`cryptWhole` encrypts the whole blocks left at `dO` with `vg_aes_ctr32`
(`cryptWhole_pc`), by `Proof.Gcm.ctr_whole`. `ctrArgs_ok` sets up the
arguments of the call, here and in `cryptTail`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.Sm4Gcm.X86 VG.WriteBytes VG.Proof.AesGcm.X86
open VG.Impl.AesGcm.X86 hiding ctrCall keyCall ctrArgs cryptWhole cryptTail crypt tag init cryptEntry
  streamEncrypt streamDecrypt finEntry finTag streamFinish streamVerify oneEntry oneTag oneCrypt «seal» «open»
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt)
open VG.Proof.Gcm (Ctr xorKs)

section
variable {Ctx St W SP : BitVec 32} {K : Nat} (L : Lay4 Ctx St W SP K) {ci : CtrImpl}
include L

/-- `ctrArgs`: the context and the counter block. -/
theorem ctrArgs_ok {s : State} (he : Env Ctx St W SP s) :
    ∃ s', runBlock isa ctrArgs s = some s' ∧ s'.gpr .eax = Ctx ∧ s'.gpr .edx = St + BitVec.ofNat 32 48 ∧
      (∀ r, r ≠ .eax → r ≠ .edx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  refine ⟨_, by xrun [ctrArgs, he.ebp, he.esi, L.aW, he.wIn'], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · regs [he.ctx]
  · regs [he.esi]
  · intro r h₁ h₂
    simp only [gpr_setMem, gpr_arithFlags, gpr_setReg_of_ne _ _ h₁, gpr_setReg_of_ne _ _ h₂]
  all_goals rfl

variable {icb : Block} {D : BitVec 32} {n P : Nat}

/-- After `splitWhole`, `nb` whole blocks from byte `j`. -/
structure CWhole1 (j nb : Nat) (m₀ : Mem) (s : State) : Prop where
  at_ : CrAt Ctx St W SP K icb D n P m₀ j s
  ebx : s.gpr .ebx = D + BitVec.ofNat 32 j
  edi : s.gpr .edi = BitVec.ofNat 32 nb
  zf : s.zf = some (decide (nb = 0))
  dO : slotv s.mem W dO = D + BitVec.ofNat 32 (j + 16 * nb)
  nO : slotv s.mem W nO = BitVec.ofNat 32 ((n - j) % 16)

theorem cWhole1_ok {j : Nat} {m₀ : Mem} {s : State} (h : CrMid Ctx St W SP K icb D n P m₀ j s) :
    WP isa (.block splitWhole) s (CWhole1 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K)
      (icb := icb) (D := D) (n := n) (P := P) j ((n - j) / 16) m₀) := by
  have he := h.at_.env
  obtain ⟨s₁, run, bx, di, zf, g, m, rd, wr⟩ := splitWhole_ok L.lay he h.dO h.nO (r := n - j)
    (by have := h.at_.nlt; omega_using [this])
  refine WP.of_runBlock ⟨s₁, run, ?_⟩
  have fr : Frame [pslotR W] s.mem s₁.mem := by
    rw [m]; exact pslot_write (pslot_write (Frame.refl _ _) (by decide) (by decide) _) (by decide) (by decide) _
  refine ⟨h.at_.pslot L fr (g _ (by decide) (by decide) (by decide) (by decide))
      (g _ (by decide) (by decide) (by decide) (by decide)) (g _ (by decide) (by decide) (by decide) (by decide)) rd wr,
    bx, di, zf, ?_, ?_⟩
  · rw [slotv_eq, m]; mems [add_ofNat_assoc32]
  · rw [slotv_eq, m]; mems []

theorem cArgs_ok (hK : K = 1536) {j nb : Nat} (hnb : nb ≠ 0) (hj : j + 16 * nb ≤ n) {m₀ : Mem} {s : State}
    (h : CWhole1 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (icb := icb) (D := D) (n := n)
      (P := P) j nb m₀ s) :
    WP isa (.block ctrArgs) s fun s' => CtrReady Ctx St W SP (St + BitVec.ofNat 32 48) (D + BitVec.ofNat 32 j) nb s' ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  subst hK
  have he := h.at_.env
  have hd := h.at_.data
  obtain ⟨s', run, ax, dx, g, m, rd, wr⟩ := ctrArgs_ok L he
  refine WP.of_runBlock ⟨s', run, ?_, m, rd, wr⟩
  have hjn : j < n := by omega_using [hnb, hj]
  have eP := hd.ok.ptr hjn
  have eC := L.aS (o := 48) (by decide)
  obtain ⟨dr, dst, dw, dk⟩ := hd.ok.part (j := j) (k := 16 * nb) hj
  obtain ⟨dwr, dctx⟩ := hd.part (j := j) (k := 16 * nb) hj
  refine ⟨ax, dx, by rw [g _ (by decide) (by decide), h.ebx],
    by rw [g _ (by decide) (by decide), h.edi], by rw [g _ (by decide) (by decide), he.ebp],
    by rw [g _ (by decide) (by decide), he.esi],
    by rw [g _ (by decide) (by decide), he.esp], by rw [rd, wr]; exact he.ctxR,
    by rw [wr]; exact he.stW, by rw [wr]; exact he.wW, by rw [m]; exact he.ctx,
    by rw [L.nS (by decide)]; have := L.fs; omega_using [this], by rw [hd.ok.ptrN hjn]; have := hd.ok.fit; omega_using [hj, this],
    by rw [wr, eC]; exact he.stC (by decide), by rw [wr, eP]; exact dwr,
    by rw [eC, eP]; exact (dst.sub_right (Lay.stSub (by decide))).symm,
    by rw [eC]; exact L.cs.sub_right (Lay.stSub (by decide)), by rw [eP]; exact dctx,
    by rw [eC]; exact L.stk_st (by decide), by rw [eP]; exact dk,
    by rw [eC]; exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm,
    by rw [eP]; exact (dw.sub_right (Lay.wSub (by decide))).symm⟩

theorem cArgs_pc (hK : K = 1536) {j nb : Nat} (hnb : nb ≠ 0) (hj : j + 16 * nb ≤ n) :
    Pc (CWhole1 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (icb := icb) (D := D) (n := n)
        (P := P) j nb) (.block ctrArgs)
      (fun m₀ s => ∃ s₁, CWhole1 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (icb := icb)
        (D := D) (n := n) (P := P) j nb m₀ s₁ ∧
        CtrReady Ctx St W SP (St + BitVec.ofNat 32 48) (D + BitVec.ofNat 32 j) nb s ∧
        s.mem = s₁.mem ∧ s.rd = s₁.rd ∧ s.wr = s₁.wr) :=
  Pc.taint [.ebp, .esi] (fun m₀ s h => WP.mono (cArgs_ok L hK hnb hj h) fun s' ⟨g, m, rd, wr⟩ => ⟨s, h, g, m, rd, wr⟩)
    (fun _ _ s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.at_.env.ebp, h₂.at_.env.ebp]
      · rw [h₁.at_.env.esi, h₂.at_.env.esi]) (by taint_decide)

/-- What `vg_sm4_ctr32` writes on the data from `D + j` is apart from the
rest of the data. -/
theorem ctrFr_disj (hK : K = 1536) {s : State} (hd : DataW Ctx St W SP K s D n) {j nb a l : Nat}
    (hal : a + l ≤ n) (hsep : a + l ≤ j ∨ j + 16 * nb ≤ a) (hj : j + 16 * nb ≤ n) :
    ∀ r ∈ [(⟨w64 St + BitVec.ofNat 64 48, 16⟩ : Region), ⟨w64 D + BitVec.ofNat 64 j, 16 * nb⟩,
      below SP 1536], (⟨w64 D + BitVec.ofNat 64 a, l⟩ : Region).Disjoint r := by
  subst hK
  have hs : Region.Sub ⟨w64 D + BitVec.ofNat 64 a, l⟩ ⟨w64 D, n⟩ := Offset.sub_base _ hal
  have hn := hd.ok.n_lt
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hd.ok.st.sub_left hs).sub_right (Lay.stSub (by decide))
  · exact Offset.disjoint _ (by omega_using [hsep]) (by omega_using [hal, hn]) (by omega_using [hj, hn])
  · exact (hd.ok.stk.sub_right hs).symm

/-- The slots are apart from what `vg_sm4_ctr32` writes. -/
theorem ctrFr_slot (hK : K = 1536) {s : State} (hd : DataW Ctx St W SP K s D n) {j nb o : Nat}
    (h₁ : 240 ≤ o) (h₂ : o + 4 ≤ 512) (hj : j + 16 * nb ≤ n) :
    ∀ r ∈ [(⟨w64 St + BitVec.ofNat 64 48, 16⟩ : Region), ⟨w64 D + BitVec.ofNat 64 j, 16 * nb⟩,
      below SP 1536], (⟨w64 W + BitVec.ofNat 64 o, 4⟩ : Region).Disjoint r := by
  subst hK
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (L.st_w (by decide) (.inr ⟨by omega_using [h₁], by omega_using [h₂]⟩)).symm
  · exact ((hd.ok.w.sub_left (Offset.sub_base _ hj)).sub_right (Lay.wSub (by omega_using [h₂]))).symm
  · exact (L.stk_w (by omega_using [h₂])).symm

theorem ctrFr_crFrame (hK : K = 1536) {j nb : Nat} (hj : j + 16 * nb ≤ n) {m m' : Mem}
    (h : Frame [(⟨w64 St + BitVec.ofNat 64 48, 16⟩ : Region), ⟨w64 D + BitVec.ofNat 64 j, 16 * nb⟩,
      below SP 1536] m m') : Frame (crFrame St W SP K D n) m m' := by
  subst hK
  exact h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub_base _ hj⟩
    · exact ⟨below SP 1536, by simp, fun _ h => h⟩

theorem cWhole3 (hK : K = 1536) {j nb : Nat} (hnb : nb ≠ 0) (hnbd : nb = (n - j) / 16) {m₀ : Mem} {s₁ s₂ s' : State}
    (h : CWhole1 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (icb := icb) (D := D) (n := n)
      (P := P) j nb m₀ s₁)
    (m₂ : s₂.mem = s₁.mem) (rd₂ : s₂.rd = s₁.rd) (wr₂ : s₂.wr = s₁.wr)
    (g : CtrOut Ctx St W SP (St + BitVec.ofNat 32 48) (D + BitVec.ofNat 32 j) nb s₂ s') :
    CrMid Ctx St W SP K icb D n P m₀ (j + 16 * nb) s' := by
  have ha := h.at_
  have hd := ha.data
  have hj : j + 16 * nb ≤ n := by omega_using [hnb, hnbd]
  have hjn : j < n := by omega_using [hnb, hnbd]
  have eP := hd.ok.ptr hjn
  have eC := L.aS (o := 48) (by decide)
  have gf := g.frame
  have go := g.out
  have gc := g.ctr
  rw [eC, eP, m₂] at gf
  rw [eC, eP, m₂] at go
  rw [eC, m₂] at gc
  have hn := hd.ok.n_lt
  have crs := ctrFr_crFrame L (D := D) (n := n) hK hj gf
  have hcm : ciphOf s₁.mem Ctx = ciphOf m₀ Ctx := ciph_crFrame L hd ha.frame
  rw [hcm] at go
  have hw : (P + j) % 16 = 0 := ha.whole.resolve_left (by omega_using [hjn])
  have hrest16 : bytesAt s₁.mem (w64 D + BitVec.ofNat 64 j) (16 * nb) =
      bytesAt m₀ (w64 D + BitVec.ofNat 64 j) (16 * nb) := by
    have e := congrArg (List.take (16 * nb)) ha.rest
    rwa [bytesAt_take _ _ (by omega_using [hnbd]), bytesAt_take _ _ (by omega_using [hnbd])] at e
  refine ⟨⟨g.env, hj, ha.nlt, hd.of_eq (g.rd.trans rd₂) (g.wr.trans wr₂), fun hc₀ => ?_, fun hc₀ => ?_,
    ?_, .inr (by omega_using [hw]), ha.frame.trans crs⟩, ?_, ?_⟩
  · have := (Proof.Gcm.ctr_whole (ha.ctr hc₀) hw go gc).2
    rwa [Nat.add_assoc] at this
  · have w := (Proof.Gcm.ctr_whole (ha.ctr hc₀) hw go gc).1
    rw [hrest16] at w
    refine done_append ?_ w
    have := ctrFr_disj L hK hd (a := 0) (l := j) (j := j) (nb := nb) (by omega_using [hj]) (.inl (by omega_using [])) hj
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at this
    rw [bytesAt_frame gf this (by omega_using [hnb, hnbd, hn])]; exact ha.done hc₀
  · rw [bytesAt_frame gf (ctrFr_disj L hK hd (by omega_using [hnb, hnbd]) (.inr (Nat.le_refl _)) hj) (by omega_using [hnbd])]
    have e := congrArg (List.drop (16 * nb)) ha.rest
    rw [bytesAt_drop _ _ (by omega_using [hnbd]), bytesAt_drop _ _ (by omega_using [hnbd]), add_ofNat_assoc,
      show n - j - 16 * nb = n - (j + 16 * nb) by omega_using []] at e
    exact e
  · rw [slotv_eq, slot_frame gf (ctrFr_slot L hK hd (by decide) (by decide) hj)]; exact h.dO
  · rw [slotv_eq, slot_frame gf (ctrFr_slot L hK hd (by decide) (by decide) hj)]
    have := h.nO; rw [slotv_eq] at this; rw [this]; congr 1; omega_using [hnbd]

theorem cryptWhole_pc (hK : K = 1536) {j : Nat} :
    Pc (CrMid Ctx St W SP K icb D n P · j) (cryptWhole ci.fn)
      (CrMid Ctx St W SP K icb D n P · (j + 16 * ((n - j) / 16))) := by
  generalize hnb : (n - j) / 16 = nb
  refine Pc.seq (Q := CWhole1 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (icb := icb) (D := D)
      (n := n) (P := P) j nb)
    (hnb ▸ Pc.taint [.ebp] (fun m₀ s h => cWhole1_ok L h)
      (fun _ _ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.at_.env.ebp, h₂.at_.env.ebp]) (by taint_decide)) ?_
  refine Pc.ite (decide (nb = 0)) (fun _ _ h => h.zf) (fun ht => ?_) (fun hf => ?_)
  · have h0 : nb = 0 := by simpa using ht
    subst h0
    refine Pc.mono Pc.nil (fun _ _ h => h) fun m₀ s h => ?_
    rw [show j + 16 * 0 = j by omega_using []]
    refine ⟨h.at_, by rw [h.dO, show j + 16 * 0 = j by omega_using []], by rw [h.nO]; congr 1; omega_using [hnb]⟩
  · have h0 : nb ≠ 0 := by simpa using hf
    have hjn : j + 16 * nb ≤ n := by omega_using [hnb, h0]
    refine Pc.seq (cArgs_pc L hK h0 hjn) ?_
    exact Pc.mono (Pc.of (I := CtrReady Ctx St W SP (St + BitVec.ofNat 32 48) (D + BitVec.ofNat 32 j) nb)
        (fun _ h => ctrW_ok L hK h) (ctrW_ct L hK) _ fun _ _ ⟨_, _, g, _⟩ => g) (fun _ _ h => h)
      fun m₀ s₃ ⟨s₂, ⟨s₁, h₁, _, m₂, rd₂, wr₂⟩, g₃⟩ => cWhole3 L hK h0 hnb.symm h₁ m₂ rd₂ wr₂ g₃

end

end VG.Proof.Sm4Gcm.X86

end

end

/-! ### `Sm4Gcm.X86.CryptHead`, which only this module used -/

section

/-!
# SM4-GCM on x86: the rest of the keystream block (`cryptHead`)

Untrusted: everything here is checked by Lean. With `P mod 16 ≠ 0` bytes of
the keystream block used, `cryptHead` XORs the next `min (16 - P mod 16, n)`
into the data (`cryptHead_pc`), by `Proof.Gcm.ctr_head`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.Sm4Gcm.X86 VG.WriteBytes VG.Proof.AesGcm.X86
open VG.Impl.AesGcm.X86 hiding ctrCall keyCall ctrArgs cryptWhole cryptTail crypt tag init cryptEntry
  streamEncrypt streamDecrypt finEntry finTag streamFinish streamVerify oneEntry oneTag oneCrypt «seal» «open»
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt)
open VG.Proof.Gcm (Ctr xorKs)

section
variable {Ctx St W SP : BitVec 32} {K : Nat} (L : Lay4 Ctx St W SP K) {icb : Block}
  {D : BitVec 32} {n P : Nat}
include L

/-- After the block that sets up the XOR. -/
structure CHead2 (k : Nat) (m₀ : Mem) (s : State) : Prop where
  env : Env Ctx St W SP s
  edi : s.gpr .edi = D
  edx : s.gpr .edx = St + BitVec.ofNat 32 (64 + P % 16)
  ecx : s.gpr .ecx = BitVec.ofNat 32 k
  dO : slotv s.mem W dO = D + BitVec.ofNat 32 k
  nO : slotv s.mem W nO = BitVec.ofNat 32 (n - k)
  fr : Frame [pslotR W] m₀ s.mem
  data : DataW Ctx St W SP K s D n
  nlt : n < 2 ^ 32

theorem cHead2_ok (k : Nat) (hk : k ≤ n) (m₀ : Mem) {s : State} (h : CrIn Ctx St W SP K D n P s)
    (hm : s.mem = m₀) {s₁ : State} (hs₁ : MinOut k s s₁) :
    WP isa (.block [.mov .edi (slot dO), .mov .edx (.reg .esi), .alu .add .edx (imm 64), .alu .add .edx (slot bO),
      .mov .eax (slot nO), .alu .sub .eax (.reg .ecx), .store (at_ .ebp nO) .eax,
      .mov .eax (.reg .edi), .alu .add .eax (.reg .ecx), .store (at_ .ebp dO) .eax]) s₁
      (CHead2 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (D := D) (n := n) (P := P) k m₀) := by
  have he := h.env
  have he₁ : Env Ctx St W SP s₁ := he.keep (hs₁.other _ (by decide) (by decide))
    (hs₁.other _ (by decide) (by decide)) (hs₁.other _ (by decide) (by decide)) hs₁.rd hs₁.wr (by rw [hs₁.mem])
  have hd : slotv s₁.mem W dO = D := by rw [hs₁.mem]; exact h.dO
  have hn : slotv s₁.mem W nO = BitVec.ofNat 32 n := by rw [hs₁.mem]; exact h.nO
  have hb : slotv s₁.mem W bO = BitVec.ofNat 32 (P % 16) := by rw [hs₁.mem]; exact h.bO
  have hc := hs₁.ecx
  have esub : BitVec.ofNat 32 n - BitVec.ofNat 32 k = BitVec.ofNat 32 (n - k) := ofNat_sub32 hk h.nlt
  refine WP.of_runBlock ⟨_, by xrun [he₁.ebp, he₁.esi, L.aW, he₁.wIn, he₁.wIn', hd, hn, hb, hc], ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.nlt⟩
  · exact he₁.keep (by regs []) (by regs []) (by regs []) rfl rfl (by mems [])
  · regs [hd]
  · regs [he₁.esi, add_ofNat_assoc32]
  · regs [hc]
  · mems [slotv_eq, hd, hc]
  · mems [slotv_eq, hn, hc, esub]
  · simp only [mem_setMem, gpr_setMem, mem_setReg, mem_arithFlags, ← hs₁.mem, ← hm]
    exact pslot_write (pslot_write (Frame.refl _ _) (by decide) (by decide) _) (by decide) (by decide) _
  · exact h.data.of_eq (by mems [hs₁.rd]) (by mems [hs₁.wr])

/-- The XOR with the rest of the keystream block. -/
theorem cHead3_ok (k : Nat) (hkn : k ≤ n) (hk1 : 1 ≤ k) (hbk : P % 16 + k ≤ 16) (hw : k = n ∨ P % 16 + k = 16)
    (hP : P % 16 ≠ 0) (m₀ : Mem) {s : State}
    (h : CHead2 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (D := D) (n := n) (P := P) k m₀ s) :
    WP isa xorLoop s (CrMid Ctx St W SP K icb D n P m₀ k) := by
  have he := h.env
  have eS := L.aS (o := 64 + P % 16) (by omega_using [])
  have dk := h.data.take hkn
  have xp : XorPre s (St + BitVec.ofNat 32 (64 + P % 16)) D k := by
    refine ⟨h.edx, h.edi, h.ecx, hk1, by have := h.nlt; omega_using [hbk], ?_, dk.ok.fit, ?_, dk.wr, ?_⟩
    · rw [L.nS (by omega_using [])]; have := L.fs; omega_using [hbk, this]
    · rw [eS]; exact covers_left (he.stC (by omega_using [hbk]))
    · rw [eS]; exact (dk.ok.st.sub_right (Lay.stSub (by omega_using [hbk]))).symm
  refine WP.mono (xorLoop_ok s xp) fun s' c => ?_
  have cm := c.mem
  rw [eS] at cm
  have hxl := length_xorBytes s.mem (w64 D) (w64 St + BitVec.ofNat 64 (64 + P % 16)) k
  have fw : Frame [⟨w64 D, k⟩] s.mem s'.mem := by rw [cm]; exact writeBytes_frame' _ hxl
  have fw' : Frame [⟨w64 D + BitVec.ofNat 64 0, k⟩] s.mem s'.mem := by simpa using fw
  have hf₁ : Frame (crFrame St W SP K D n) s.mem s'.mem := part_crFrame (j := 0) (by omega_using [hkn]) fw'
  have hf : Frame (crFrame St W SP K D n) m₀ s'.mem := (pslot_crFrame h.fr).trans hf₁
  have hlt := h.nlt
  -- What the XOR writes is apart from the state and the slots.
  have dS : ∀ {a l : Nat}, a + l ≤ 80 → ∀ r ∈ [(⟨w64 D, k⟩ : Region)], (⟨w64 St + BitVec.ofNat 64 a, l⟩ : Region).Disjoint r :=
    fun hal r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (dk.ok.st.sub_right (Lay.stSub hal)).symm
  have dW : ∀ {o : Nat}, o + 4 ≤ 2560 → ∀ r ∈ [(⟨w64 D, k⟩ : Region)], (⟨w64 W + BitVec.ofNat 64 o, 4⟩ : Region).Disjoint r :=
    fun ho r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (dk.ok.w.sub_right (Lay.wSub ho)).symm
  have pS : ∀ {a l : Nat}, a + l ≤ 80 → ∀ r ∈ [pslotR W], (⟨w64 St + BitVec.ofNat 64 a, l⟩ : Region).Disjoint r :=
    fun hal r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.st_w hal (.inr ⟨by decide, by decide⟩)
  have pD : ∀ {a l : Nat}, a + l ≤ n → ∀ r ∈ [pslotR W], (⟨w64 D + BitVec.ofNat 64 a, l⟩ : Region).Disjoint r :=
    fun hal r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.data.ok.w.sub_left (Offset.sub_base _ hal)).sub_right (Lay.wSub (by decide))
  have pD0 : ∀ r ∈ [pslotR W], (⟨w64 D, k⟩ : Region).Disjoint r := by
    have := pD (a := 0) (l := k) (by omega_using [hkn]); simpa using this
  refine ⟨⟨env_crFrame L h.data he hf₁ (c.other _ (by decide) (by decide) (by decide) (by decide) (by decide))
      (c.other _ (by decide) (by decide) (by decide) (by decide) (by decide))
      (c.other _ (by decide) (by decide) (by decide) (by decide) (by decide)) c.rd c.wr, hkn, hlt,
    h.data.of_eq c.rd c.wr, fun hc => ?_, fun hc => ?_, ?_, ?_, hf⟩,
    ?_, ?_⟩
  · refine (hc.head hP hbk).congr ?_ ?_
    · rw [blockAt_frame fw (dS (by decide)), blockAt_frame h.fr (pS (by decide))]
    · rw [blockAt_frame fw (dS (by decide)), blockAt_frame h.fr (pS (by decide))]
  · have e := bytesAt_writeBytes_self s.mem (w64 D) (xorBytes s.mem (w64 D) (w64 St + BitVec.ofNat 64 (64 + P % 16)) k)
      (by rw [hxl]; omega_using [hbk])
    rw [hxl] at e
    rw [cm, e, xorBytes, bytesAt_frame h.fr pD0 (by omega_using [hbk]), bytesAt_frame h.fr (pS (by omega_using [hbk])) (by omega_using [hbk])]
    have := Proof.Gcm.ctr_head hc hP (d := bytesAt m₀ (w64 D) k) (by rw [length_bytesAt]; exact hbk)
    rw [length_bytesAt, add_ofNat_assoc] at this
    exact this
  · rw [bytesAt_frame fw (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (split_disj (by omega_using [hkn, hlt])).symm) (by omega_using [hlt]),
      bytesAt_frame h.fr (pD (by omega_using [hkn])) (by omega_using [hlt])]
  · rcases hw with hw | hw
    · left; omega_using [hw]
    · right; omega_using [hw]
  · rw [slotv_eq, slot_frame fw (dW (by decide))]; exact h.dO
  · rw [slotv_eq, slot_frame fw (dW (by decide))]; exact h.nO

theorem cryptHead_pc (hn0 : n ≠ 0) (hP : P % 16 ≠ 0) :
    Pc (fun (m₀ : Mem) s => CrIn Ctx St W SP K D n P s ∧ s.mem = m₀) cryptHead
      (CrMid Ctx St W SP K icb D n P · (min (16 - P % 16) n)) := by
  have hb16 : P % 16 < 16 := Nat.mod_lt _ (by decide)
  generalize hk : min (16 - P % 16) n = k
  have hkn : k ≤ n := by omega_using [hk]
  have hk1 : 1 ≤ k := by omega_using [hn0, hk]
  have hbk : P % 16 + k ≤ 16 := by omega_using [hk]
  have hw : k = n ∨ P % 16 + k = 16 := by omega_using [hk]
  refine Pc.seq (Q := fun m₀ s₁ => ∃ s, (CrIn Ctx St W SP K D n P s ∧ s.mem = m₀) ∧ MinOut k s s₁)
    (hk ▸ Pc.of (I := CrIn Ctx St W SP K D n P) (R := MinOut (min (16 - P % 16) n))
      (fun s h => minLen_ok L.lay h.env h.nO h.bO (by omega_using []) h.nlt)
      (minLen_ct fun s h => ⟨h.env.ebp, Ctx, St, SP, 28, L.lay, h.env, h.nO, h.bO, by omega_using [], h.nlt⟩)
      _ fun _ _ h => h.1) ?_
  refine Pc.seq (Q := CHead2 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (D := D) (n := n)
      (P := P) k)
    (Pc.taint [.ebp, .esi] (fun m₀ s₁ ⟨s, ⟨h, hm⟩, hs₁⟩ => cHead2_ok L k hkn m₀ h hm hs₁)
      (fun _ _ s₁ s₂ ⟨t₁, ⟨h₁, _⟩, g₁⟩ ⟨t₂, ⟨h₂, _⟩, g₂⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [g₁.other _ (by decide) (by decide), g₂.other _ (by decide) (by decide), h₁.env.ebp, h₂.env.ebp]
        · rw [g₁.other _ (by decide) (by decide), g₂.other _ (by decide) (by decide), h₁.env.esi, h₂.env.esi])
      (by taint_decide)) ?_
  exact Pc.taint [.edi, .edx, .ecx] (fun m₀ s h => cHead3_ok L k hkn hk1 hbk hw hP m₀ h)
    (fun _ _ s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h₁.edi, h₂.edi]
      · rw [h₁.edx, h₂.edx]
      · rw [h₁.ecx, h₂.ecx])
    (by taint_decide)

end

end VG.Proof.Sm4Gcm.X86

end

end

/-!
# SM4-GCM on x86: the last bytes of the text (`cryptTail`), and `crypt`

Untrusted: everything here is checked by Lean. From a block boundary with
fewer than 16 bytes left, `cryptTail` makes the next keystream block (the
counter block encrypted onto zeros, by `vg_sm4_ctr32`) and XORs it into
them (`cryptTail_pc`), by `Proof.Gcm.ctr_tail`. `crypt_pc`: the three
pieces.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.Sm4Gcm.X86 VG.WriteBytes VG.Proof.AesGcm.X86
open VG.Impl.AesGcm.X86 hiding ctrCall keyCall ctrArgs cryptWhole cryptTail crypt tag init cryptEntry
  streamEncrypt streamDecrypt finEntry finTag streamFinish streamVerify oneEntry oneTag oneCrypt «seal» «open»
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt)
open VG.Proof.Gcm (Ctr xorKs)

/-- The regions `vg_sm4_ctr32` writes for the keystream block. -/
abbrev ksFrame (St SP : BitVec 32) : List Region :=
  [⟨w64 St + BitVec.ofNat 64 48, 16⟩, ⟨w64 St + BitVec.ofNat 64 64, 16 * 1⟩, below SP 1536]

section
variable {Ctx St W SP : BitVec 32} {K : Nat} (L : Lay4 Ctx St W SP K) {ci : CtrImpl}
include L

theorem ksFrame_crFrame (hK : K = 1536) {D : BitVec 32} {n : Nat} {m m' : Mem} (h : Frame (ksFrame St SP) m m') :
    Frame (crFrame St W SP K D n) m m' := by
  subst hK
  exact h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨below SP 1536, by simp, fun _ h => h⟩

omit L in
theorem ks_crFrame {D : BitVec 32} {n : Nat} {m m' : Mem} (h : Frame [⟨w64 St + BitVec.ofNat 64 64, 16⟩] m m') :
    Frame (crFrame St W SP K D n) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub _ (by decide) (by decide)⟩

theorem data_ksFrame (hK : K = 1536) {s : State} {D : BitVec 32} {n : Nat} (hd : DataW Ctx St W SP K s D n) {a l : Nat}
    (hal : a + l ≤ n) : ∀ r ∈ ksFrame St SP, (⟨w64 D + BitVec.ofNat 64 a, l⟩ : Region).Disjoint r := by
  subst hK
  obtain hs : Region.Sub ⟨w64 D + BitVec.ofNat 64 a, l⟩ ⟨w64 D, n⟩ := Offset.sub_base _ hal
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hd.ok.st.sub_left hs).sub_right (Lay.stSub (by decide))
  · exact (hd.ok.st.sub_left hs).sub_right (Lay.stSub (by decide))
  · exact (hd.ok.stk.sub_right hs).symm

theorem slot_ksFrame (hK : K = 1536) {o : Nat} (h₁ : 240 ≤ o) (h₂ : o + 4 ≤ 512) :
    ∀ r ∈ ksFrame St SP, (⟨w64 W + BitVec.ofNat 64 o, 4⟩ : Region).Disjoint r := by
  subst hK
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (L.st_w (by decide) (.inr ⟨by omega_arith, by omega_arith⟩)).symm
  · exact (L.st_w (by decide) (.inr ⟨by omega_arith, by omega_arith⟩)).symm
  · exact (L.stk_w (by omega_arith)).symm

variable {icb : Block} {D : BitVec 32} {n P : Nat}

/-- The keystream block zeroed, and the arguments of `vg_sm4_ctr32` for it. -/
theorem tail1_ok {s : State} (he : Env Ctx St W SP s) :
    WP isa (.block (([.mov .eax (imm 0), .store (at_ .esi 64) .eax, .store (at_ .esi 68) .eax,
          .store (at_ .esi 72) .eax, .store (at_ .esi 76) .eax, .mov .ebx (.reg .esi), .alu .add .ebx (imm 64),
          .mov .edi (imm 1)] : List Instr) ++ ctrArgs)) s fun s' =>
      s'.mem = Cmac.zero4 s.mem (w64 St + BitVec.ofNat 64 64) ∧ s'.gpr .eax = Ctx ∧
      s'.gpr .edx = St + BitVec.ofNat 32 48 ∧
      s'.gpr .ebp = W ∧ s'.gpr .ebx = St + BitVec.ofNat 32 64 ∧
      s'.gpr .edi = BitVec.ofNat 32 1 ∧ s'.gpr .esi = St ∧ s'.gpr .esp = SP ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, m₁, bx, di, g₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [.mov .eax (imm 0), .store (at_ .esi 64) .eax,
      .store (at_ .esi 68) .eax, .store (at_ .esi 72) .eax, .store (at_ .esi 76) .eax, .mov .ebx (.reg .esi),
      .alu .add .ebx (imm 64), .mov .edi (imm 1)] s = some s₁ ∧
      s₁.mem = Cmac.zero4 s.mem (w64 St + BitVec.ofNat 64 64) ∧ s₁.gpr .ebx = St + BitVec.ofNat 32 64 ∧
      s₁.gpr .edi = BitVec.ofNat 32 1 ∧ (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .edi → s₁.gpr r = s.gpr r) ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by xrun [he.esi, L.aS, he.stIn], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · mems []; simp only [Proof.Cmac.zero4, Proof.Cmac.store4, add_ofNat_assoc]; rfl
    · regs [he.esi]
    · regs []
    · intro r h₁ h₂ h₃
      simp only [gpr_setMem, gpr_arithFlags, gpr_setReg_of_ne _ _ h₁, gpr_setReg_of_ne _ _ h₂,
        gpr_setReg_of_ne _ _ h₃]
    all_goals rfl
  obtain fz : Frame [⟨w64 St + BitVec.ofNat 64 64, 16⟩] s.mem s₁.mem := by rw [m₁]; exact Cmac.frame_store4 _ _ _ _ _
  obtain he₁ : Env Ctx St W SP s₁ := he.keep (g₁ _ (by decide) (by decide) (by decide))
    (g₁ _ (by decide) (by decide) (by decide)) (g₁ _ (by decide) (by decide) (by decide)) rd₁ wr₁
    (slot_frame fz fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm)
  obtain ⟨s₂, run₂, ax, dx, g₂, m₂, rd₂, wr₂⟩ := ctrArgs_ok L he₁
  refine WP.of_runBlock ⟨s₂, runBlock_app_of run₁ run₂, by rw [m₂, m₁], ax, dx,
    by rw [g₂ _ (by decide) (by decide), he₁.ebp],
    by rw [g₂ _ (by decide) (by decide), bx],
    by rw [g₂ _ (by decide) (by decide), di],
    by rw [g₂ _ (by decide) (by decide), he₁.esi],
    by rw [g₂ _ (by decide) (by decide), he₁.esp], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩

/-- After the call: the keystream block for the last bytes, and the counter block after it. -/
structure CTail (j : Nat) (m₀ : Mem) (s : State) : Prop where
  env : Env Ctx St W SP s
  le : j ≤ n
  nlt : n < 2 ^ 32
  hlt : n - j < 16
  nz : n - j ≠ 0
  data : DataW Ctx St W SP K s D n
  dO : slotv s.mem W dO = D + BitVec.ofNat 32 j
  nO : slotv s.mem W nO = BitVec.ofNat 32 (n - j)
  ks : CtrS m₀ St (ciphOf m₀ Ctx) icb P → ∃ m, CtrS m St (ciphOf m₀ Ctx) icb (P + j) ∧
    blockAt s.mem (w64 St + BitVec.ofNat 64 64) = ciphOf m₀ Ctx (blockAt m (w64 St + BitVec.ofNat 64 48)) ∧
    blockAt s.mem (w64 St + BitVec.ofNat 64 48) = Spec.Gcm.inc32 (blockAt m (w64 St + BitVec.ofNat 64 48))
  done : CtrS m₀ St (ciphOf m₀ Ctx) icb P →
    bytesAt s.mem (w64 D) j = xorKs (ciphOf m₀ Ctx) icb P (bytesAt m₀ (w64 D) j)
  rest : bytesAt s.mem (w64 D + BitVec.ofNat 64 j) (n - j) = bytesAt m₀ (w64 D + BitVec.ofNat 64 j) (n - j)
  whole : (P + j) % 16 = 0
  frame : Frame (crFrame St W SP K D n) m₀ s.mem

theorem tail2 (hK : K = 1536) {j : Nat} (hlt : n - j < 16) (hnz : n - j ≠ 0) {m₀ : Mem} {s₀ s₁ s₂ : State}
    (h : CrMid Ctx St W SP K icb D n P m₀ j s₀) (m₁ : s₁.mem = Cmac.zero4 s₀.mem (w64 St + BitVec.ofNat 64 64))
    (rd₁ : s₁.rd = s₀.rd) (wr₁ : s₁.wr = s₀.wr)
    (g : CtrOut Ctx St W SP (St + BitVec.ofNat 32 48) (St + BitVec.ofNat 32 64) 1 s₁ s₂) :
    CTail (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (icb := icb) (D := D) (n := n) (P := P)
      j m₀ s₂ := by
  have ha := h.at_
  have hd := ha.data
  obtain eC := L.aS (o := 48) (by decide)
  obtain eK := L.aS (o := 64) (by decide)
  have gf := g.frame
  have go := g.out
  have gc := g.ctr
  rw [eC, eK] at gf go
  rw [eC] at gc
  obtain fz : Frame [⟨w64 St + BitVec.ofNat 64 64, 16⟩] s₀.mem s₁.mem := by rw [m₁]; exact Cmac.frame_store4 _ _ _ _ _
  obtain zS : ∀ r ∈ [(⟨w64 St + BitVec.ofNat 64 64, 16⟩ : Region)], (⟨w64 St + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r :=
    fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.st_st (.inl (by decide)) (by decide) (by decide)
  obtain zD : ∀ {a l : Nat}, a + l ≤ n → ∀ r ∈ [(⟨w64 St + BitVec.ofNat 64 64, 16⟩ : Region)],
      (⟨w64 D + BitVec.ofNat 64 a, l⟩ : Region).Disjoint r := fun hal r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hd.ok.st.sub_left (Offset.sub_base _ hal)).sub_right (Lay.stSub (by decide))
  obtain zW : ∀ {o : Nat}, 96 ≤ o → o + 4 ≤ 2560 → ∀ r ∈ [(⟨w64 St + BitVec.ofNat 64 64, 16⟩ : Region)],
      (⟨w64 W + BitVec.ofNat 64 o, 4⟩ : Region).Disjoint r := fun h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (L.st_w (by decide) (.inr ⟨h₁, h₂⟩)).symm
  have hn := hd.ok.n_lt
  obtain hcm : ciphOf s₁.mem Ctx = ciphOf m₀ Ctx := by
    rw [ciph_crFrame L hd (ks_crFrame fz), ciph_crFrame L hd ha.frame]
  rw [hcm] at go
  obtain hb0 : blockAt s₁.mem (w64 St + BitVec.ofNat 64 64) = 0 := by
    rw [Spec.Gcm.blockAt, m₁, zero4_bytes', ofBytes_zeros]
  rw [blocksAt_one, blocksAt_one, hb0] at go
  obtain hks := congrArg (fun l => List.getD l 0 0) go
  simp only [List.getD_cons_zero] at hks
  rw [Proof.Gcm.ctr32_getD _ _ _ (by simp)] at hks
  simp only [List.getD_cons_zero, BitVec.zero_xor] at hks
  obtain hcb : blockAt s₁.mem (w64 St + BitVec.ofNat 64 48) = blockAt s₀.mem (w64 St + BitVec.ofNat 64 48) :=
    blockAt_frame fz zS
  refine ⟨g.env, ha.le, ha.nlt, hlt, hnz, hd.of_eq (g.rd.trans rd₁) (g.wr.trans wr₁), ?_, ?_,
    fun hc₀ => ⟨s₀.mem, ha.ctr hc₀, ?_, ?_⟩, fun hc₀ => ?_, ?_, ha.whole.resolve_left hnz,
    (ha.frame.trans (ks_crFrame fz)).trans (ksFrame_crFrame L hK gf)⟩
  · rw [slotv_eq, slot_frame gf (slot_ksFrame L hK (by decide) (by decide)),
      slot_frame fz (zW (by decide) (by decide))]; exact h.dO
  · rw [slotv_eq, slot_frame gf (slot_ksFrame L hK (by decide) (by decide)),
      slot_frame fz (zW (by decide) (by decide))]; exact h.nO
  · rw [hks, hcb]; simp [Nat.repeat]
  · rw [gc, hcb]; rfl
  · have := data_ksFrame L hK hd (a := 0) (l := j) (by have := ha.le; omega_arith)
    obtain z := zD (a := 0) (l := j) (by have := ha.le; omega_arith)
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at this z
    rw [bytesAt_frame gf this (by omega_arith), bytesAt_frame fz z (by omega_arith)]; exact ha.done hc₀
  · rw [bytesAt_frame gf (data_ksFrame L hK hd (by omega_arith)) (by omega_arith), bytesAt_frame fz (zD (by omega_arith)) (by omega_arith)]
    exact ha.rest

theorem tail3 {j : Nat} {m₀ : Mem} {s : State}
    (h : CTail (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (icb := icb) (D := D) (n := n) (P := P)
      j m₀ s) {s' : State}
    (hx : XorPost s (St + BitVec.ofNat 32 64) (D + BitVec.ofNat 32 j) (n - j) s') :
    CrOut Ctx St W SP K icb D n P m₀ s' := by
  have hd := h.data
  obtain hjn : j < n := by have := h.nz; omega_arith
  obtain eP := hd.ok.ptr hjn
  obtain eK := L.aS (o := 64) (by decide)
  have cm := hx.mem
  rw [eP, eK] at cm
  have hn := hd.ok.n_lt
  obtain hxl := length_xorBytes s.mem (w64 D + BitVec.ofNat 64 j) (w64 St + BitVec.ofNat 64 64) (n - j)
  obtain fw : Frame [⟨w64 D + BitVec.ofNat 64 j, n - j⟩] s.mem s'.mem := by rw [cm]; exact writeBytes_frame' _ hxl
  obtain hf₁ : Frame (crFrame St W SP K D n) s.mem s'.mem := part_crFrame (by omega_arith) fw
  obtain dS : ∀ {a l : Nat}, a + l ≤ 80 → ∀ r ∈ [(⟨w64 D + BitVec.ofNat 64 j, n - j⟩ : Region)],
      (⟨w64 St + BitVec.ofNat 64 a, l⟩ : Region).Disjoint r := fun hal r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hd.ok.st.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Lay.stSub hal) |>.symm
  obtain e := bytesAt_writeBytes_self s.mem (w64 D + BitVec.ofNat 64 j)
    (xorBytes s.mem (w64 D + BitVec.ofNat 64 j) (w64 St + BitVec.ofNat 64 64) (n - j)) (by rw [hxl]; omega_arith)
  rw [hxl] at e
  refine ⟨env_crFrame L hd h.env hf₁ (hx.other _ (by decide) (by decide) (by decide) (by decide) (by decide))
      (hx.other _ (by decide) (by decide) (by decide) (by decide) (by decide))
      (hx.other _ (by decide) (by decide) (by decide) (by decide) (by decide)) hx.rd hx.wr, fun hc₀ => ?_, fun hc₀ => ?_, h.frame.trans hf₁⟩
  · obtain ⟨m, hm, hk, hc⟩ := h.ks hc₀
    obtain t := (Proof.Gcm.ctr_tail hm h.whole hk hc (d := bytesAt s.mem (w64 D + BitVec.ofNat 64 j) (n - j))
      (by rw [length_bytesAt]; exact h.hlt) (by rw [length_bytesAt]; exact h.nz)).2
    rw [length_bytesAt, show P + j + (n - j) = P + n by omega_arith] at t
    exact t.congr (blockAt_frame fw (dS (by decide))) (blockAt_frame fw (dS (by decide)))
  · obtain ⟨m, hm, hk, hc⟩ := h.ks hc₀
    obtain t := (Proof.Gcm.ctr_tail hm h.whole hk hc (d := bytesAt s.mem (w64 D + BitVec.ofNat 64 j) (n - j))
      (by rw [length_bytesAt]; exact h.hlt) (by rw [length_bytesAt]; exact h.nz)).1
    rw [length_bytesAt, h.rest] at t
    rw [show n = j + (n - j) by omega_arith]
    refine done_append ?_ ?_
    · have := split_disj (D := w64 D) (j := j) (l := n - j) (by omega_arith)
      rw [bytesAt_frame fw (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact this) (by omega_arith)]
      exact h.done hc₀
    · rw [cm, e, xorBytes, h.rest]; exact t

theorem cryptTail_pc (hK : K = 1536) {j : Nat} (hlt : n - j < 16) :
    Pc (CrMid Ctx St W SP K icb D n P · j) (cryptTail ci.fn) (CrOut Ctx St W SP K icb D n P ·) := by
  refine Pc.seq (Q := fun m₀ s => CrMid Ctx St W SP K icb D n P m₀ j s ∧ s.zf = some (decide (n - j = 0)))
    (Pc.taint [.ebp] (fun m₀ s h => WP.mono (test_ok L.lay h.at_.env .eax nO (by decide) h.nO
        (by have := h.at_.nlt; omega_arith))
        fun s' ⟨zf, _, g, m, rd, wr⟩ => ⟨⟨h.at_.pslot L (by rw [m]; exact Frame.refl _ _) (g _ (by decide))
          (g _ (by decide)) (g _ (by decide)) rd wr, by rw [m]; exact h.dO, by rw [m]; exact h.nO⟩, zf⟩)
      (fun _ _ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.at_.env.ebp, h₂.at_.env.ebp]) (by taint_decide)) ?_
  refine Pc.ite (decide (n - j = 0)) (fun _ _ h => h.2) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n - j = 0 := by simpa using ht
    refine Pc.mono Pc.nil (fun _ _ h => h) fun m₀ s ⟨h, _⟩ => ?_
    have ha := h.at_
    obtain e : j = n := by have := ha.le; omega_arith
    subst e
    exact ⟨ha.env, ha.ctr, ha.done, ha.frame⟩
  obtain hnz : n - j ≠ 0 := by simpa using hf
  refine Pc.seq (Q := fun m₀ s => ∃ s₀, CrMid Ctx St W SP K icb D n P m₀ j s₀ ∧
      s.mem = Cmac.zero4 s₀.mem (w64 St + BitVec.ofNat 64 64) ∧
      CtrReady Ctx St W SP (St + BitVec.ofNat 32 48) (St + BitVec.ofNat 32 64) 1 s ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr)
    (Pc.taint [.ebp, .esi] (fun m₀ s ⟨h, _⟩ => ?_)
      (fun _ _ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h₁.1.at_.env.ebp, h₂.1.at_.env.ebp]
        · rw [h₁.1.at_.env.esi, h₂.1.at_.env.esi]) (by taint_decide)) ?_
  · subst hK
    have he := h.at_.env
    refine WP.mono (tail1_ok L he) fun s' ⟨m, ax, dx, bp, bx, di, si, sp, rd, wr⟩ => ⟨s, h, m, ?_, rd, wr⟩
    obtain eC := L.aS (o := 48) (by decide)
    obtain eK := L.aS (o := 64) (by decide)
    obtain fz : Frame [⟨w64 St + BitVec.ofNat 64 64, 16⟩] s.mem s'.mem := by rw [m]; exact Cmac.frame_store4 _ _ _ _ _
    refine ⟨ax, dx, bx, di, bp, si, sp, by rw [rd, wr]; exact he.ctxR, by rw [wr]; exact he.stW,
      by rw [wr]; exact he.wW, ?_, by rw [L.nS (by decide)]; have := L.fs; omega_arith,
      by rw [L.nS (by decide)]; have := L.fs; omega_arith, by rw [wr, eC]; exact he.stC (by decide),
      by rw [wr, eK]; exact he.stC (by decide), by rw [eC, eK]; exact Lay.st_st (.inl (by decide)) (by decide) (by decide),
      by rw [eC]; exact L.cs.sub_right (Lay.stSub (by decide)), by rw [eK]; exact L.cs.sub_right (Lay.stSub (by decide)),
      by rw [eC]; exact L.stk_st (by decide), by rw [eK]; exact L.stk_st (by decide),
      by rw [eC]; exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm,
      by rw [eK]; exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm⟩
    · rw [slot_frame fz fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm]
      exact he.ctx
  refine Pc.seq (Q := CTail (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (icb := icb) (D := D)
      (n := n) (P := P) j)
    (Pc.mono (Pc.of (I := CtrReady Ctx St W SP (St + BitVec.ofNat 32 48) (St + BitVec.ofNat 32 64) 1)
        (fun _ h => ctrW_ok L hK h) (ctrW_ct L hK) _ fun _ _ ⟨_, _, _, g, _⟩ => g) (fun _ _ h => h)
      fun m₀ s₂ ⟨s₁, ⟨s₀, h₀, m₁, _, rd₁, wr₁⟩, g⟩ => tail2 L hK hlt hnz h₀ m₁ rd₁ wr₁ g) ?_
  refine Pc.seq (Q := fun m₀ s => CTail (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (icb := icb)
      (D := D) (n := n) (P := P) j m₀ s ∧ s.gpr .edi = D + BitVec.ofNat 32 j ∧ s.gpr .edx = St + BitVec.ofNat 32 64 ∧
      s.gpr .ecx = BitVec.ofNat 32 (n - j))
    (Pc.taint [.ebp, .esi] (fun m₀ s h => ?_)
      (fun _ _ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h₁.env.ebp, h₂.env.ebp]
        · rw [h₁.env.esi, h₂.env.esi]) (by taint_decide)) ?_
  · have he := h.env
    have hd := h.dO
    have hn := h.nO
    refine WP.of_runBlock ⟨_, by xrun [he.ebp, he.esi, L.aW, he.wIn', hd, hn], ?_, ?_, ?_, ?_⟩
    · refine ⟨he.keep (by regs []) (by regs []) (by regs []) (by mems []) (by mems []) (by mems []), h.le, h.nlt,
        h.hlt, h.nz, h.data.of_eq (by mems []) (by mems []), by mems []; exact h.dO,
        by mems []; exact h.nO, by mems []; exact h.ks, by mems []; exact h.done, by mems []; exact h.rest, h.whole,
        by mems []; exact h.frame⟩
    · regs []
    · regs [he.esi]
    · regs []
  refine Pc.taint [.edi, .edx, .ecx] (fun m₀ s ⟨h, di, dx, cx⟩ => ?_)
    (fun _ _ s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h₁.2.1, h₂.2.1]
      · rw [h₁.2.2.1, h₂.2.2.1]
      · rw [h₁.2.2.2, h₂.2.2.2]) (by taint_decide)
  have he := h.env
  have hdd := h.data
  obtain hjn : j < n := by have := h.nz; omega_arith
  obtain eP := hdd.ok.ptr hjn
  obtain eK := L.aS (o := 64) (by decide)
  obtain ⟨dwr, -⟩ := hdd.part (j := j) (k := n - j) (by omega_arith)
  obtain ⟨-, dst, -, -⟩ := hdd.ok.part (j := j) (k := n - j) (by omega_arith)
  obtain xp : XorPre s (St + BitVec.ofNat 32 64) (D + BitVec.ofNat 32 j) (n - j) := by
    refine ⟨dx, di, cx, by omega_arith, by have := h.nlt; omega_arith, by rw [L.nS (by decide)]; have := L.fs; omega_arith,
      by rw [hdd.ok.ptrN hjn]; have := hdd.ok.fit; omega_arith, by rw [eK]; exact covers_left (he.stC (by omega_arith)),
      by rw [eP]; exact dwr, by rw [eK, eP]; exact (dst.sub_right (Lay.stSub (by omega_arith))).symm⟩
  exact WP.mono (xorLoop_ok s xp) fun s' x => tail3 L h x

omit L in
theorem CrIn.keep {s s' : State} (h : CrIn Ctx St W SP K D n P s) (hbp : s'.gpr .ebp = s.gpr .ebp)
    (hsi : s'.gpr .esi = s.gpr .esi) (hsp : s'.gpr .esp = s.gpr .esp) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : CrIn Ctx St W SP K D n P s' :=
  ⟨h.env.keep hbp hsi hsp hrd hwr (by rw [hm]), by rw [hm]; exact h.dO, by rw [hm]; exact h.nO,
    by rw [hm]; exact h.bO, h.nlt, h.data.of_eq hrd hwr⟩

theorem crypt_pc (hK : K = 1536) :
    Pc (fun (m₀ : Mem) s => CrIn Ctx St W SP K D n P s ∧ s.mem = m₀) (crypt ci.fn)
      (CrOut Ctx St W SP K icb D n P ·) := by
  obtain hb16 : P % 16 < 16 := Nat.mod_lt _ (by decide)
  refine Pc.seq (Q := fun m₀ s => (CrIn Ctx St W SP K D n P s ∧ s.mem = m₀) ∧ s.zf = some (decide (n = 0)))
    (Pc.taint [.ebp] (fun m₀ s ⟨h, hm⟩ => WP.mono (test_ok L.lay h.env .eax nO (by decide) h.nO h.nlt)
        fun s' ⟨zf, _, g, m, rd, wr⟩ => ⟨⟨h.keep (g _ (by decide)) (g _ (by decide)) (g _ (by decide)) m rd wr,
          by rw [m, hm]⟩, zf⟩)
      (fun _ _ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.env.ebp, h₂.1.env.ebp]) (by taint_decide)) ?_
  refine Pc.ite (decide (n = 0)) (fun _ _ h => h.2) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    refine Pc.mono Pc.nil (fun _ _ h => h) fun m₀ s ⟨⟨h, hm⟩, _⟩ => ⟨h.env, fun hc => ?_, fun _ => ?_,
      by rw [hm]; exact Frame.refl _ _⟩
    · rw [hm]; exact hc
    · rw [hm]; rfl
  obtain hn0 : n ≠ 0 := by simpa using hf
  refine Pc.seq (Q := fun m₀ s => (CrIn Ctx St W SP K D n P s ∧ s.mem = m₀) ∧ s.zf = some (decide (P % 16 = 0)))
    (Pc.taint [.ebp] (fun m₀ s ⟨⟨h, hm⟩, _⟩ => WP.mono (test_ok L.lay h.env .eax bO (by decide) h.bO (by omega_arith))
        fun s' ⟨zf, _, g, m, rd, wr⟩ => ⟨⟨h.keep (g _ (by decide)) (g _ (by decide)) (g _ (by decide)) m rd wr,
          by rw [m, hm]⟩, zf⟩)
      (fun _ _ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.1.env.ebp, h₂.1.1.env.ebp]) (by taint_decide)) ?_
  generalize hj₀ : (if P % 16 = 0 then 0 else min (16 - P % 16) n) = j₀
  obtain hj₀n : j₀ ≤ n := by rw [← hj₀]; split <;> omega_arith
  refine Pc.seq (Q := (CrMid Ctx St W SP K icb D n P · j₀)) ?_
    (Pc.seq (cryptWhole_pc L hK) (cryptTail_pc L hK (by omega_arith)))
  refine Pc.ite (decide (P % 16 = 0)) (fun _ _ h => h.2) (fun ht => ?_) (fun hf => ?_)
  · have h0 : P % 16 = 0 := by simpa using ht
    simp only [h0, ↓reduceIte] at hj₀
    subst hj₀
    refine Pc.mono Pc.nil (fun _ _ h => h) fun m₀ s ⟨⟨h, hm⟩, _⟩ => ⟨⟨h.env, Nat.zero_le _, h.nlt, h.data,
      fun hc => by rw [hm]; exact hc, fun _ => by rw [hm]; rfl, by rw [hm], .inr (by omega_arith),
      by rw [hm]; exact Frame.refl _ _⟩, by rw [h.dO]; exact (BitVec.add_zero D).symm, by rw [h.nO, Nat.sub_zero]⟩
  · have h0 : P % 16 ≠ 0 := by simpa using hf
    simp only [h0, ↓reduceIte] at hj₀
    subst hj₀
    exact Pc.mono (cryptHead_pc L hn0 h0) (fun _ _ h => h.1) fun _ _ h => h

end

end VG.Proof.Sm4Gcm.X86
