module

public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyChkCk
public import VerifiedGarbage.Impl.Rsa.RISCV64.CheckCrtKey
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_check_crt_key` on RISC-V: correct

As `vg_rsa_check_key` (`KeyChkCk.lean`), without `d`: `cck_moves_ok`,
`cck_valid`, `cck_main`, `cck_correct`.
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.KeyCheck

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Keys
open VG.Impl.Rsa.RISCV64.Keys (seqs saved mov load)
open VG.Impl.Rsa.RISCV64.KeyCheck
open VG.Proof.Rsa.KeyWorkspace (upd upd_ne upd_self)
open VG.Proof.Bignum.RISCV64.Pub (sat)

/-- The pointers and lengths of `vg_rsa_check_crt_key`, kept by the entry. -/
structure CckRegs (s0 t : State) : Prop where
  s1 : t.gpr .s1 = s0.gpr .a0
  s2 : t.gpr .s2 = s0.gpr .a1
  s3 : t.gpr .s3 = s0.gpr .a4
  s4 : t.gpr .s4 = s0.gpr .a5
  s5 : t.gpr .s5 = s0.gpr .a6
  s6 : t.gpr .s6 = s0.gpr .a7
  a2 : t.gpr .a2 = stackArg s0 0
  a3 : t.gpr .a3 = stackArg s0 2
  a6 : t.gpr .a6 = stackArg s0 4

abbrev cckRegs : List Reg := [.s1, .s2, .s3, .s4, .s5, .s6, .a2, .a3, .a6]

theorem CckRegs.of_keep {s0 t u : State} (h : CckRegs s0 t) {rs : List Reg} (k : Keep rs t u)
    (hr : ∀ r ∈ cckRegs, r ∉ rs := by decide) : CckRegs s0 u := by
  have e : ∀ r ∈ cckRegs, u.gpr r = t.gpr r := fun r hr' => k.gpr (hr r hr')
  exact ⟨(e _ (by decide)).trans h.s1, (e _ (by decide)).trans h.s2, (e _ (by decide)).trans h.s3,
    (e _ (by decide)).trans h.s4, (e _ (by decide)).trans h.s5, (e _ (by decide)).trans h.s6,
    (e _ (by decide)).trans h.a2, (e _ (by decide)).trans h.a3, (e _ (by decide)).trans h.a6⟩

/-- The arguments into their registers. -/
theorem cck_moves_ok {s0 : State} (h0 : CckP s0) (u : State) (hu : Saved s0 (stackArg s0 6) u) :
    WP isa (.block VG.Impl.Rsa.RISCV64.CheckCrtKey.moves) u fun v => CckRegs s0 v ∧ v.mem = u.mem ∧
      v.rd = u.rd ∧ v.wr = u.wr ∧ v.gpr .s11 = u.gpr .s11 ∧ v.gpr .a4 = off (s0.gpr .a2) 0 ∧
      v.gpr .a5 = BitVec.ofNat 64 (s0.gpr .a3).toNat ∧ v.gpr .s1 = off (s0.gpr .a0) 0 ∧
      v.gpr .s2 = BitVec.ofNat 64 (s0.gpr .a1).toNat := by
  have hp := cck_kpre h0
  have bu := KBase.of_saved (Z := (stackArg s0 7).toNat * 8) hu (by have := hp.zk; omega)
  have g : ∀ r, r ≠ .t0 → r ≠ .s11 → u.gpr r = s0.gpr r := fun r h1 h2 =>
    hu.keep.gpr (by simp [h1, h2])
  have sa : ∀ i < 8, stackArg u i = stackArg s0 i := fun i hi => stackArg_saved hp bu hu.sp hi
  rw [show VG.Impl.Rsa.RISCV64.CheckCrtKey.moves = [mov .s1 .a0, mov .s2 .a1, mov .s3 .a4, mov .s4 .a5,
      mov .s5 .a6, mov .s6 .a7, mov .a4 .a2, mov .a5 .a3, .addSp .t0 0] ++
      [.load .d .a2 .t0 0, .load .d .a3 .t0 16, .load .d .a6 .t0 32] from rfl, WP.block_append_iff]
  refine WP.mono (WP.keep [.s1, .s2, .s3, .s4, .s5, .s6, .a4, .a5, .t0] (Q := fun x =>
    x.gpr .s1 = u.gpr .a0 ∧ x.gpr .s2 = u.gpr .a1 ∧ x.gpr .s3 = u.gpr .a4 ∧ x.gpr .s4 = u.gpr .a5 ∧
    x.gpr .s5 = u.gpr .a6 ∧ x.gpr .s6 = u.gpr .a7 ∧ x.gpr .a4 = u.gpr .a2 ∧ x.gpr .a5 = u.gpr .a3 ∧
    x.gpr .t0 = u.sp ∧ x.mem = u.mem ∧ x.sp = u.sp) (by
      brun [mov, add_ofNat_zero', exec_addSp (show 0 < 2048 by decide)]) (by rfl) (by rfl))
    fun x ⟨⟨x1, x2, x3, x4, x5, x6, x4', x5', xt, xm, xsp⟩, kx⟩ => ?_
  have sx : ∀ i, stackArg x i = stackArg u i := fun i => by simp only [stackArg, stackArgAddr, xm, xsp]
  have hin : ∀ i < 8, InRegions (x.rd ++ x.wr) (stackArgAddr x i) 8 := fun i hi => by
    rw [kx.2.1, kx.2.2, hu.keep.2.1, hu.keep.2.2, show stackArgAddr x i = stackArgAddr s0 i by
      simp only [stackArgAddr, xsp, hu.sp]]
    exact hp.arg_rd hi
  have hal : ∀ i < 8, (stackArgAddr x i).toNat % 8 = 0 := fun i hi => by
    rw [show stackArgAddr x i = stackArgAddr s0 i by simp only [stackArgAddr, xsp, hu.sp]]
    exact hp.arg_al hi
  have t0w : ∀ (y : State) (r : Reg) (a : BitVec 64), r ≠ .t0 → y.gpr .t0 = y.sp →
      (y.write r a).gpr .t0 = (y.write r a).sp := fun y r a hr hy => by
    rw [gpr_write_of_ne _ _ (Ne.symm hr)]; exact hy
  have e0 : x.gpr .t0 = x.sp := by rw [xt, xsp]
  let y1 := x.write .a2 (stackArg x 0)
  let y2 := y1.write .a3 (stackArg y1 2)
  have e1 : y1.gpr .t0 = y1.sp := t0w _ _ _ (by decide) e0
  have e2 : y2.gpr .t0 = y2.sp := t0w _ _ _ (by decide) e1
  refine ldSp_ok (u := x) e0 (i := 0) rfl (by decide) (hin 0 (by decide)) (hal 0 (by decide)) ?_
  refine ldSp_ok (u := y1) e1 (i := 2) rfl (by decide) (hin 2 (by decide)) (hal 2 (by decide)) ?_
  refine ldSp_ok (u := y2) e2 (i := 4) rfl (by decide) (hin 4 (by decide)) (hal 4 (by decide)) ?_
  refine WP.block_nil ?_
  simp only [y1, y2, stackArg_write, sx, sa _ (by decide : 0 < 8), sa _ (by decide : 2 < 8),
    sa _ (by decide : 4 < 8)]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, xm, kx.2.1, kx.2.2, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [gpr_write, reduceCtorEq, x1, x2, x3, x4, x5, x6, x4', x5',
      g .a0 (by decide) (by decide), g .a1 (by decide) (by decide), g .a2 (by decide) (by decide),
      g .a3 (by decide) (by decide), g .a4 (by decide) (by decide), g .a5 (by decide) (by decide),
      g .a6 (by decide) (by decide), g .a7 (by decide) (by decide), ↓reduceIte,
      kx.gpr (r := .s11) (by decide), add_ofNat_zero', BitVec.ofNat_toNat, BitVec.setWidth_eq] <;> rfl

/-- `checkCrtKey` of the arguments. -/
abbrev cckOk (s0 : State) : Bool :=
  Spec.Rsa.checkCrtKey (Spec.Rsa.bytesAt s0.mem (s0.gpr .a0) (s0.gpr .a1).toNat)
    (Spec.Rsa.bytesAt s0.mem (s0.gpr .a2) (s0.gpr .a3).toNat)
    (Spec.Rsa.bytesAt s0.mem (s0.gpr .a4) (s0.gpr .a5).toNat)
    (Spec.Rsa.bytesAt s0.mem (s0.gpr .a6) (s0.gpr .a7).toNat)
    (Spec.Rsa.bytesAt s0.mem (stackArg s0 0) (s0.gpr .a5).toNat)
    (Spec.Rsa.bytesAt s0.mem (stackArg s0 2) (s0.gpr .a7).toNat)
    (Spec.Rsa.bytesAt s0.mem (stackArg s0 4) (s0.gpr .a5).toNat)

theorem cck_valid {s0 t : State} (h0 : CckP s0)
    (hb : KBase (stackArg s0 6) ((stackArg s0 7).toNat * 8) s0 t) (hr : CckRegs s0 t)
    (h4 : t.gpr .a4 = BitVec.ofNat 64
      (sat (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .a2) (s0.gpr .a3).toNat))) <<< 31)
    (hev : Spec.Rsa.exponentValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .a2) (s0.gpr .a3).toNat))
      = true)
    (hmv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .a0) (s0.gpr .a1).toNat))
      (s0.gpr .a1).toNat = true) :
    WP isa (seqs (([setup, .block eArr] : List (Prog isa)) ++ VG.Impl.Rsa.RISCV64.CheckCrtKey.loads ++
        (start ++ crtChecks) ++ ([.block ret] : List (Prog isa)))) t fun u =>
      KBase (stackArg s0 6) ((stackArg s0 7).toNat * 8) s0 u ∧
        u.gpr .a0 = BitVec.ofNat 64 (if cckOk s0 then 1 else 0) := by
  have hp := cck_kpre h0
  obtain ⟨-, hw8, -, hkw⟩ := hp.ws
  have he' : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .a2) (s0.gpr .a3).toNat) < 2 ^ 33 := by
    simp only [Spec.Rsa.exponentValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hev; exact hev.2
  have hsat : sat (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .a2) (s0.gpr .a3).toNat)) =
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .a2) (s0.gpr .a3).toNat) := by
    unfold sat; omega
  rw [hsat] at h4
  have p1 := h0.p1; have p2 := h0.p2; have q1 := h0.q1; have q2 := h0.q2
  have k1024 := hp.k1024
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  rw [kc_seqs_cons (by simp)]
  refine WP.mono (WP.keep [.s9, .s10, .t0, .t3, .t5] (setup_ok hp hb (hr.s2.trans (ofNat_toNat' _)))
    (by rfl) (by rfl)) fun t1 ⟨⟨b1, w1, z1, _⟩, k1⟩ => ?_
  rw [kc_seqs_cons (by simp [VG.Impl.Rsa.RISCV64.CheckCrtKey.loads])]
  refine WP.mono (eArr_ok (LdS.of_setup b1 w1 z1) rfl (by rw [k1.gpr (by decide)]; exact h4) he')
    fun t2 ⟨l2, k2⟩ => ?_
  have R := (hr.of_keep k1).of_keep k2
  simp only [VG.Impl.Rsa.RISCV64.CheckCrtKey.loads, List.cons_append]
  -- `n`.
  rw [kc_seqs_cons (by simp)]
  refine WP.mono (ldStep_ok l2 (j := aN) (by decide) rfl (by decide) R.s1 (R.s2.trans (ofNat_toNat' _))
    (by have := hp.k64; omega) (by omega) (by rw [h0.hrd]; simp) h0.dn h0.wn) fun t3 ⟨l3, k3⟩ => ?_
  have R3 := R.of_keep k3
  -- `p`.
  rw [kc_seqs_cons (by simp)]
  refine WP.mono (ldStep_ok l3 (j := aP) (by decide) rfl (by decide) R3.s3 (R3.s4.trans (ofNat_toNat' _))
    p1 (by omega) (by rw [h0.hrd]; simp) h0.dp h0.wp) fun t5 ⟨l5, k5⟩ => ?_
  have R5 := R3.of_keep k5
  -- `q`.
  rw [kc_seqs_cons (by simp)]
  refine WP.mono (ldStep_ok l5 (j := aQ) (by decide) rfl (by decide) R5.s5 (R5.s6.trans (ofNat_toNat' _))
    q1 (by omega) (by rw [h0.hrd]; simp) h0.dq h0.wq) fun t6 ⟨l6, k6⟩ => ?_
  have R6 := R5.of_keep k6
  -- `dP`.
  rw [kc_seqs_cons (by simp)]
  have ddp := h0.ddp; have wdp := h0.wdp
  simp only [rgS, cckScr, h0.hdp] at ddp
  rw [h0.hdp] at wdp
  refine WP.mono (ldStep_ok l6 (j := aDP) (by decide) rfl (by decide) R6.a2 (R6.s4.trans (ofNat_toNat' _))
    p1 (by omega) (by rw [h0.hrd, ← h0.hdp]; simp) ddp wdp) fun t7 ⟨l7, k7⟩ => ?_
  have R7 := R6.of_keep k7
  -- `dQ`.
  rw [kc_seqs_cons (by simp)]
  have ddq := h0.ddq; have wdq := h0.wdq
  simp only [rgS, cckScr, h0.hdq] at ddq
  rw [h0.hdq] at wdq
  refine WP.mono (ldStep_ok l7 (j := aDQ) (by decide) rfl (by decide) R7.a3 (R7.s6.trans (ofNat_toNat' _))
    q1 (by omega) (by rw [h0.hrd, ← h0.hdq]; simp) ddq wdq) fun t8 ⟨l8, k8⟩ => ?_
  have R8 := R7.of_keep k8
  -- `qInv`.
  rw [kc_seqs_cons (by simp [start])]
  have dqi := h0.dqi; have wqi := h0.wqi
  simp only [rgS, cckScr, h0.hqi] at dqi
  rw [h0.hqi] at wqi
  refine WP.mono (ldStep_ok l8 (j := aQI) (by decide) rfl (by decide) R8.a6 (R8.s4.trans (ofNat_toNat' _))
    p1 (by omega) (by rw [h0.hrd, ← h0.hqi]; simp) dqi wqi) fun t9 ⟨l9, k9⟩ => ?_
  have R9 := R8.of_keep k9
  -- The checks.
  let g : Geo := ⟨stackArg s0 6, (stackArg s0 7).toNat * 8, (s0.gpr .a1).toNat⟩
  let v : Vals := ⟨Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .a0) (s0.gpr .a1).toNat),
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .a2) (s0.gpr .a3).toNat),
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .a4) (s0.gpr .a5).toNat),
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .a6) (s0.gpr .a7).toNat),
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (stackArg s0 0) (s0.gpr .a5).toNat),
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (stackArg s0 2) (s0.gpr .a7).toNat),
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (stackArg s0 4) (s0.gpr .a5).toNat), 0⟩
  have a9 : Arrs t9.mem g.B g.w (vals v) live0 := fun j hj => by
    simp only [live0, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (l9.arrs.get (List.mem_range.mpr (by decide))).trans rfl
  rw [List.nil_append, kc_seqs_append (l₁ := start) (by simp [start]) (by simp [crtChecks, eqA])]
  refine WP.mono (start_ok (g := g) (v := v) l9.ws a9 (l9.top _ (by decide))) fun t10 ⟨X₁, X₂, hX, g10⟩ => ?_
  rw [kc_seqs_append (l₁ := crtChecks) (by simp [crtChecks, eqA]) (by simp)]
  refine WP.mono (crtChecks_ok g10 ⟨(s0.gpr .a7).toNat, q1, by omega, lt_pow8_of_len _ (len_bytes _ _ _),
    R9.s6.trans (ofNat_toNat' _)⟩) fun t11 ⟨R₁, R₂, R₃, hR₁, hR₂, hR₃, g11⟩ => ?_
  rw [show seqs [.block ret] = .block ret from rfl]
  refine WP.mono (ret_ok g11) fun t ⟨⟨t3, tm⟩, kt⟩ => ⟨(g11.base l9.base).of_regs kt tm, ?_⟩
  rw [t3]
  congr 2
  have e := cck_bits (k := (s0.gpr .a1).toNat) (w := g.w) hmv hev
    (lt_pow_of_len _ (by rw [len_bytes]; exact p2)) (lt_pow_of_len _ (by rw [len_bytes]; exact q2))
    (by have := hp.k64; omega) (pow_kw _) hX hR₁ hR₂ hR₃
  rw [show cckOk s0 = Spec.Rsa.crtKeyValid (s0.gpr .a1).toNat _ _ _ _ _ _ _ by
    simp only [cckOk, Spec.Rsa.checkCrtKey, len_bytes]; rfl, e]

theorem cckOk_valid {s0 : State} (h : cckOk s0 = true) :
    Spec.Rsa.exponentValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .a2) (s0.gpr .a3).toNat)) = true ∧
      Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .a0) (s0.gpr .a1).toNat))
        (s0.gpr .a1).toNat = true := by
  simp only [cckOk, Spec.Rsa.checkCrtKey, Spec.Rsa.crtKeyValid, len_bytes, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.1.1⟩

/-- `vg_rsa_check_crt_key`: the registers restored, and `checkCrtKey` returned. -/
theorem cck_main {s0 : State} (h0 : CckP s0) :
    WP isa VG.Impl.Rsa.RISCV64.CheckCrtKey.code s0 fun t =>
      (∀ i < 12, t.gpr (saved i) = s0.gpr (saved i)) ∧ t.gpr .a0 = BitVec.ofNat 64 (if cckOk s0 then 1 else 0) := by
  have hp := cck_kpre h0
  have hk := hp.k1024
  have e2 := h0.e2
  unfold VG.Impl.Rsa.RISCV64.CheckCrtKey.code
  show WP isa (fn (8 * 6) _ _ _) s0 _
  exact fn_ok hp (by decide) (MV := CckRegs s0) (cck_moves_ok h0) h0.e1 (by omega) (by rw [h0.hrd]; simp)
    h0.de h0.we (by rw [h0.hrd]; simp) h0.dn h0.wn cckOk_valid
    fun v t mv kt bt h4 ev mv' => cck_valid h0 bt (mv.of_keep kt) h4 ev mv'

/-- What `vg_rsa_check_crt_key` returns. -/
def cckPost (s s' : State) : Prop := (s'.gpr .a0).setWidth 32 = if cckOk s then 1 else 0

theorem cck_correct (s : State) (hpre : (Spec.Rsa.checkCrtKeyContract RISCV64.abi).pre s) :
    ∃ tr t, Exec isa VG.Impl.Rsa.RISCV64.CheckCrtKey.code s tr t ∧ abiPreserved s t ∧ cckPost s t := by
  show WP isa VG.Impl.Rsa.RISCV64.CheckCrtKey.code s fun t => abiPreserved s t ∧ cckPost s t
  refine WP.mono (WP.rdwr (WP.keep fnRegs (cck_main (cckP_of hpre)) (by rfl) (by rfl)))
    fun t ⟨⟨⟨hs, ha⟩, k⟩, _, _, hsp⟩ => ⟨⟨fun r hr => ?_, hsp, k.gpr (by decide)⟩, ?_⟩
  · obtain ⟨i, hi, rfl⟩ := pres_saved r hr
    exact hs i hi
  · unfold cckPost
    rw [ha]
    cases cckOk s <;> rfl

end VG.Proof.Rsa.RISCV64.KeyCheck
