module

public import VerifiedGarbage.Proof.RsaPss.X86_64.VFrame
public import VerifiedGarbage.Proof.RsaPss.X86_64.Params
public import VerifiedGarbage.Proof.RsaOaep.X86_64.EncCorrect
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# RSASSA-PSS verification on x86-64: the prologues and the checks

From the entry, the frame, the prologues, the checks of `n₀`, `emLen` and
the salt's length, then `verifyMain` if they pass, or 0 if one fails
(`verBody_ok`): `anyArgs` stores whether any salt length is accepted and
the expected one (`anyArgs_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Impl.RsaOaep.X86_64 (frameBytes sScr sScrLen sN sK sE sEl sSelH sSelG sHD oRsa argSlot arg selPrologueWith)
open VG.Impl.Mgf1.X86_64 (sp seqs)
open VG.Proof.RsaOaep.X86_64 (encStack stkR fb frR frame_sub ret_sub argAddr allocState_gpr' stackArgAddr_j tw
  Lay Rep Geo upd ea_sp Here selW fnW lenOf StepW cs_disj keep_cs3 wp_good block_good Good selPrologueWith_good
  wp_alloc freed)
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)

variable {s : State}

/-- A stack argument, read from memory the function changed only in the
stack it uses and the working space. -/
theorem arg_keepV (hp : VPre s) {m : Mem} (hf : FrV s m) {j : Nat} (hj : j < 12) :
    m.readW (off (fb s) (frameBytes + 8 + 8 * j)) 64 = stackArg s j := by
  rw [argAddr]
  refine hf.readW (r := vargsR s) ?_ (fun r hr => ?_) (by decide)
  · rw [stackArgAddr_j s j]
    exact Offset.contains_base _ (by omega) (by omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.dKa.symm
    · exact hp.dSa.symm

theorem arg_in4 (hp : VPre s) {u : State} (hrd : u.rd = s.rd) {j : Nat} (hj : j < 12) :
    InRegions (u.rd ++ u.wr) (off (fb s) (frameBytes + 8 + 8 * j)) 4 := by
  rw [hrd, hp.hrd]
  refine ⟨vargsR s, List.mem_append_left _ (by simp [vrd]), ?_⟩
  rw [argAddr, stackArgAddr_j s j]
  exact Offset.contains_base _ (by omega) (by omega)

theorem readW32_low (m : Mem) (a : Addr) : m.readW a 32 = (m.readW a 64).setWidth 32 := by
  have e := Mem.read_eq_of_bytes (n := 4) (v := (m.readW a 64).setWidth 32) (a := a) (m := m) fun i hi => by
    rw [BitVec.extractLsb'_setWidth_of_le (by omega)]
    show _ = ((m.read a 8).setWidth 64).extractLsb' (8 * i) 8
    rw [BitVec.extractLsb'_setWidth_of_le (by omega), Mem.extractLsb'_read m a (by omega : i < 8)]
  show (m.read a 4).setWidth 32 = _
  rw [e]; exact BitVec.setWidth_eq _

theorem zext32_beq_zero (x : BitVec 32) : (BitVec.setWidth 64 x == 0) = decide (x = 0) := by
  by_cases h : x = 0
  · subst h; rfl
  · have : BitVec.setWidth 64 x ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by
      have := congrArg BitVec.toNat e
      simp only [BitVec.toNat_setWidth] at this
      rw [Nat.mod_eq_of_lt (by omega)] at this
      exact this))
    rw [beq_eq_false_iff_ne.mpr this, decide_eq_false h]

/-- `any_salt_len` is zero: a salt length is expected. -/
abbrev vfixed (s : State) : Bool := decide ((stackArg s 2).setWidth 32 = 0)

/-- `anyArgs`' first block: `sSlen := salt_len` (word 29), ZF set if a length
is expected. -/
theorem any1_ok (hp : VPre s) {u : State} {S : Addr} (L : Lay u (fb s) S) (hrd : u.rd = s.rd)
    (hf : FrV s u.mem) {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep u.mem (fb s) S V W) :
    WP isa (.block [.mov .rax (.mem (arg 3)), .store (sp sSlen) .rax, .mov32 .rax (.mem (arg 2)),
      .alu .test .rax (.reg .rax)]) u fun v => Lay v (fb s) S ∧ Keep [.rax] u v ∧
      Rep v.mem (fb s) S V (upd W 29 (stackArg s 3)) ∧ v.zf = some (vfixed s) := by
  have G' := L.geo
  have R1 := R.wf G' (k := 29) (by decide) (stackArg s 3)
  rw [show off (fb s) (8 * 29) = off (fb s) sSlen from rfl] at R1
  have hF := fb_toNatV hp
  have := hp.sp2
  have a1 := arg_keepV hp hf (j := 3) (by decide)
  have a2 : (u.mem.writeW (off (fb s) sSlen) (stackArg s 3)).readW (off (fb s) (frameBytes + 8 + 8 * 2)) 32 =
      (stackArg s 2).setWidth 32 := by
    rw [readW32_low, Mem.readW_writeW_sep (Offset.sep _ (.inr (by unfold sSlen frameBytes; omega))
      (by unfold frameBytes; omega) (by unfold sSlen; omega)) (by decide), arg_keepV hp hf (j := 2) (by decide)]
  refine WP.mono (WP.keep [.rax] (Q := fun v => v.mem = u.mem.writeW (off (fb s) sSlen) (stackArg s 3) ∧
      v.zf = some (vfixed s)) ?_ rfl) fun v ⟨⟨hm, hz⟩, hk⟩ =>
    ⟨L.of_rep' R (hm ▸ R1) (by simp [upd]) (hk.gpr (by decide)) hk.2.2, hk, hm ▸ R1, hz⟩
  xrun [arg, ea_sp, L.rsp, hp.arg_in hrd (j := 3) (by decide), arg_in4 hp hrd (j := 2) (by decide), a1, a2,
    L.st (d := sSlen) (by decide)]
  rw [BitVec.and_self, zext32_beq_zero]

/-- `anyArgs`' branches: `sAny` (28) 0 if a length is expected and 1 if not,
and `rdx` the expected length, 0 if any. -/
theorem anyBr_ok {v : State} {S : Addr} (Lv : Lay v (fb s) S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R1' : Rep v.mem (fb s) S V W) (w29 : W 29 = stackArg s 3) (b : Bool) (hb : b = vfixed s) :
    WP isa (if b then .block [.mov32 .rax (.imm 0), .store (sp sAny) .rax, .mov .rdx (.mem (sp sSlen))]
      else .block [.mov32 .rax (.imm 1), .store (sp sAny) .rax, .mov32 .rdx (.imm 0)]) v fun w =>
      Lay w (fb s) S ∧ Keep [.rax, .rdx] v w ∧ Rep w.mem (fb s) S V (upd W 28 (if vfixed s then 0 else 1)) ∧
      w.gpr .rdx = if vfixed s then stackArg s 3 else 0 := by
  have G' := Lv.geo
  have R2 := R1'.wf G' (k := 28) (by decide) (if vfixed s then 0 else 1)
  rw [show off (fb s) (8 * 28) = off (fb s) sAny from rfl] at R2
  subst hb
  cases hf : vfixed s
  · simp only [hf, Bool.false_eq_true, ite_false] at R2 ⊢
    refine WP.mono (WP.keep [.rax, .rdx] (Q := fun w => w.mem = v.mem.writeW (off (fb s) sAny) (1 : BitVec 64) ∧
        w.gpr .rdx = 0) ?_ rfl)
      fun w ⟨⟨hm', hdx⟩, k'⟩ => ⟨Lv.of_rep' R1' (hm' ▸ R2) (by simp [upd]) (k'.gpr (by decide)) k'.2.2,
        k', hm' ▸ R2, hdx⟩
    xrun [ea_sp, Lv.rsp, Lv.st (d := sAny) (by decide),
      show BitVec.setWidth 64 (1 : BitVec 32) = (1 : BitVec 64) from rfl,
      show BitVec.setWidth 64 (0 : BitVec 32) = (0 : BitVec 64) from rfl]
  · simp only [hf, ite_true] at R2 ⊢
    have e29 : (v.mem.writeW (off (fb s) sAny) (0 : BitVec 64)).readW (off (fb s) sSlen) 64 = stackArg s 3 := by
      rw [R2.rd (d := sSlen) 29 rfl (by decide)]; simp [upd, w29]
    refine WP.mono (WP.keep [.rax, .rdx] (Q := fun w => w.mem = v.mem.writeW (off (fb s) sAny) (0 : BitVec 64) ∧
        w.gpr .rdx = stackArg s 3) ?_ rfl)
      fun w ⟨⟨hm', hdx⟩, k'⟩ => ⟨Lv.of_rep' R1' (hm' ▸ R2) (by simp [upd]) (k'.gpr (by decide)) k'.2.2,
        k', hm' ▸ R2, hdx⟩
    xrun [ea_sp, Lv.rsp, Lv.st (d := sAny) (by decide), Lv.ld (d := sSlen) (by decide),
      show BitVec.setWidth 64 (0 : BitVec 32) = (0 : BitVec 64) from rfl, e29]

/-- `anyArgs`: `sSlen := salt_len` (word 29), `sAny` (28) 0 if a length is
expected and 1 if not, and `rdx` the expected length, 0 if any. -/
theorem anyArgs_ok (hp : VPre s) {u : State} {S : Addr} (L : Lay u (fb s) S) (hrd : u.rd = s.rd)
    (hf : FrV s u.mem) {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep u.mem (fb s) S V W) :
    WP isa anyArgs u fun u' => Lay u' (fb s) S ∧ Keep [.rax, .rdx] u u' ∧
      Rep u'.mem (fb s) S V (upd (upd W 29 (stackArg s 3)) 28 (if vfixed s then 0 else 1)) ∧
      u'.gpr .rdx = if vfixed s then stackArg s 3 else 0 := by
  refine WP.seq (WP.mono (any1_ok hp L hrd hf R) fun v ⟨Lv, hk, R1, hz⟩ => ?_)
  refine WP.ite (M := isa) _ (show isa.eval .e v = _ from hz) (fun hb => ?_) (fun hb => ?_)
  · exact WP.mono (anyBr_ok Lv R1 (by simp [upd]) true hb.symm) fun w ⟨a, k, c, d⟩ =>
      ⟨a, (hk.trans k).mono (by decide), c, d⟩
  · exact WP.mono (anyBr_ok Lv R1 (by simp [upd]) false hb.symm) fun w ⟨a, k, c, d⟩ =>
      ⟨a, (hk.trans k).mono (by decide), c, d⟩

theorem pssLensH_good : Good (Impl.Dispatch.X86_64.chain (pssLens.map fun p =>
    (p.1, .block (Impl.RsaOaep.X86_64.consts p.2)))) := ⟨by decide, by decide, by decide⟩

theorem pssLensG_good : Good (Impl.Dispatch.X86_64.chain (pssLens.map fun p =>
    (p.1, .block [.mov32 .rax (Impl.RsaOaep.X86_64.im p.2), .store (sp Impl.RsaOaep.X86_64.sGD) .rax]))) :=
  ⟨by decide, by decide, by decide⟩

theorem emLen_good : Good emLen := ⟨rfl, rfl, by decide⟩
theorem anyArgs_good : Good anyArgs := ⟨rfl, rfl, by decide⟩

/-- `n₀`, the first byte of `n`. -/
abbrev n0v (s : State) : Nat := (s.mem (s.gpr .rdi)).toNat

/-- `k`. -/
abbrev vk (s : State) : Nat := (s.gpr .rsi).toNat

/-- The expected salt length, 0 if any is accepted. -/
abbrev vsl (s : State) : Nat := if vfixed s then (stackArg s 3).toNat else 0

/-- The slots after the checks: the mask (30), `lo` (31), `salt_len` (29) and
whether any length is accepted (28). -/
def vcW (s : State) : Nat → BitVec 64 :=
  upd (upd (upd (upd (verW s) 30 (maskV (n0v s))) 31 (BitVec.ofNat 64 (loV (n0v s)))) 29 (stackArg s 3)) 28
    (if vfixed s then 0 else 1)

theorem verW_22 : verW s 22 = s.gpr .rdi := by simp [verW, fnW, selW, verPW, upd]
theorem verW_23 : verW s 23 = s.gpr .rsi := by simp [verW, fnW, selW, verPW, upd]
theorem verW_39 : verW s 39 = BitVec.ofNat 64 (lenOf (vselH s)) := by simp [verW, fnW, selW, upd]

/-- 0 returned, from a state in the frame. -/
theorem vfail_ok {t : State} (he : VEnv s t) :
    WP isa verifyFail t fun t' => VEnv s t' ∧ t'.gpr .rax = 0 := by
  refine WP.mono (wp_good (block_good _ rfl rfl) (WP.keep [.rax] (Q := fun t' => t'.mem = t.mem ∧
    t'.gpr .rax = 0) ?_ rfl)) fun t' ⟨⟨⟨_, hax⟩, k⟩, sp', mx', f'⟩ =>
      ⟨he.step k.2.1 k.2.2 sp' (keep_cs3 k (by decide)) mx' f', hax⟩
  xrun [verifyFail, show BitVec.setWidth 64 (0 : BitVec 32) = (0 : BitVec 64) from rfl]

theorem vsl_toNat : (if vfixed s then stackArg s 3 else 0).toNat = vsl s := by
  unfold vsl; split <;> rfl

/-! ## The steps -/

/-- `V₀`: the working space's bytes on entry. -/
abbrev v0 (s : State) : Nat → Byte := fun o => s.mem (off (stackArg s 4) o)

theorem vpro_step (hp : VPre s) : WP isa (.block verifyPrologue) (allocState frameBytes s) (JPV verPW s) :=
  WP.mono (wp_good (block_good _ rfl rfl) (verPro_ok hp)) fun _ ⟨⟨k, L, R, f⟩, _, mx, w⟩ =>
    ⟨k.mono (by decide), L, R, f, mx, w.funs, w.syms⟩

theorem vsel_step (hp : VPre s) {t : State} (h : JPV verPW s t) :
    WP isa (selPrologueWith pssLens 8 9) t (JPV verW s) := by
  obtain ⟨k1, L1, R1, f1, mx1, fu1, sy1⟩ := h
  exact WP.mono (wp_good (selPrologueWith_good pssLensH_good pssLensG_good 8 9)
    (verSel_ok hp k1 L1 R1 f1)) fun t2 ⟨⟨L2, k2, R2, f2⟩, _, mx2, w2⟩ =>
      ⟨(k1.trans k2).mono (by decide), L2, R2, f1.trans f2, mx2.trans mx1, w2.funs.trans fu1, w2.syms.trans sy1⟩

/-- After `n0`. -/
def JN (s t : State) : Prop :=
  VEnv s t ∧ Lay t (fb s) (stackArg s 4) ∧ Rep t.mem (fb s) (stackArg s 4) (v0 s) (verW s) ∧
    t.gpr .rax = BitVec.ofNat 64 (n0v s) ∧ t.zf = some (decide (n0v s = 0))

theorem vn0_step (hp : VPre s) {t : State} (h : JPV verW s t) : WP isa (.block n0) t (JN s) := by
  have hk1 := hp.k1
  have he2 := h.env hp
  obtain ⟨-, L2, R2, f12, -⟩ := h
  have hc : (nR s).Contains (s.gpr .rdi) 1 := by
    have h := Offset.contains_base (s.gpr .rdi) (d := 0) (n := 1) (k := (s.gpr .rsi).toNat) (by omega) (by decide)
    rwa [BitVec.add_zero] at h
  have hn0 : t.mem (s.gpr .rdi) = s.mem (s.gpr .rdi) := f12 _ fun r hr hc' => by
    rw [List.mem_singleton.mp hr] at hc'
    exact (hp.dKn.sub_left (frame_sub s)) _ hc' hc
  have hin : InRegions (t.rd ++ t.wr) (s.gpr .rdi) 1 := by
    rw [he2.rd, hp.hrd]
    exact ⟨nR s, List.mem_append_left _ (by simp [vrd]), hc⟩
  refine WP.mono (wp_good (block_good _ rfl rfl) (n0_ok L2 R2 verW_22 hin))
    fun t3 ⟨⟨k3, hm3, hax3, hz3⟩, sp3, mx3, f3⟩ => ?_
  rw [hn0] at hax3 hz3
  exact ⟨he2.step k3.2.1 k3.2.2 sp3 (keep_cs3 k3 (by decide)) mx3 f3,
    L2.congr (k3.gpr (by decide)) k3.2.2 (by rw [hm3]), hm3 ▸ R2, hax3, hz3⟩

/-- After `emLen`: the mask (30) and `lo` (31), `rax = emLen`, CF set if it
is less than `hLen + 2`. -/
def JE (s t : State) : Prop :=
  VEnv s t ∧ Lay t (fb s) (stackArg s 4) ∧
    Rep t.mem (fb s) (stackArg s 4) (v0 s) (upd (upd (verW s) 30 (maskV (n0v s))) 31
      (BitVec.ofNat 64 (loV (n0v s)))) ∧
    t.gpr .rax = BitVec.ofNat 64 (vk s - loV (n0v s)) ∧
    t.cf = some (decide (vk s - loV (n0v s) < lenOf (vselH s) + 2)) ∧ n0v s ≠ 0

theorem vem_step (hp : VPre s) {t : State} (h : JN s t) (hn0 : n0v s ≠ 0) :
    WP isa (.seq (.block smear) emLen) t (JE s) := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hD64 : lenOf (vselH s) ≤ 64 := pssLensOK.le _ (mem_pssLens hp.iH)
  obtain ⟨he3, L3, R3, hax3, -⟩ := h
  have hx256 : n0v s < 256 := (s.mem (s.gpr .rdi)).isLt
  refine WP.seq (WP.mono (wp_good (block_good _ rfl rfl) (smear_ok t hx256 hn0 hax3))
    fun t4 ⟨⟨k4, hm4, hdx4, hz4⟩, sp4, mx4, f4⟩ => ?_)
  have he4 := he3.step k4.2.1 k4.2.2 sp4 (keep_cs3 k4 (by decide)) mx4 f4
  have L4 : Lay t4 (fb s) (stackArg s 4) := L3.congr (k4.gpr (by decide)) k4.2.2 (by rw [hm4])
  refine WP.mono (wp_good emLen_good (emLen_ok L4 (hm4 ▸ R3) (k := (s.gpr .rsi).toNat) (by rw [verW_23,
      BitVec.ofNat_toNat, BitVec.setWidth_eq]) verW_39 hD64 (by omega) (by omega) hdx4 hz4))
    fun t5 ⟨⟨L5, k5, R5, hax5, hcf5⟩, sp5, mx5, f5⟩ =>
      ⟨he4.step k5.2.1 k5.2.2 sp5 (keep_cs3 k5 (by decide)) mx5 f5, L5, R5, hax5, hcf5, hn0⟩

/-- After `anyArgs`' first block. -/
def JY (s t : State) : Prop :=
  VEnv s t ∧ Lay t (fb s) (stackArg s 4) ∧
    Rep t.mem (fb s) (stackArg s 4) (v0 s) (upd (upd (upd (verW s) 30 (maskV (n0v s))) 31
      (BitVec.ofNat 64 (loV (n0v s)))) 29 (stackArg s 3)) ∧
    t.zf = some (vfixed s) ∧ n0v s ≠ 0 ∧ lenOf (vselH s) + 2 ≤ vk s - loV (n0v s)

theorem vany1_step (hp : VPre s) {t : State} (h : JE s t) (hfit : lenOf (vselH s) + 2 ≤ vk s - loV (n0v s)) :
    WP isa (.block [.mov .rax (.mem (arg 3)), .store (sp sSlen) .rax, .mov32 .rax (.mem (arg 2)),
      .alu .test .rax (.reg .rax)]) t (JY s) := by
  obtain ⟨he5, L5, R5, -, -, hn0⟩ := h
  exact WP.mono (wp_good (block_good _ rfl rfl) (any1_ok hp L5 he5.rd he5.fr R5))
    fun t6 ⟨⟨L6, k6, R6, hz6⟩, sp6, mx6, f6⟩ =>
      ⟨he5.step k6.2.1 k6.2.2 sp6 (keep_cs3 k6 (by decide)) mx6 f6, L6, R6, hz6, hn0, hfit⟩

/-- After `anyArgs`. -/
def JZ (s t : State) : Prop :=
  VEnv s t ∧ Lay t (fb s) (stackArg s 4) ∧ Rep t.mem (fb s) (stackArg s 4) (v0 s) (vcW s) ∧
    t.gpr .rdx = (if vfixed s then stackArg s 3 else 0) ∧ n0v s ≠ 0 ∧
    lenOf (vselH s) + 2 ≤ vk s - loV (n0v s)

theorem vanyBr_step {t : State} (h : JY s t) (b : Bool) (hb : b = vfixed s) :
    WP isa (if b then .block [.mov32 .rax (.imm 0), .store (sp sAny) .rax, .mov .rdx (.mem (sp sSlen))]
      else .block [.mov32 .rax (.imm 1), .store (sp sAny) .rax, .mov32 .rdx (.imm 0)]) t (JZ s) := by
  obtain ⟨he6, L6, R6, -, hn0, hfit⟩ := h
  have hg : Good (if b then (.block [.mov32 .rax (.imm 0), .store (sp sAny) .rax, .mov .rdx (.mem (sp sSlen))] :
      Prog isa) else .block [.mov32 .rax (.imm 1), .store (sp sAny) .rax, .mov32 .rdx (.imm 0)]) := by
    cases b <;> exact block_good _ rfl rfl
  exact WP.mono (wp_good hg (anyBr_ok L6 R6 (by simp [upd]) b hb))
    fun t7 ⟨⟨L7, k7, R7, hdx7⟩, sp7, mx7, f7⟩ =>
      ⟨he6.step k7.2.1 k7.2.2 sp7 (keep_cs3 k7 (by decide)) mx7 f7, L7, R7, hdx7, hn0, hfit⟩

/-- After the salt's check. -/
def JF (s t : State) : Prop :=
  VEnv s t ∧ Lay t (fb s) (stackArg s 4) ∧ Rep t.mem (fb s) (stackArg s 4) (v0 s) (vcW s) ∧
    t.gpr .rax = BitVec.ofNat 64 (vk s - loV (n0v s) - (lenOf (vselH s) + 2)) ∧
    t.cf = some (decide (vk s - loV (n0v s) - (lenOf (vselH s) + 2) < vsl s)) ∧ n0v s ≠ 0 ∧
    lenOf (vselH s) + 2 ≤ vk s - loV (n0v s)

theorem vfit_step (hp : VPre s) {t : State} (h : JZ s t) :
    WP isa (.block (([.mov .rax (.mem (sp sK)), .mov .r8 (.mem (sp sLo)), .alu .sub .rax (.reg .r8)] : List Instr) ++
      saltFits))
      t (JF s) := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hlo := loV_le (n0v s)
  obtain ⟨he6, L6, R6, hdx6, hn0, hfit⟩ := h
  have hW : ∀ k, k ≠ 28 → k ≠ 29 → k ≠ 30 → k ≠ 31 → vcW s k = verW s k := fun k h1 h2 h3 h4 => by
    simp only [vcW, upd, ifn h1, ifn h2, ifn h3, ifn h4]
  have w23 : vcW s 23 = BitVec.ofNat 64 (s.gpr .rsi).toNat := by
    rw [hW 23 (by decide) (by decide) (by decide) (by decide), verW_23, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have w31 : vcW s 31 = BitVec.ofNat 64 (loV (n0v s)) := by simp [vcW, upd]
  have w39 : vcW s 39 = BitVec.ofNat 64 (lenOf (vselH s)) :=
    (hW 39 (by decide) (by decide) (by decide) (by decide)).trans verW_39
  rw [WP.block_append_iff]
  refine WP.mono (wp_good (block_good _ rfl rfl) (WP.keep [.rax, .r8] (Q := fun v => v.mem = t.mem ∧
      v.gpr .rax = BitVec.ofNat 64 ((s.gpr .rsi).toNat - loV (n0v s))) ?_ rfl))
    fun t7 ⟨⟨⟨hm7, hax7⟩, k7⟩, sp7, mx7, f7⟩ => ?_
  · xrun [ea_sp, L6.rsp, L6.ld (d := sK) (by decide), L6.ld (d := sLo) (by decide),
      R6.rd (d := sK) 23 rfl (by decide), R6.rd (d := sLo) 31 rfl (by decide), w23, w31,
      VG.Offset.ofNat_sub_ofNat (show loV (n0v s) ≤ (s.gpr .rsi).toNat by omega)]
  have he7 := he6.step k7.2.1 k7.2.2 sp7 (keep_cs3 k7 (by decide)) mx7 f7
  have L7 : Lay t7 (fb s) (stackArg s 4) := L6.congr (k7.gpr (by decide)) k7.2.2 (by rw [hm7])
  have R7 := hm7 ▸ R6
  refine WP.mono (wp_good (block_good _ rfl rfl) (saltFits_ok L7 R7 w39 (a := (s.gpr .rsi).toNat - loV (n0v s))
      (by unfold vk at hfit; omega) (by omega) hax7 ((k7.gpr (by decide)).trans hdx6)))
    fun t8 ⟨⟨k8, hm8, hax8, hcf8⟩, sp8, mx8, f8⟩ => ?_
  rw [vsl_toNat] at hcf8
  exact ⟨he7.step k8.2.1 k8.2.2 sp8 (keep_cs3 k8 (by decide)) mx8 f8,
    L7.congr (k8.gpr (by decide)) k8.2.2 (by rw [hm8]), hm8 ▸ R7, hax8, hcf8, hn0, hfit⟩

variable (pubN : String) (pubC : Prog isa)

/-- The frame, the prologues and the checks, then `verifyMain` if they pass:
`Q`, if failing them leads to `Q` with 0 returned and `verifyMain` does. -/
theorem verBody_ok (hp : VPre s) {Q : State → Prop}
    (hfail : ∀ t, VEnv s t → t.gpr .rax = 0 →
      ¬ (n0v s ≠ 0 ∧ lenOf (vselH s) + 2 + vsl s ≤ vk s - loV (n0v s)) → Q t)
    (hmain : ∀ t, VEnv s t → Lay t (fb s) (stackArg s 4) →
      Rep t.mem (fb s) (stackArg s 4) (fun o => s.mem (off (stackArg s 4) o)) (vcW s) →
      t.gpr .rax = BitVec.ofNat 64 (vk s - loV (n0v s) - (lenOf (vselH s) + 2)) → n0v s ≠ 0 →
      lenOf (vselH s) + 2 + vsl s ≤ vk s - loV (n0v s) → WP isa (verifyMain pubN pubC) t Q) :
    WP isa (verifyBody pubN pubC) (allocState frameBytes s) Q := by
  unfold verifyBody seqs seqs seqs
  refine WP.seq (WP.mono (vpro_step hp) fun t1 h1 => ?_)
  refine WP.seq (WP.mono (vsel_step hp h1) fun t2 h2 => ?_)
  refine WP.seq (WP.mono (vn0_step hp h2) fun t3 h3 => ?_)
  refine WP.ite (M := isa) _ (show isa.eval .e t3 = _ from h3.2.2.2.2) (fun hb => ?_) (fun hb => ?_)
  · rw [decide_eq_true_eq] at hb
    exact WP.mono (vfail_ok h3.1) fun t' ⟨he', hax⟩ => hfail t' he' hax fun h => h.1 hb
  rw [decide_eq_false_iff_not] at hb
  unfold seqs seqs
  refine VG.Proof.RsaOaep.X86_64.WP.seq_assoc (WP.seq (WP.mono (vem_step hp h3 hb) fun t5 h5 => ?_))
  refine WP.ite (M := isa) _ (show isa.eval .b t5 = _ from h5.2.2.2.2.1) (fun hb' => ?_) (fun hb' => ?_)
  · rw [decide_eq_true_eq] at hb'
    exact WP.mono (vfail_ok h5.1) fun t' ⟨he', hax⟩ => hfail t' he' hax fun h => by unfold vk at h hb'; omega
  rw [decide_eq_false_iff_not] at hb'
  unfold seqs seqs anyArgs
  refine WP.seq (WP.seq (WP.mono (vany1_step hp h5 (by omega)) fun t6 h6 => ?_))
  refine WP.ite (M := isa) _ (show isa.eval .e t6 = _ from h6.2.2.2.1)
    (fun hb => WP.mono (vanyBr_step h6 true hb.symm) fun t7 h7 => ?_)
    (fun hb => WP.mono (vanyBr_step h6 false hb.symm) fun t7 h7 => ?_)
  all_goals
    unfold seqs
    refine WP.seq (WP.mono (vfit_step hp h7) fun t8 h8 => ?_)
    refine WP.ite (M := isa) _ (show isa.eval .b t8 = _ from h8.2.2.2.2.1) (fun hb'' => ?_) (fun hb'' => ?_)
    · rw [decide_eq_true_eq] at hb''
      exact WP.mono (vfail_ok h8.1) fun t' ⟨he', hax⟩ => hfail t' he' hax fun h => by unfold vk at h hb''; omega
    rw [decide_eq_false_iff_not] at hb''
    obtain ⟨he8, L8, R8, hax8, -, hn0, hfit⟩ := h8
    exact hmain t8 he8 L8 R8 hax8 hn0 (by omega)

end VG.Proof.RsaPss.X86_64
