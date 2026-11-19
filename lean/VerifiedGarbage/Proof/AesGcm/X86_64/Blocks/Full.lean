module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.Stitch
import VerifiedGarbage.Proof.AesGcm.X86_64.Run
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Aes.KeyExp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
import VerifiedGarbage.Proof.Framework.X86_64.Straight
import VerifiedGarbage.Proof.Gcm.Split
import VerifiedGarbage.Proof.AesGcm.X86_64.Fn
public import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.Mid
public import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `AesGcm.X86_64.Blocks.Fin`, which the modules that import this one used -/

section

/-! ### `AesGcm.X86_64.Blocks.Tail`, which this module and modules that import it used -/

section

/-!
# AES-GCM on whole blocks, x86-64: the blocks left

Untrusted: everything here is checked by Lean. From `Mid s q q ys`, the
`n - q` blocks left, if any, are encrypted with `vg_aes_ctr32` and hashed
with `vg_ghash` (`encTail_ok`), or hashed and then decrypted (`decTail_ok`),
with the arguments reloaded from `scratch` for each call (`ctrArgs_ok`,
`ghArgs_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Blocks

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Blocks
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Gcm (Block blockAt blocksAt ctxCiph ctxH ctr32 ghashFrom inc32)

/-- A prefix of a region that `rs` covers. -/
theorem covers_prefix {b : Addr} {k L : Nat} {rs : List Region} (h : Covers [⟨b, L⟩] rs) (hk : k ≤ L) :
    Covers [⟨b, k⟩] rs := fun a m ⟨r, hr, hc⟩ => by
  simp only [List.mem_singleton] at hr; subst hr
  exact h a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega_using [hk, hc]⟩

/-- `covers_off` without a bound on the region's length. -/
theorem covers_off' {p : Addr} {k d m : Nat} {rs : List Region} (h : Covers [⟨p, k⟩] rs) (hd : d + m ≤ k)
    (hd' : d < 2 ^ 64) : Covers [⟨p + BitVec.ofNat 64 d, m⟩] rs := by
  intro a j ⟨r, hr, hc⟩
  simp only [List.mem_singleton] at hr; subst hr
  refine h a j ⟨_, List.mem_singleton_self _, ?_⟩
  simp only [Region.Contains] at hc ⊢
  have e : a - p = (a - (p + BitVec.ofNat 64 d)) + BitVec.ofNat 64 d := by
    rw [Offset.sub_add_eq]; exact (BitVec.sub_add_cancel _ _).symm
  rw [e, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) hd']
  have := Nat.mod_le ((a - (p + BitVec.ofNat 64 d)).toNat + d) (2 ^ 64)
  omega_using [hd, hc]

/-- What the calls need of the state: the stack pointer, the permissions, the
arguments kept for what is left after `q` blocks, and `scratch` on the stack. -/
structure Ready (s : State) (q : Nat) (st : State) : Prop where
  rsp : st.gpr .rsp = SP s
  rd : st.rd = s.rd
  wr : st.wr = s.wr
  kept : Kept s q st.mem
  arg : st.mem.readW (SP s + BitVec.ofNat 64 8) 64 = S s

/-- What the calls' working space is. -/
abbrev S5 (s : State) : Addr := S s + BitVec.ofNat 64 64

section
variable {M : CtxMode} {s : State} (hp : BP M s)
include hp

theorem cov_k : Covers [kR M s] (s.rd ++ s.wr) := covers_of_mem (by rw [hp.rd]; simp)
theorem cov_c : Covers [cR s] s.wr := covers_of_mem (by rw [hp.wr]; simp)
theorem cov_y : Covers [yR s] s.wr := covers_of_mem (by rw [hp.wr]; simp)
theorem cov_d : Covers [dR s] s.wr := covers_of_mem (by rw [hp.wr]; simp)
theorem cov_s : Covers [sR s] s.wr := covers_of_mem (by rw [hp.wr]; simp)

omit hp in
/-- The data left after `q` blocks is in the data. -/
theorem dq_sub {q : Nat} (hq : q ≤ n s) : Region.Sub ⟨dq s q, 16 * (n s - q)⟩ (dR s) :=
  Offset.sub_base _ (by omega_using [hq])

omit hp in
theorem s5_sub {k : Nat} (hk : k ≤ 2048) : Region.Sub ⟨S5 s, k⟩ (sR s) := Offset.sub_base _ (by omega_using [hk])

/-- The head of `tail`: `r8` the number of blocks left, `ZF` if none. -/
theorem tailHead_ok {q : Nat} {ys : List Block} {st : State} (h : Mid s q q ys st) :
    WP isa (.block [.mov .r11 (.mem (at_ .rsp 8)), .mov .r8 (.mem (at_ .r11 argN)), .alu .test .r8 (.reg .r8)])
      st fun st' => Mid s q q ys st' ∧ st'.zf = some (decide (n s - q = 0)) := by
  have hn : n s < 2 ^ 64 := (s.gpr .r9).isLt
  have a₀ : InRegions (st.rd ++ st.wr) (st.gpr .rsp + BitVec.ofNat 64 8) 8 := by
    rw [h.rd, h.wr, h.rsp]; exact a_in hp
  have hS : st.mem.readW (st.gpr .rsp + BitVec.ofNat 64 8) 64 = S s := by rw [h.rsp, keep_a hp h.frame]; rfl
  have r₆ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 40) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have hz := and_self_beq (show n s - q < 2 ^ 64 by omega_using [hn])
  apply WP.of_runBlock
  refine ⟨_, by simp only [argN]; xrun [a₀, hS, r₆, h.kept.n], ?_, by simp only [zf_arithFlags, hz]⟩
  exact h.slots hp (fun r h1 h2 h3 => by simp [gpr_setReg, gpr_arithFlags, h1, h2]) h.kept (Frame.refl _ _) rfl rfl

theorem Mid.ready {q k : Nat} {ys : List Block} {st : State} (h : Mid s q k ys st) : Ready s k st :=
  ⟨h.rsp, h.rd, h.wr, h.kept, by rw [keep_a hp h.frame]; rfl⟩

/-- The arguments of `vg_aes_ctr32` on the `n - q` blocks left. -/
theorem ctrArgs_ok {q : Nat} {st : State} (h : Ready s q st) (hq : q < n s) :
    WP isa (.block ctrArgs) st fun st' => CtrCall st' (K s) (C s) (dq s q) (S5 s) (R s) (n s - q) ∧
      Ready s q st' ∧ (∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) ∧ st'.mem = st.mem := by
  have hn : n s < 2 ^ 64 := (s.gpr .r9).isLt
  have hw := hp.w_d
  have a₀ : InRegions (st.rd ++ st.wr) (st.gpr .rsp + BitVec.ofNat 64 8) 8 := by
    rw [h.rd, h.wr, h.rsp]; exact a_in hp
  have hS : st.mem.readW (st.gpr .rsp + BitVec.ofNat 64 8) 64 = S s := by rw [h.rsp, h.arg]
  have r₁ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 0) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have kc0 : st.mem.readW (S s + BitVec.ofNat 64 0) 64 = K s := by simpa using h.kept.ctx
  have r₂ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 8) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have r₃ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 16) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have r₅ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 32) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have r₆ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 40) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have hdq : Region.Sub ⟨dq s q, 16 * (n s - q)⟩ (dR s) := dq_sub (by omega_using [hq])
  have p240 : Region.Sub ⟨K s, 240⟩ (kR M s) := Region.sub_prefix (by have := M.ge; have := M.le; omega_arith)
  have s48 : Region.Sub ⟨S5 s, 2048⟩ (sR s) := s5_sub (by decide)
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [ctrArgs, argCtx, argRounds, argCtr, argData, argN]
    xrun [a₀, hS, r₁, r₂, r₃, r₅, r₆, kc0, h.kept.rounds, h.kept.ctr, h.kept.data, h.kept.n], ?_⟩
  refine ⟨⟨by simp [gpr_setReg], by simp [gpr_setReg, R], by simp [gpr_setReg], by simp [gpr_setReg, dq],
    by simp [gpr_setReg], by simp [gpr_setReg, gpr_arithFlags, S5], hp.rounds, ?_,
    hp.k_c.sub_left p240, (hp.k_d.sub_left p240).sub_right hdq, (hp.k_s.sub_left p240).sub_right s48,
    hp.c_d.sub_right hdq, hp.c_s.sub_right s48, (hp.d_s.sub_left hdq).sub_right s48, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨by simp [gpr_setReg, gpr_arithFlags, h.rsp], h.rd, h.wr, h.kept, h.arg⟩, fun r hr => ?_, rfl⟩
  · simp only [dq, BitVec.toNat_add, BitVec.toNat_ofNat]
    have := Nat.mod_le ((D s).toNat + 16 * q % 2 ^ 64) (2 ^ 64)
    rw [Nat.mod_eq_of_lt (a := 16 * q) (by omega_using [hq, hw])]; omega_using [hw]
  all_goals try simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ↓reduceIte, h.rsp]
  · exact hp.t_k.sub_right p240
  · exact hp.t_c
  · exact hp.t_d.sub_right hdq
  · exact hp.t_s.sub_right s48
  · simp only [rd_setReg, wr_setReg, rd_arithFlags, wr_arithFlags, h.rd, h.wr]
    refine covers_cons (covers_prefix (cov_k hp) (by have := M.ge; have := M.le; omega_arith)) (covers_cons (covers_left (cov_c hp))
      (covers_cons (covers_left (covers_off' (cov_d hp) (by omega_using [hq]) (by omega_using [hq, hw])))
        (covers_left (covers_off (cov_s hp) (by decide) (by decide)))))
  · simp only [wr_setReg, wr_arithFlags, h.wr]
    exact covers_cons (cov_c hp) (covers_cons (covers_off' (cov_d hp) (by omega_using [hq]) (by omega_using [hq, hw]))
      (covers_off (cov_s hp) (by decide) (by decide)))
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags]

/-- The data is not all of memory: the key context is apart from it. -/
theorem n16_lt : n s * 16 < 2 ^ 64 := by
  have hw := hp.w_d
  refine Nat.lt_of_not_le fun hge => hp.k_d (K s) ?_ ?_
  · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; have := M.ge; omega_using [this]
  · simp only [Region.Contains]
    have := (K s - D s).isLt
    omega_using [hge]

/-- The arguments of `vg_ghash` on the `n - q` blocks left. -/
theorem ghArgs_ok {q : Nat} {st : State} (h : Ready s q st) (hq : q < n s) :
    WP isa (.block ghArgs) st fun st' => GhCall st' (K s + BitVec.ofNat 64 240) (Y s) (dq s q) (S5 s) (n s - q) ∧
      Ready s q st' ∧ (∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) ∧ st'.mem = st.mem := by
  have hn : n s < 2 ^ 64 := (s.gpr .r9).isLt
  have hw := hp.w_d
  have h16 := n16_lt hp
  have a₀ : InRegions (st.rd ++ st.wr) (st.gpr .rsp + BitVec.ofNat 64 8) 8 := by
    rw [h.rd, h.wr, h.rsp]; exact a_in hp
  have hS : st.mem.readW (st.gpr .rsp + BitVec.ofNat 64 8) 64 = S s := by rw [h.rsp, h.arg]
  have r₁ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 0) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have kc0 : st.mem.readW (S s + BitVec.ofNat 64 0) 64 = K s := by simpa using h.kept.ctx
  have r₄ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 24) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have r₅ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 32) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have r₆ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 40) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have hdq : Region.Sub ⟨dq s q, 16 * (n s - q)⟩ (dR s) := dq_sub (by omega_using [hq])
  have pH : Region.Sub ⟨K s + BitVec.ofNat 64 240, 16⟩ (kR M s) := Offset.sub_base _ (by have := M.ge; have := M.le; omega_arith)
  have s16 : Region.Sub ⟨S5 s, 256⟩ (sR s) := s5_sub (by decide)
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [ghArgs, argCtx, argY, argData, argN]
    xrun [a₀, hS, r₁, r₄, r₅, r₆, kc0, h.kept.y, h.kept.data, h.kept.n], ?_⟩
  refine ⟨⟨by simp [gpr_setReg, gpr_arithFlags], by simp [gpr_setReg], by simp [gpr_setReg, dq],
    by simp [gpr_setReg], by simp [gpr_setReg, gpr_arithFlags, S5], by omega_using [h16],
    hp.k_y.sub_left pH, (hp.k_s.sub_left pH).sub_right s16, hp.y_d.sub_right hdq, hp.y_s.sub_right s16,
    (hp.d_s.sub_left hdq).sub_right s16, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨by simp [gpr_setReg, gpr_arithFlags, h.rsp], h.rd, h.wr, h.kept, h.arg⟩, fun r hr => ?_, rfl⟩
  all_goals try simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ↓reduceIte, h.rsp]
  · exact hp.t_k.sub_right pH
  · exact hp.t_y
  · exact hp.t_d.sub_right hdq
  · exact hp.t_s.sub_right s16
  · simp only [rd_setReg, wr_setReg, rd_arithFlags, wr_arithFlags, h.rd, h.wr]
    refine covers_cons (covers_off (cov_k hp) (by have := M.ge; have := M.le; omega_arith) (by have := M.ge; have := M.le; omega_using [this]))
      (covers_cons (covers_left (covers_off' (cov_d hp) (by omega_using [hq]) (by omega_using [hq, hw])))
      (covers_cons (covers_left (cov_y hp)) (covers_left (covers_off (cov_s hp) (by decide) (by decide)))))
  · simp only [wr_setReg, wr_arithFlags, h.wr]
    exact covers_cons (cov_y hp) (covers_off (cov_s hp) (by decide) (by decide))
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags]

end

end VG.Proof.AesGcm.X86_64.Blocks

end

end

/-!
# AES-GCM on whole blocks, x86-64: the end

Untrusted: everything here is checked by Lean. From `Mid s q q ys`, `tail`
calls `vg_aes_ctr32` and `vg_ghash` on the blocks left (if any), and
the counter mode and GHASH of the two parts make those of all the blocks
(`ctr32_append`, `ghashFrom_append`): `encTail_ok`, `decTail_ok`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Blocks

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Blocks
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Gcm (Block blockAt blocksAt ctxCiph ctxH ctr32 ghashFrom inc32)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- `scratch` on the stack is apart from the return addresses of calls. -/
theorem arg_below (SP : Addr) : (⟨SP + BitVec.ofNat 64 8, 8⟩ : Region).Disjoint (below SP 8) :=
  Offset.disjoint_below SP (n := 8) (d := 8) (k := 8) (by decide)

/-- A region apart from what a call of `vg_aes_ctr32` or `vg_ghash` on the
blocks left writes. -/
structure Apart (s : State) (q : Nat) (r : Region) : Prop where
  c : r.Disjoint (cR s)
  y : r.Disjoint (yR s)
  d : r.Disjoint ⟨dq s q, 16 * (n s - q)⟩
  s5 : r.Disjoint ⟨S5 s, 2048⟩
  t : r.Disjoint (below (SP s) 8)

/-- The calls of `tail`, for `n - q > 0` blocks left after `Mid`. -/
structure Calls (s : State) (q : Nat) (st st₂ st₃ st₄ st₅ : State) : Prop where
  m₂ : st₂.mem = st.mem
  f₃ : Frame [cR s, (⟨dq s q, 16 * (n s - q)⟩ : Region), ⟨S5 s, 2048⟩, below (SP s) 8] st₂.mem st₃.mem
  m₄ : st₄.mem = st₃.mem
  f₅ : Frame [yR s, (⟨S5 s, 256⟩ : Region), below (SP s) 8] st₄.mem st₅.mem
  saved : ∀ r ∈ calleeSaved, st₅.gpr r = st.gpr r

section
variable {M : CtxMode} {s : State} (hp : BP M s)
include hp

omit hp in
theorem Apart.ctr {q : Nat} {r : Region} (h : Apart s q r) :
    ∀ r' ∈ [cR s, (⟨dq s q, 16 * (n s - q)⟩ : Region), ⟨S5 s, 2048⟩, below (SP s) 8], r.Disjoint r' := by
  intro r' hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  exacts [h.c, h.d, h.s5, h.t]

omit hp in
theorem Apart.gh {q : Nat} {r : Region} (h : Apart s q r) :
    ∀ r' ∈ [yR s, (⟨S5 s, 256⟩ : Region), below (SP s) 8], r.Disjoint r' := by
  intro r' hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [h.y, h.s5.sub_right (Region.sub_prefix (by decide)), h.t]

theorem apart_kR' {q : Nat} (hq : q ≤ n s) : Apart s q (kR' s) where
  c := kR'_disj hp _ (by simp)
  y := kR'_disj hp _ (by simp)
  d := (kR'_disj hp (dR s) (by simp)).sub_right (dq_sub hq)
  s5 := Offset.base_disjoint (S s) (e := 64) (n := 2048) (k := 48) (by decide) (by decide)
  t := (hp.t_s.sub_right kR'_sub).symm

theorem apart_a {q : Nat} (hq : q ≤ n s) : Apart s q (aR s) where
  c := hp.c_a.symm
  y := hp.y_a.symm
  d := hp.d_a.symm.sub_right (dq_sub hq)
  s5 := hp.s_a.symm.sub_right (s5_sub (by decide))
  t := arg_below _

theorem apart_ret {q : Nat} (hq : q ≤ n s) : Apart s q ⟨SP s, 8⟩ where
  c := hp.r_c
  y := hp.r_y
  d := hp.r_d.sub_right (dq_sub hq)
  s5 := hp.r_s.sub_right (s5_sub (by decide))
  t := ret_below _

theorem apart_k {q : Nat} (hq : q ≤ n s) : Apart s q (kR M s) where
  c := hp.k_c
  y := hp.k_y
  d := hp.k_d.sub_right (dq_sub hq)
  s5 := hp.k_s.sub_right (s5_sub (by decide))
  t := hp.t_k.symm

/-- The first `q` blocks are apart from what the calls write. -/
theorem apart_dq {q : Nat} (hq : q ≤ n s) : Apart s q ⟨D s, 16 * q⟩ where
  c := hp.c_d.symm.sub_left (Region.sub_prefix (by omega_using [hq]))
  y := hp.y_d.symm.sub_left (Region.sub_prefix (by omega_using [hq]))
  d := Offset.base_disjoint _ (Nat.le_refl _) (by have := hp.w_d; omega_using [hq, this])
  s5 := (hp.d_s.sub_left (Region.sub_prefix (by omega_using [hq]))).sub_right (s5_sub (by decide))
  t := hp.t_d.symm.sub_left (Region.sub_prefix (by omega_using [hq]))

omit hp in
/-- Ready through a call that writes apart from it. -/
theorem Ready.frame {q : Nat} {st st' : State} (h : Ready s q st) {rs : List Region}
    (hf : Frame rs st.mem st'.mem) (hk : ∀ r ∈ rs, (kR' s).Disjoint r) (ha : ∀ r ∈ rs, (aR s).Disjoint r)
    (hsp : st'.gpr .rsp = st.gpr .rsp) (hrd : st'.rd = st.rd) (hwr : st'.wr = st.wr) : Ready s q st' :=
  ⟨hsp.trans h.rsp, hrd.trans h.rd, hwr.trans h.wr, h.kept.frame hf hk,
    by rw [hf.readW (Region.contains_self _ _) ha (by decide)]; exact h.arg⟩

/-- The key schedule, through a frame apart from the key context. -/
theorem keep_sch {m m' : Mem} {rs : List Region} (hf : Frame rs m m') (hd : ∀ r' ∈ rs, (kR M s).Disjoint r') :
    Spec.Aes.bytesAt m' (K s) (16 * (R s + 1)) = Spec.Aes.bytesAt m (K s) (16 * (R s + 1)) := by
  have hRb : 16 * (R s + 1) ≤ 256 := by rcases hp.rounds with h | h | h <;> simp only [R, h] <;> decide
  exact bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix (Nat.le_trans hRb M.ge))) (by have := hp.w_k; omega_using [hRb])

theorem wR_k : ∀ r ∈ wR s, (kR M s).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  exacts [hp.k_c, hp.k_y, hp.k_d, hp.k_s]

omit hp in
theorem length_blocksAt (m : Mem) (p : Addr) (k : Nat) : (blocksAt m p k).length = k := by simp [blocksAt]

omit hp in
/-- The blocks at `D` split after `q`. -/
theorem blocksAt_split (m : Mem) {q : Nat} (hq : q ≤ n s) :
    blocksAt m (D s) (n s) = blocksAt m (D s) q ++ blocksAt m (dq s q) (n s - q) := by
  rw [← Proof.Gcm.blocksAt_add, Nat.add_sub_cancel' hq]

/-- What the function returns with, when encrypting. -/
def EncDone (s s' : State) : Prop := gprPreserved s s' ∧ Proof.AesGcm.encryptBlocksX86_64.post s s'

/-- What the function returns with, when decrypting. -/
def DecDone (s s' : State) : Prop := gprPreserved s s' ∧ Proof.AesGcm.decryptBlocksX86_64.post s s'

/-- `tail` from `Mid s q q ys`: its calls, if any blocks are left. -/
theorem tail_calls (first second : Prog isa) {q : Nat} {ys : List Block} {st : State} (h : Mid s q q ys st)
    {Q : State → Prop} (h0 : ∀ st₁, Mid s q q ys st₁ → n s - q = 0 → Q st₁)
    (hc : ∀ st₁, Mid s q q ys st₁ → q < n s → WP isa (.seq first second) st₁ Q) :
    WP isa (tail first second) st Q := by
  refine WP.seq (WP.mono (tailHead_ok hp h) fun st₁ ⟨M, hz⟩ => ?_)
  refine WP.ite (decide (n s - q = 0)) (by simp only [eval, hz]) (fun e => ?_) (fun e => ?_)
  · simp only [decide_eq_true_eq] at e
    exact WP.block_nil (h0 st₁ M e)
  · exact hc st₁ M (by simp at e; omega_using [e])

/-- The data left is apart from what `vg_ghash` writes. -/
theorem dq_gh {q : Nat} (hq : q ≤ n s) :
    ∀ r ∈ [yR s, (⟨S5 s, 256⟩ : Region), below (SP s) 8], (⟨dq s q, 16 * (n s - q)⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.y_d.symm.sub_left (dq_sub hq)
  · exact (hp.d_s.sub_left (dq_sub hq)).sub_right (s5_sub (by decide))
  · exact hp.t_d.symm.sub_left (dq_sub hq)

/-- `Y` is apart from what `vg_aes_ctr32` writes. -/
theorem y_ctr {q : Nat} (hq : q ≤ n s) :
    ∀ r ∈ [cR s, (⟨dq s q, 16 * (n s - q)⟩ : Region), ⟨S5 s, 2048⟩, below (SP s) 8], (yR s).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.c_y.symm
  · exact hp.y_d.sub_right (dq_sub hq)
  · exact hp.y_s.sub_right (s5_sub (by decide))
  · exact hp.t_y.symm

/-- The counter is apart from what `vg_ghash` writes. -/
theorem c_gh : ∀ r ∈ [yR s, (⟨S5 s, 256⟩ : Region), below (SP s) 8], (cR s).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.c_y
  · exact hp.c_s.sub_right (s5_sub (by decide))
  · exact hp.t_c.symm

omit hp in
/-- The hash subkey is in the key context. -/
theorem h_sub : Region.Sub ⟨K s + BitVec.ofNat 64 240, 16⟩ (kR M s) := Offset.sub_base _ (by have := M.ge; omega_using [this])

/-- The encryption of the blocks left, from `Mid`. -/
theorem encCalls_ok (v : GcmImpl) {q : Nat} {st₁ : State}
    (M : Mid s q q (ctr32 (ciph s) (cb s) (blocksAt s.mem (D s) q)) st₁) (hlt : q < n s) :
    WP isa (.seq (ctrCall v.callees.ctr) (ghCall v.callees.gh)) st₁ (EncDone s) := by
  have hq := M.q_le
  have hw := hp.w_d
  have h16 := n16_lt hp
  refine WP.seq (WP.seq (WP.mono (ctrArgs_ok hp (M.ready hp) hlt) fun st₂ ⟨hc, R₂, sv₂, m₂⟩ =>
    WP.mono (ctr_call v.ctr hc) fun st₃ g => ?_))
  have f₃ := g.frame
  rw [R₂.rsp] at f₃
  have R₃ : Ready s q st₃ := R₂.frame f₃ (fun r hr => (apart_kR' hp hq).ctr r hr)
    (fun r hr => (apart_a hp hq).ctr r hr) (g.saved _ (by decide)) g.rd g.wr
  refine WP.seq (WP.mono (ghArgs_ok hp R₃ hlt) fun st₄ ⟨hg, R₄, sv₄, m₄⟩ =>
    WP.mono (gh_call v.gh hg) fun st₅ g' => ?_)
  have f₅ := g'.frame
  rw [R₄.rsp] at f₅
  have c : Calls s q st₁ st₂ st₃ st₄ st₅ := ⟨m₂, f₃, m₄, f₅, fun r hr => by
    rw [g'.saved r hr, sv₄ r hr, g.saved r hr, sv₂ r hr]⟩
  -- What the calls compute.
  have hK : Spec.Aes.bytesAt st₂.mem (K s) (16 * (R s + 1)) = Spec.Aes.bytesAt s.mem (K s) (16 * (R s + 1)) := by
    rw [m₂]; exact keep_sch hp M.frame (wR_k hp)
  have hC₂ : blockAt st₂.mem (C s) = Nat.repeat inc32 q (cb s) := by rw [m₂]; exact M.ctr
  have hD₂ : blocksAt st₂.mem (dq s q) (n s - q) = blocksAt s.mem (dq s q) (n s - q) := by rw [m₂]; exact M.rest
  have out₃ := g.out
  rw [hK, hC₂, hD₂] at out₃
  have hx : blocksAt st₄.mem (dq s q) (n s - q) =
      ctr32 (ciph s) (Nat.repeat inc32 q (cb s)) (blocksAt s.mem (dq s q) (n s - q)) := by rw [m₄]; exact out₃
  have hH : blockAt st₄.mem (K s + BitVec.ofNat 64 240) = hk s := by
    rw [m₄, blockAt_frame f₃ fun r hr => ((apart_k hp hq).ctr r hr).sub_left (h_sub (s := s)), m₂,
      blockAt_frame M.frame fun r hr => (wR_k hp r hr).sub_left (h_sub (s := s))]; rfl
  have hY : blockAt st₄.mem (Y s) = ghashFrom (hk s) (y₀ s) (ctr32 (ciph s) (cb s) (blocksAt s.mem (D s) q)) := by
    rw [m₄, blockAt_frame f₃ (y_ctr hp hq), m₂]; exact M.y
  have hfirst : blocksAt st₅.mem (D s) q = ctr32 (ciph s) (cb s) (blocksAt s.mem (D s) q) := by
    rw [← M.data]
    exact blocksAt_frame f₅ (fun r hr => ((apart_dq hp hq).gh r hr)) (by omega_using [hlt, hw]) |>.trans (by
      rw [m₄]; exact (blocksAt_frame f₃ (fun r hr => ((apart_dq hp hq).ctr r hr)) (by omega_using [hlt, hw])).trans (by rw [m₂]))
  have hsecond : blocksAt st₅.mem (dq s q) (n s - q) =
      ctr32 (ciph s) (Nat.repeat inc32 q (cb s)) (blocksAt s.mem (dq s q) (n s - q)) := by
    rw [blocksAt_frame f₅ (dq_gh hp hq) (by omega_using [hw]), hx]
  have hall : ctr32 (ciph s) (cb s) (blocksAt s.mem (D s) (n s)) =
      ctr32 (ciph s) (cb s) (blocksAt s.mem (D s) q) ++
        ctr32 (ciph s) (Nat.repeat inc32 q (cb s)) (blocksAt s.mem (dq s q) (n s - q)) := by
    rw [blocksAt_split s.mem hq, Proof.Gcm.ctr32_append, length_blocksAt]
  refine ⟨⟨fun r hr => by rw [c.saved r hr, M.saved r hr], ?_⟩, ?_, ?_, ?_⟩
  · show st₅.mem.readW (SP s) 64 = s.mem.readW (SP s) 64
    rw [f₅.readW (Region.contains_self _ _) ((apart_ret hp hq).gh) (by decide), m₄,
      f₃.readW (Region.contains_self _ _) ((apart_ret hp hq).ctr) (by decide), m₂, keep_r hp M.frame]
  · show blocksAt st₅.mem (D s) (n s) = ctr32 (ciph s) (cb s) (blocksAt s.mem (D s) (n s))
    rw [blocksAt_split st₅.mem hq, hfirst, hsecond, hall]
  · show blockAt st₅.mem (C s) = Nat.repeat inc32 (n s) (cb s)
    rw [blockAt_frame f₅ (c_gh hp), m₄, g.ctr, hC₂, ← Proof.Gcm.repeat_add, Nat.sub_add_cancel hq]
  · show blockAt st₅.mem (Y s) = ghashFrom (hk s) (y₀ s) (ctr32 (ciph s) (cb s) (blocksAt s.mem (D s) (n s)))
    rw [g'.out, hH, hY, hx, ← Proof.Gcm.ghashFrom_append, hall]

/-- The decryption of the blocks left, from `Mid`: hashed, then decrypted. -/
theorem decCalls_ok (v : GcmImpl) {q : Nat} {st₁ : State}
    (M : Mid s q q (blocksAt s.mem (D s) q) st₁) (hlt : q < n s) :
    WP isa (.seq (ghCall v.callees.gh) (ctrCall v.callees.ctr)) st₁ (DecDone s) := by
  have hq := M.q_le
  have hw := hp.w_d
  have h16 := n16_lt hp
  refine WP.seq (WP.seq (WP.mono (ghArgs_ok hp (M.ready hp) hlt) fun st₂ ⟨hg, R₂, sv₂, m₂⟩ =>
    WP.mono (gh_call v.gh hg) fun st₃ g => ?_))
  have f₃ := g.frame
  rw [R₂.rsp] at f₃
  have R₃ : Ready s q st₃ := R₂.frame f₃ (fun r hr => (apart_kR' hp hq).gh r hr)
    (fun r hr => (apart_a hp hq).gh r hr) (g.saved _ (by decide)) g.rd g.wr
  refine WP.seq (WP.mono (ctrArgs_ok hp R₃ hlt) fun st₄ ⟨hc, R₄, sv₄, m₄⟩ =>
    WP.mono (ctr_call v.ctr hc) fun st₅ g' => ?_)
  have f₅ := g'.frame
  rw [R₄.rsp] at f₅
  have hP₂ : blocksAt st₂.mem (dq s q) (n s - q) = blocksAt s.mem (dq s q) (n s - q) := by rw [m₂]; exact M.rest
  have hH : blockAt st₂.mem (K s + BitVec.ofNat 64 240) = hk s := by
    rw [m₂, blockAt_frame M.frame fun r hr => (wR_k hp r hr).sub_left (h_sub (s := s))]; rfl
  have hY₂ : blockAt st₂.mem (Y s) = ghashFrom (hk s) (y₀ s) (blocksAt s.mem (D s) q) := by rw [m₂]; exact M.y
  have hK : Spec.Aes.bytesAt st₄.mem (K s) (16 * (R s + 1)) = Spec.Aes.bytesAt s.mem (K s) (16 * (R s + 1)) := by
    rw [m₄, keep_sch hp f₃ (fun r hr => (apart_k hp hq).gh r hr), m₂]; exact keep_sch hp M.frame (wR_k hp)
  have hC₄ : blockAt st₄.mem (C s) = Nat.repeat inc32 q (cb s) := by
    rw [m₄, blockAt_frame f₃ (c_gh hp), m₂]; exact M.ctr
  have hD₄ : blocksAt st₄.mem (dq s q) (n s - q) = blocksAt s.mem (dq s q) (n s - q) := by
    rw [m₄, blocksAt_frame f₃ (dq_gh hp hq) (by omega_using [hw])]; exact hP₂
  have out₅ := g'.out
  rw [hK, hC₄, hD₄] at out₅
  have hfirst : blocksAt st₅.mem (D s) q = ctr32 (ciph s) (cb s) (blocksAt s.mem (D s) q) := by
    rw [← M.data, blocksAt_frame f₅ (fun r hr => ((apart_dq hp hq).ctr r hr)) (by omega_using [hlt, hw]), m₄,
      blocksAt_frame f₃ (fun r hr => ((apart_dq hp hq).gh r hr)) (by omega_using [hlt, hw]), m₂]
  refine ⟨⟨fun r hr => by rw [g'.saved r hr, sv₄ r hr, g.saved r hr, sv₂ r hr, M.saved r hr], ?_⟩, ?_, ?_, ?_⟩
  · show st₅.mem.readW (SP s) 64 = s.mem.readW (SP s) 64
    rw [f₅.readW (Region.contains_self _ _) ((apart_ret hp hq).ctr) (by decide), m₄,
      f₃.readW (Region.contains_self _ _) ((apart_ret hp hq).gh) (by decide), m₂, keep_r hp M.frame]
  · show blocksAt st₅.mem (D s) (n s) = ctr32 (ciph s) (cb s) (blocksAt s.mem (D s) (n s))
    rw [blocksAt_split st₅.mem hq, hfirst, out₅, blocksAt_split s.mem hq, Proof.Gcm.ctr32_append, length_blocksAt]; rfl
  · show blockAt st₅.mem (C s) = Nat.repeat inc32 (n s) (cb s)
    rw [g'.ctr, hC₄, ← Proof.Gcm.repeat_add, Nat.sub_add_cancel hq]
  · show blockAt st₅.mem (Y s) = ghashFrom (hk s) (y₀ s) (blocksAt s.mem (D s) (n s))
    rw [blockAt_frame f₅ (y_ctr hp hq), m₄, g.out, hH, hY₂, hP₂, ← Proof.Gcm.ghashFrom_append,
      ← blocksAt_split s.mem hq]

end

end VG.Proof.AesGcm.X86_64.Blocks

end

end

/-!
# AES-GCM on whole blocks, x86-64: loops that take all the blocks

Untrusted: everything here is checked by Lean. With a `piece` that also
takes the blocks after the last 16 (`full`), `Blocks.fullBody` gives at least
16 blocks all to it, after which nothing is left (`fullBody_ok`), and fewer
to `rest` and the calls, as without `full`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Blocks

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Blocks
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Gcm (Block blockAt blocksAt ctxCiph ctxH ctr32 ghashFrom inc32)

section
variable {aligned : Bool} {M : CtxMode} {s : State} (hp : BP M s)
include hp

omit hp in
/-- `r11` at the working space. -/
theorem scratch_ok (s₁ : State) :
    WP isa (.block (Blocks.scratchSetup aligned)) s₁ fun s₃ =>
      s₃.gpr .r11 = AlignedScratch.ptr aligned (s₁.gpr .r11) ∧ (∀ r, r ≠ .r11 → s₃.gpr r = s₁.gpr r) ∧
      s₃.mem = s₁.mem ∧ s₃.rd = s₁.rd ∧ s₃.wr = s₁.wr := by
  cases aligned <;> apply WP.of_runBlock
  all_goals refine ⟨_, by xrun [Blocks.scratchSetup], ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (intro r a; simp [gpr_setReg, gpr_arithFlags, a])
    | simp [AlignedScratch.ptr, gpr_setReg, gpr_arithFlags, mem_arithFlags, mem_setReg,
        rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]

/-- With `full`: at least 16 blocks all by `piece` (or, if `small`, at least
`smallMin small4` by `pieceS.getD piece`, but for a multiple of 4
with `skip4 small4 dec`), which leaves `Done` (`hpost`), or fewer by `rest` and
the calls (`hsmall`). -/
theorem fullBody_ok {small small4 dec : Bool} {piece first second : Prog isa} {pieceS : Option (Prog isa)}
    {Post : State → State → Prop} {Done : State → Prop}
    (hpiece : ∀ s₃, Gcm.X86_64.Stitch.SPreM M s₃ → WP isa piece s₃ (Post s₃))
    (hpieceS : ∀ s₃, Gcm.X86_64.Stitch.SPreM M s₃ (if small then 1 else 16) → Gcm.X86_64.Stitch.nb s₃ < 16 →
      WP isa (pieceS.getD piece) s₃ (Post s₃))
    (hpost : ∀ s₃ s₄, s₃.gpr .r9 = BitVec.ofNat 64 (n s) → (∀ r ∈ argRegs, s₃.gpr r = s.gpr r) →
      (∀ r ∈ calleeSaved, s₃.gpr r = s.gpr r) →
      s₃.gpr .r11 = S s + BitVec.ofNat 64 (AlignedScratch.offset aligned (S s)) → s₃.rd = s.rd →
      s₃.wr = s.wr → Kept s 0 s₃.mem → Frame [kR' s] s.mem s₃.mem → Post s₃ s₄ → Done s₄)
    (hsmall : n s < 16 → ∀ st, Mid s 0 0 [] st → WP isa (.seq (.block rest) (tail first second)) st Done)
    {s₁ : State} (h11 : s₁.gpr .r11 = S s) (hg : ∀ r, r ≠ .r11 → s₁.gpr r = s.gpr r) (hk : Kept s 0 s₁.mem)
    (hf : Frame [kR' s] s.mem s₁.mem) (hrd : s₁.rd = s.rd) (hwr : s₁.wr = s.wr) :
    WP isa (fullBody piece first second aligned small small4 pieceS dec) s₁ Done := by
  have hmin : 1 ≤ smallMin small4 := by cases small4 <;> decide
  -- The piece, from a state with `s₁`'s registers and memory.
  have pc : ∀ (p : Prog isa) (lo : Nat),
      (∀ s₃, Gcm.X86_64.Stitch.SPreM M s₃ lo → Gcm.X86_64.Stitch.nb s₃ = n s → WP isa p s₃ (Post s₃)) →
      lo ≤ n s → ∀ s₂ : State, s₂.gpr = s₁.gpr → s₂.mem = s₁.mem →
      s₂.rd = s₁.rd → s₂.wr = s₁.wr → WP isa (stitchPart p aligned true) s₂ Done := by
    intro p lo hpiece hlo s₂ g₂ m₂ rd₂ wr₂
    refine WP.seq (WP.mono (scratch_ok (aligned := aligned) s₂) fun s₄ ⟨h11₄, g₄, m₄, rd₄, wr₄⟩ => ?_)
    have keepR : ∀ r, r ≠ .r11 → s₄.gpr r = s.gpr r := fun r c => by rw [g₄ r c, g₂, hg r c]
    have ga : ∀ r ∈ argRegs, s₄.gpr r = s.gpr r := fun r hr => by
      simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact keepR _ (by decide)
    have gc : ∀ r ∈ calleeSaved, s₄.gpr r = s.gpr r := fun r hr => by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact keepR _ (by decide)
    have g11 : s₄.gpr .r11 = S s + BitVec.ofNat 64 (AlignedScratch.offset aligned (S s)) := by
      rw [h11₄, g₂, h11]; exact AlignedScratch.ptr_eq aligned (S s) hp.w_s
    have h9 : s₄.gpr .r9 = BitVec.ofNat 64 (n s) := by
      rw [keepR _ (by decide)]; exact (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _)|>.symm
    have rd₄' : s₄.rd = s.rd := by rw [rd₄, rd₂, hrd]
    have wr₄' : s₄.wr = s.wr := by rw [wr₄, wr₂, hwr]
    have hk₄ : Kept s 0 s₄.mem := by rw [m₄, m₂]; exact hk
    have hf₄ : Frame [kR' s] s.mem s₄.mem := by rw [m₄, m₂]; exact hf
    have hn9 : Gcm.X86_64.Stitch.nb s₄ = n s := by
      show (s₄.gpr .r9).toNat = _
      rw [h9]; exact toNat_ofNat_of_lt (s.gpr .r9).isLt
    exact WP.mono (hpiece s₄ (spreM_of hp hlo (Nat.le_refl _) h9 ga g11 rd₄' wr₄' hf₄) hn9) fun s₅ hP =>
      hpost s₄ s₅ h9 ga gc g11 rd₄' wr₄' hk₄ hf₄ hP
  -- The calls, from a state with `s₁`'s registers and memory.
  have cl : n s < 16 → ∀ s₂ : State, s₂.gpr = s₁.gpr → s₂.mem = s₁.mem → s₂.rd = s₁.rd → s₂.wr = s₁.wr →
      WP isa (.seq (.block rest) (tail first second)) s₂ Done := fun hlt s₂ g₂ m₂ rd₂ wr₂ =>
    hsmall hlt _ (mid_entry hp (fun r hr => by rw [g₂]; exact hg r hr) (by rw [m₂]; exact hk)
      (by rw [m₂]; exact hf) (rd₂.trans hrd) (wr₂.trans hwr))
  refine WP.seq (WP.mono (cmp16_ok (hg _ (by decide))) fun s₂ ⟨g₂, m₂, rd₂, wr₂, cf₂⟩ => ?_)
  refine WP.ite (decide (n s < 16)) (by simp only [eval, cf₂]) (fun h => ?_) (fun h => ?_)
  · have hlt : n s < 16 := by simpa using h
    cases small with
    | false => exact cl hlt s₂ g₂ m₂ rd₂ wr₂
    | true =>
      refine WP.seq (WP.mono (cmpMin_ok (s := s) small4 (by rw [g₂]; exact hg _ (by decide)))
        fun s₃ ⟨g₃, m₃, rd₃, wr₃, cf₃⟩ => ?_)
      refine WP.ite (decide (n s < smallMin small4)) (by simp only [eval, cf₃]) (fun h0 => ?_) (fun h0 => ?_)
      · exact cl hlt s₃ (g₃.trans g₂) (m₃.trans m₂) (rd₃.trans rd₂) (wr₃.trans wr₂)
      · have hS := pc _ _ (fun s₃ h3 hn => hpieceS s₃ h3 (hn ▸ hlt)) (by simp at h0 ⊢; omega_using [hmin, h0])
        cases hsk : skip4 small4 dec <;> simp only [smallPart, hsk, Bool.false_eq_true, ↓reduceIte]
        · exact hS s₃ (g₃.trans g₂) (m₃.trans m₂) (rd₃.trans rd₂) (wr₃.trans wr₂)
        · refine WP.seq (WP.mono (test3_ok (s := s) (by rw [g₃, g₂]; exact hg _ (by decide)))
            fun s₄ ⟨g₄, m₄, rd₄, wr₄, zf₄⟩ => ?_)
          refine WP.ite (decide (n s % 4 = 0)) (by simp only [eval, zf₄]) (fun _ => ?_) (fun _ => ?_)
          · exact cl hlt s₄ (g₄.trans (g₃.trans g₂)) (m₄.trans (m₃.trans m₂)) (rd₄.trans (rd₃.trans rd₂))
              (wr₄.trans (wr₃.trans wr₂))
          · exact hS s₄ (g₄.trans (g₃.trans g₂)) (m₄.trans (m₃.trans m₂)) (rd₄.trans (rd₃.trans rd₂))
              (wr₄.trans (wr₃.trans wr₂))
  · exact pc _ _ (fun s₃ h3 _ => hpiece s₃ h3) (by simp at h; omega_using [h]) s₂ g₂ m₂ rd₂ wr₂

/-- After a loop that encrypts all the blocks: the blocks hashed are those
written. -/
theorem stitchEFull_ok {s₃ s₄ : State} (h9 : s₃.gpr .r9 = BitVec.ofNat 64 (n s)) (ga : ∀ r ∈ argRegs, s₃.gpr r = s.gpr r)
    (gc : ∀ r ∈ calleeSaved, s₃.gpr r = s.gpr r)
    (g11 : s₃.gpr .r11 = S s + BitVec.ofNat 64 (AlignedScratch.offset aligned (S s))) (rd₃ : s₃.rd = s.rd)
    (wr₃ : s₃.wr = s.wr) (hk₃ : Kept s 0 s₃.mem) (hf₃ : Frame [kR' s] s.mem s₃.mem)
    (hP : Gcm.X86_64.Stitch.EPost s₃ s₄) :
    Mid s (n s) 0 (ctr32 (ciph s) (cb s) (blocksAt s.mem (D s) (n s))) s₄ := by
  refine mid_of_post hp (Nat.le_refl _) h9 ga gc g11 rd₃ wr₃ hk₃ hf₃ hP.data hP.ctr hP.frame hP.gpr hP.rd hP.wr
    fun eH eY _ eD => ?_
  have hn : n s < 2 ^ 64 := (s.gpr .r9).isLt
  have hy := hP.y
  simp only [Gcm.X86_64.Stitch.yp, Gcm.X86_64.Stitch.hk, Gcm.X86_64.Stitch.y₀, Gcm.X86_64.Stitch.kp,
    Gcm.X86_64.Stitch.dp, Gcm.X86_64.Stitch.nb, h9, ga _ (by simp [argRegs] : Reg.rcx ∈ argRegs),
    ga _ (by simp [argRegs] : Reg.rdi ∈ argRegs), ga _ (by simp [argRegs] : Reg.r8 ∈ argRegs),
    toNat_ofNat_of_lt hn] at hy
  rw [hy, eH, eY, eD]

/-- After a loop that decrypts all the blocks: those hashed are those read. -/
theorem stitchDFull_ok {s₃ s₄ : State} (h9 : s₃.gpr .r9 = BitVec.ofNat 64 (n s)) (ga : ∀ r ∈ argRegs, s₃.gpr r = s.gpr r)
    (gc : ∀ r ∈ calleeSaved, s₃.gpr r = s.gpr r)
    (g11 : s₃.gpr .r11 = S s + BitVec.ofNat 64 (AlignedScratch.offset aligned (S s))) (rd₃ : s₃.rd = s.rd)
    (wr₃ : s₃.wr = s.wr) (hk₃ : Kept s 0 s₃.mem) (hf₃ : Frame [kR' s] s.mem s₃.mem)
    (hP : Gcm.X86_64.Stitch.DPost s₃ s₄) :
    Mid s (n s) 0 (blocksAt s.mem (D s) (n s)) s₄ := by
  refine mid_of_post hp (Nat.le_refl _) h9 ga gc g11 rd₃ wr₃ hk₃ hf₃ hP.data hP.ctr hP.frame hP.gpr hP.rd hP.wr
    fun eH eY eD _ => ?_
  have hn : n s < 2 ^ 64 := (s.gpr .r9).isLt
  have hy := hP.y
  simp only [Gcm.X86_64.Stitch.yp, Gcm.X86_64.Stitch.hk, Gcm.X86_64.Stitch.y₀, Gcm.X86_64.Stitch.kp,
    Gcm.X86_64.Stitch.dp, Gcm.X86_64.Stitch.nb, h9, ga _ (by simp [argRegs] : Reg.rcx ∈ argRegs),
    ga _ (by simp [argRegs] : Reg.rdi ∈ argRegs), ga _ (by simp [argRegs] : Reg.r8 ∈ argRegs),
    toNat_ofNat_of_lt hn] at hy
  rw [hy, eH, eY, eD]

end

end VG.Proof.AesGcm.X86_64.Blocks
