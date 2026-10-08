import VerifiedGarbage.Proof.Ecdh.AArch64.Validate
import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64
import VerifiedGarbage.Proof.Framework.AArch64.Syms

/-!
# ECDSA verification on AArch64: the arguments and the key

`front_ok`: `args`, the signature's setup and table (`stage₁`, whose
`SetupPre` the arguments meet), the load of `s` (`loadS_ok`) and ECDH's
checks of the key (`peer_ok`, `validate_ok`) leave `r`, the hash and `s` in
their slots, `R = O`, the flag of the
key's validity as the code checks it (`KeyOk`), and the key's point, or `G`
if it is not valid, for ECDH's window method (`Front`).
-/

namespace VG.Proof.Ecdsa.Verify.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x)
open VG.Impl.Ecdh.AArch64 (QY R2P BP QXM QYM W0 W1 W2 W3 PX PY)

variable {c : Cfg}

/-- The arguments: `public = x0` (`1 + 2 len` bytes), `digest = x1`
(`len` bytes), `sig = x2` (`2 len` bytes) and `scratch = x3`, and the comb's
tables at the static `c.tsym` (`Artifact.consts`), readable and writable as
the contract says and apart from `scratch`. -/
structure VPre (c : Cfg) (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .x0, 1 + 2 * c.C.len⟩, ⟨s.gpr .x1, c.C.len⟩, ⟨s.gpr .x2, 2 * c.C.len⟩,
    ⟨s.syms c.tsym, 8 * c.combWords.length⟩]
  wr : s.wr = [⟨s.gpr .x3, size⟩]
  pk_sc : Region.Disjoint ⟨s.gpr .x0, 1 + 2 * c.C.len⟩ ⟨s.gpr .x3, size⟩
  dg_sc : Region.Disjoint ⟨s.gpr .x1, c.C.len⟩ ⟨s.gpr .x3, size⟩
  sig_sc : Region.Disjoint ⟨s.gpr .x2, 2 * c.C.len⟩ ⟨s.gpr .x3, size⟩
  sc_fit : (s.gpr .x3).toNat + size ≤ 2 ^ 64
  tbl : TblPre c s (s.syms c.tsym) (s.gpr .x3)

/-- The verification frontend only needs the argument regions; the point
multiplier decides whether constant tables are required. -/
structure FrontPre (c : Cfg) (s : State) : Prop where
  rd : ∃ extra, s.rd = [⟨s.gpr .x0, 1 + 2 * c.C.len⟩,
    ⟨s.gpr .x1, c.C.len⟩, ⟨s.gpr .x2, 2 * c.C.len⟩] ++ extra
  wr : s.wr = [⟨s.gpr .x3, size⟩]
  pk_sc : Region.Disjoint ⟨s.gpr .x0, 1 + 2 * c.C.len⟩ ⟨s.gpr .x3, size⟩
  dg_sc : Region.Disjoint ⟨s.gpr .x1, c.C.len⟩ ⟨s.gpr .x3, size⟩
  sig_sc : Region.Disjoint ⟨s.gpr .x2, 2 * c.C.len⟩ ⟨s.gpr .x3, size⟩
  sc_fit : (s.gpr .x3).toNat + size ≤ 2 ^ 64

instance {c : Cfg} {s : State} : Coe (VPre c s) (FrontPre c s) :=
  ⟨fun h => ⟨⟨[⟨s.syms c.tsym, 8 * c.combWords.length⟩], h.rd⟩,
    h.wr, h.pk_sc, h.dg_sc, h.sig_sc, h.sc_fit⟩⟩

/-- The key's `x` and `y`, the hash, and the signature's `r` and `s`. -/
abbrev keyX (c : Cfg) (s₀ : State) : Nat :=
  ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x0 + BitVec.ofNat 64 1) c.C.len)
abbrev keyY (c : Cfg) (s₀ : State) : Nat :=
  ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x0 + BitVec.ofNat 64 (1 + c.C.len)) c.C.len)
abbrev dig (c : Cfg) (s₀ : State) : Nat := ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x1) c.C.len)
abbrev sigR (c : Cfg) (s₀ : State) : Nat := ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x2) c.C.len)
abbrev sigS (c : Cfg) (s₀ : State) : Nat :=
  ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x2 + BitVec.ofNat 64 c.C.len) c.C.len)

/-- The key is valid as the code checks it. -/
abbrev KeyOk (c : Cfg) (s₀ : State) : Prop :=
  ((s₀.mem (s₀.gpr .x0) = 4 ∧ keyX c s₀ < c.C.p) ∧ keyY c s₀ < c.C.p) ∧
    OnCurve c (Fin.ofNat c.C.p (keyX c s₀)) (Fin.ofNat c.C.p (keyY c s₀))

/-- After the key's checks, from the state `s₀` at entry, with the working
space at `base` and the callee-saved registers `g`. -/
structure Front (c : Cfg) (s₀ : State) (base : Addr) (g : Reg → BitVec 64) (s : State) : Prop where
  scr : Scr s base size
  wr : s.wr = s₀.wr
  rd : s.rd = s₀.rd
  fixed : Fixed c base g s.mem
  k : sv c base s K = sigR c s₀
  d : sv c base s D = dig c s₀ >>> c.sh
  pt : sv c base s PT = sigS c s₀
  rx : sv c base s RX = 0
  ry : sv c base s RY = c.mont 1
  rz : sv c base s RZ = 0
  flag : word s.mem base (c.sl FLAG) = mask (KeyOk c s₀)
  px_lt : sv c base s PX < c.C.p
  py_lt : sv c base s PY < c.C.p
  px : toM c.C.p (2 ^ (64 * c.n)) (sv c base s PX) =
    if KeyOk c s₀ then Fin.ofNat c.C.p (keyX c s₀) else Fin.ofNat c.C.p c.C.gx
  py : toM c.C.p (2 ^ (64 * c.n)) (sv c base s PY) =
    if KeyOk c s₀ then Fin.ofNat c.C.p (keyY c s₀) else Fin.ofNat c.C.p c.C.gy
  /-- Memory outside the working space is unchanged. -/
  unch : Unch base [(0, size)] s₀.mem s.mem
  syms : s.syms = s₀.syms

theorem args_ok (c : Cfg) (s : State) (hl : c.C.len < 4096) :
    WP isa (.block (Impl.Ecdsa.Verify.AArch64.Cfg.args c)) s fun s' =>
      s'.gpr .x4 = s.gpr .x3 ∧ s'.gpr .x6 = s.gpr .x0 ∧ s'.gpr .x3 = s.gpr .x2 ∧
        s'.gpr .x8 = s.gpr .x2 + BitVec.ofNat 64 c.C.len ∧
        s'.gpr .x2 = s.gpr .x0 + BitVec.ofNat 64 1 ∧ Keeps [.x2, .x3, .x4, .x6, .x8] s s' := by
  apply WP.of_runBlock
  simp only [Impl.Ecdsa.Verify.AArch64.Cfg.args, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show (0 : Nat) < 4096 by decide, show (1 : Nat) < 4096 by decide,
    hl, ite_true, RegUpd.gpr_write, BitVec.setWidth_eq, BitVec.add_zero,
    reduceCtorEq, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, trivial, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

theorem verify_eq' (c : Cfg) : Impl.Ecdsa.Verify.AArch64.Cfg.verify c =
    .seq (.block (Impl.Ecdsa.Verify.AArch64.Cfg.args c)) (.seq (.seq (.block (c.setupWith (some D)))
      (.seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n)) (.block [])))
    (.seq (.block (Impl.Ecdsa.Verify.AArch64.Cfg.loadS c)) (.seq (.block (Impl.Ecdh.AArch64.Cfg.peer c))
    (.seq (Impl.Ecdh.AArch64.Cfg.validate c) (Impl.Ecdsa.Verify.AArch64.Cfg.back c))))) := rfl

/-- Ranges of the working space, as one. -/
theorem unch_whole {base : Addr} {W : List (Nat × Nat)} {m m' : Mem} (h : Unch base W m m')
    (hW : ∀ w ∈ W, w.1 + w.2 ≤ size) : Unch base [(0, size)] m m' :=
  (h.outside fun w hw => ⟨Nat.zero_le _, by have := hW w hw; omega⟩).unch

theorem slW_le (h7 : c.n < 10) {l : List Nat} (hl : ∀ i ∈ l, i < 45) : ∀ w ∈ slW c l, w.1 + w.2 ≤ size := by
  intro w hw
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
  exact sl_le c h7 (hl i hi)

theorem flag_le (h0 : 0 < c.n) (h7 : c.n < 10) : ∀ w ∈ [(c.sl FLAG, 8)], w.1 + w.2 ≤ size := by
  intro w hw
  rw [List.mem_singleton.mp hw]
  have := sl_le c h7 (i := FLAG) (by decide)
  dsimp only; omega

/-- `args`, the signature's setup and tables, `s`, and the checks of the key. -/
theorem front_ok (hc : BaseCfgOk c) {s₀ : State} (hp : FrontPre c s₀) {rest : Prog isa}
    {Q : State → Prop}
    (h : ∀ g s, (∀ r ∈ Cfg.saved.map Prod.fst, g r = s₀.gpr r) → Front c s₀ (s₀.gpr .x3) g s →
      WP isa rest s Q) :
    WP isa (.seq (.block (Impl.Ecdsa.Verify.AArch64.Cfg.args c)) (.seq (.seq (.block (c.setupWith (some D)))
      (.seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n)) (.block [])))
      (.seq (.block (Impl.Ecdsa.Verify.AArch64.Cfg.loadS c)) (.seq (.block (Impl.Ecdh.AArch64.Cfg.peer c))
      (.seq (Impl.Ecdh.AArch64.Cfg.validate c) rest))))) s₀ Q := by
  obtain ⟨extra, hrd⟩ := hp.rd
  have h0 := hc.n0
  have h7 := hc.n10
  have hsz : size = 8192 := rfl
  have hl8 := hc.len8
  have hlo := hc.len_lo
  have hhi := hc.len_hi
  refine WP.seq (WP.mono_syms (args_ok c s₀ (by omega)) fun s₁ ⟨x4₁, x6₁, x3₁, x8₁, x2₁, k₁⟩ sy₁ => ?_)
  have x1₁ : s₁.gpr .x1 = s₀.gpr .x1 := k₁.gpr _ (by decide)
  have hrd₁ : s₁.rd ++ s₁.wr = s₀.rd ++ s₀.wr := by rw [k₁.rd, k₁.wr]
  have hsp : SetupPre c s₁ := by
    refine ⟨by rw [k₁.wr, hp.wr, x4₁]; simp, fun e he => ?_, fun e he => ?_, fun e he => ?_, ?_, ?_, ?_,
      by rw [x4₁]; exact hp.sc_fit⟩
    · rw [x3₁, hrd₁, hrd]
      exact ⟨⟨s₀.gpr .x2, 2 * c.C.len⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
    · rw [x1₁, hrd₁, hrd]
      exact ⟨_, by simp, Offset.contains_base _ he (by omega)⟩
    · rw [x2₁, hrd₁, hrd, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      exact ⟨⟨s₀.gpr .x0, 1 + 2 * c.C.len⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
    · rw [x1₁, x4₁]; exact hp.dg_sc
    · rw [x2₁, x4₁]; exact hp.pk_sc.sub_left (Offset.sub_base _ (by omega))
    · rw [x3₁, x4₁]; exact hp.sig_sc.sub_left (Region.sub_prefix (by omega))
  refine WP.seq (WP.mono (stage₁ hc (.inr (.inl rfl)) hsp (rest := .block []) (Q := St₁ c (some D) s₁ (s₁.gpr .x4))
    fun _ S => WP.block_nil S) fun s₂ S₂ => ?_)
  rw [x4₁] at S₂
  have hn := S₂.scr.nowrap
  have hrw₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [S₂.rd, S₂.wr, hrd₁]
  have W₂ : Outside (s₀.gpr .x3) 0 size s₀.mem s₂.mem := fun x hx =>
    (S₂.unch x fun w hw => by rw [List.mem_singleton.mp hw]; exact hx).trans (congrFun k₁.mem x)
  -- `s`.
  have hx8 : s₂.gpr .x8 = s₀.gpr .x2 + BitVec.ofNat 64 c.C.len := by rw [S₂.gpr _ (by decide), x8₁]
  have hPT := sl_le c h7 (i := PT) (by decide)
  rw [Impl.Ecdsa.Verify.AArch64.Cfg.loadS]
  refine WP.seq (WP.mono_syms (loadBytes_ok S₂.scr (src := .x8) (by decide) (by decide) hPT (sl_mod8 c PT)
    hl8 hlo hhi (by omega) (fun d hd => by
      rw [hrw₂, hrd, hx8, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      exact ⟨⟨s₀.gpr .x2, 2 * c.C.len⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩)
    (by
      rw [hx8]
      exact (hp.sig_sc.sub_left (Offset.sub_base _ (by omega))).sub_right
        (Offset.sub_base _ hPT))) fun s₃ ⟨e₃, k₃, O₃⟩ sy₃ => ?_)
  have hs₃ := S₂.scr.of_keepRegs k₃ (by decide)
  have U₃ : Unch (s₀.gpr .x3) (slW c [PT]) s₂.mem s₃.mem := O₃.unch
  have F₃ := S₂.fixed.unch h7 hn (fixedOk_slW (l := [PT]) (by decide)) U₃
  have v₃ : ∀ {i}, i < 45 → i ≠ PT → sv c (s₀.gpr .x3) s₃ i = sv c (s₀.gpr .x3) s₂ i := fun hi hl =>
    sv_unch U₃ h7 hn hi (apart_slW (by simpa using hl))
  have pt₃ : sv c (s₀.gpr .x3) s₃ PT = sigS c s₀ := by
    rw [sv, e₃, hx8, bytesAt_keep W₂ (hp.sig_sc.sub_left (Offset.sub_base _ (by omega))) (by omega)
      (by omega)]
  -- The key.
  have hq₃ : s₃.gpr .x6 = s₀.gpr .x0 := by rw [k₃.gpr _ (by decide), S₂.gpr _ (by decide), x6₁]
  have hrw₃ : s₃.rd ++ s₃.wr = s₀.rd ++ s₀.wr := by rw [k₃.rd, k₃.wr, hrw₂]
  refine WP.seq (WP.mono_syms (peer_ok hc hs₃ hq₃ (by rw [hrw₃, hrd]; simp) hp.pk_sc F₃.mp)
    fun s₄ ⟨hs₄, k₄, U₄, r2₄, bp₄, y₄, f₄⟩ sy₄ => ?_)
  have F₄ := F₃.unch h7 hn ((fixedOk_slW (l := [R2P, BP, QY]) (by decide)).append fixedOk_flag) U₄
  have e₄ : ∀ {i}, i < 45 → i ∉ [R2P, BP, QY] → i ≠ FLAG →
      sv c (s₀.gpr .x3) s₄ i = sv c (s₀.gpr .x3) s₃ i := fun hi hl hf =>
    sv_unch U₄ h7 hn hi (apart_append (apart_slW hl) (apart_flag h0 hf))
  have W₃ : Outside (s₀.gpr .x3) 0 size s₀.mem s₃.mem :=
    W₂.trans ((U₃.outside fun w hw => by
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hw; subst hw
      exact ⟨Nat.zero_le _, hPT⟩))
  have x₄ : sv c (s₀.gpr .x3) s₃ E = keyX c s₀ := by
    rw [v₃ (by decide) (by decide), S₂.e, shAt_D_E, Nat.shiftRight_zero]
    simp only [ev, k₁.mem, x2₁]
  have hq0 : s₃.mem (s₀.gpr .x0) = s₀.mem (s₀.gpr .x0) := by
    have := keep_of_disjoint' W₃ hp.pk_sc (by omega) (i := 0) (by omega) (by omega)
    rwa [BitVec.add_zero] at this
  have y₄' : sv c (s₀.gpr .x3) s₄ QY = keyY c s₀ := by
    rw [y₄, bytesAt_keep W₃ (hp.pk_sc.sub_left (Offset.sub_base _ (by omega))) (by omega) (by omega)]
  have hf₄ : word s₄.mem (s₀.gpr .x3) (c.sl FLAG) = mask (((s₀.mem (s₀.gpr .x0) = 4 ∧
      sv c (s₀.gpr .x3) s₄ E < c.C.p) ∧ sv c (s₀.gpr .x3) s₄ QY < c.C.p)) := by
    rw [f₄, flag_unch U₃ h7 h0 hn (by decide), S₂.flag, BitVec.allOnes_and, mask_and, mask_and, hq0,
      e₄ (i := E) (by decide) (by decide) (by decide)]
  refine WP.seq (WP.mono_syms (validate_ok hc hs₄ F₄ r2₄ bp₄ hf₄)
    fun s₅ ⟨hs₅, g₅, rd₅, wr₅, U₅, f₅, px_lt, py_lt, px, py⟩ sy₅ => h s₁.gpr s₅
      (fun r hr => k₁.gpr r (by revert r; decide)) ?_)
  have F₅ := F₄.unch h7 hn ((fixedOk_slW (l := [QXM, QYM, TMP, W0, W1, W2, W3, PY]) (by decide)).append
    fixedOk_flag) U₅
  have e₅ : ∀ {i}, i < 45 → i ∉ [QXM, QYM, TMP, W0, W1, W2, W3, PY] → i ≠ FLAG →
      sv c (s₀.gpr .x3) s₅ i = sv c (s₀.gpr .x3) s₄ i := fun hi hl hf =>
    sv_unch U₅ h7 hn hi (apart_append (apart_slW hl) (apart_flag h0 hf))
  have a₅ : ∀ {i}, i < 45 → i ∉ [QXM, QYM, TMP, W0, W1, W2, W3, PY] → i ∉ [R2P, BP, QY] → i ≠ FLAG →
      i ≠ PT → sv c (s₀.gpr .x3) s₅ i = sv c (s₀.gpr .x3) s₂ i := fun hi h₁ h₂ hf hp =>
    ((e₅ hi h₁ hf).trans (e₄ hi h₂ hf)).trans (v₃ hi hp)
  have hok : PeerOk c (s₀.gpr .x3) s₄ ((s₀.mem (s₀.gpr .x0) = 4 ∧ sv c (s₀.gpr .x3) s₄ E < c.C.p) ∧
      sv c (s₀.gpr .x3) s₄ QY < c.C.p) = KeyOk c s₀ := by
    rw [PeerOk, e₄ (i := E) (by decide) (by decide) (by decide), x₄, y₄']
  simp only [hok] at f₅ px py
  rw [e₄ (i := E) (by decide) (by decide) (by decide), x₄] at px
  rw [y₄'] at py
  refine ⟨hs₅, by rw [wr₅, k₄.wr, k₃.wr, S₂.wr, k₁.wr], by rw [rd₅, k₄.rd, k₃.rd, S₂.rd, k₁.rd], F₅,
    by rw [a₅ (i := K) (by decide) (by decide) (by decide) (by decide) (by decide), S₂.k]
       simp only [kv, k₁.mem, x3₁],
    by rw [a₅ (i := D) (by decide) (by decide) (by decide) (by decide) (by decide), S₂.d, shAt_self]
       simp only [dv, k₁.mem, x1₁],
    by rw [e₅ (i := PT) (by decide) (by decide) (by decide), e₄ (by decide) (by decide) (by decide), pt₃],
    by rw [a₅ (i := RX) (by decide) (by decide) (by decide) (by decide) (by decide), S₂.rx],
    by rw [a₅ (i := RY) (by decide) (by decide) (by decide) (by decide) (by decide), S₂.ry],
    by rw [a₅ (i := RZ) (by decide) (by decide) (by decide) (by decide) (by decide), S₂.rz],
    f₅, px_lt, py_lt, px, py, ?_, by rw [sy₅, sy₄, sy₃, S₂.syms, sy₁]⟩
  have U := ((S₂.unch.trans U₃).trans U₄).trans U₅
  rw [k₁.mem] at U
  refine unch_whole U fun w hw => ?_
  simp only [List.mem_append] at hw
  rcases hw with ((hw | hw) | (hw | hw)) | (hw | hw)
  · rw [List.mem_singleton.mp hw]; exact Nat.le_of_eq (Nat.zero_add _)
  · exact slW_le h7 (by decide) w hw
  · exact slW_le h7 (by decide) w hw
  · exact flag_le h0 h7 w hw
  · exact slW_le h7 (by decide) w hw
  · exact flag_le h0 h7 w hw

end VG.Proof.Ecdsa.Verify.AArch64
