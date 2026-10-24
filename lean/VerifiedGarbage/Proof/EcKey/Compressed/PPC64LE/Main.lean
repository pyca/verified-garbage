module

public import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.Contract
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Stages
public import VerifiedGarbage.Impl.EcKey.Compressed.PPC64LE
public import VerifiedGarbage.Proof.Ecdh.Exchange
import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.Finish
import VerifiedGarbage.Proof.EcKey.Compressed.Encode
import VerifiedGarbage.Proof.Ecdh.PPC64LE.Main
import VerifiedGarbage.Proof.Ecdh.PPC64LE.Peer
import VerifiedGarbage.Proof.Ecdh.PPC64LE.Validate
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Setup
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Finish
import VerifiedGarbage.Proof.Weierstrass.BytesLen
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset

/-!
# SEC 1 point compression on PPC64LE: the whole function

`compress_ok`: `compress` computes the specification's compressed key of the
uncompressed one at `public`, or zeros, for any curve the proof of the code
supports (`CfgOk`), restores the callee-saved registers and `lr`: the
signature's setup (`stage₀'`, after `public` to `r12`), ECDH's parsing
(`peer_ok`) and validation (`validate_ok`) of the key, and `finish_ok`.
`compress_correct`: the same, against `compressContract`.
-/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Ecdsa.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont VG.Proof.Ecdsa.PPC64LE VG.Proof.Ecdh.PPC64LE VG.Spec.Weierstrass
open VG.Impl.Ecdh.PPC64LE (QY R2P BP QXM QYM W0 W1 W2 W3 PY)
open VG.Impl.EcKey.Compressed.PPC64LE (args)

variable {c : Cfg}

/-- The arguments: `out` (`1 + len` bytes), `public` (`1 + 2 len` bytes) and
`scratch`, readable and writable as the contract says and apart from each
other as it says. -/
structure CPre (c : Cfg) (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .r4, 1 + 2 * c.C.len⟩]
  wr : s.wr = [⟨s.gpr .r3, 1 + c.C.len⟩, ⟨s.gpr .r5, size⟩]
  pk_sc : Region.Disjoint ⟨s.gpr .r4, 1 + 2 * c.C.len⟩ ⟨s.gpr .r5, size⟩
  out_sc : Region.Disjoint ⟨s.gpr .r3, 1 + c.C.len⟩ ⟨s.gpr .r5, size⟩
  out_fit : (s.gpr .r3).toNat + (1 + c.C.len) ≤ 2 ^ 64
  pk_fit : (s.gpr .r4).toNat + (1 + 2 * c.C.len) ≤ 2 ^ 64
  sc_fit : (s.gpr .r5).toNat + size ≤ 2 ^ 64

theorem CPre.setup {s : State} (hp : CPre c s) : SetupPre c args (s.write .r12 (s.gpr .r4)) := by
  have hr12 : (s.write .r12 (s.gpr .r4)).gpr .r12 = s.gpr .r4 := by simp only [write_gpr, ite_true]
  have hr5 : (s.write .r12 (s.gpr .r4)).gpr .r5 = s.gpr .r5 := by
    simp only [write_gpr, reduceCtorEq, ite_false]
  have hlen : c.C.len ≤ 1 + 2 * c.C.len := by omega
  have hin : ∀ e, e + 8 ≤ c.C.len → InRegions ((s.write .r12 (s.gpr .r4)).rd ++ (s.write .r12 (s.gpr .r4)).wr)
      ((s.write .r12 (s.gpr .r4)).gpr .r12 + BitVec.ofNat 64 e) 8 := fun e he => by
    rw [hr12, write_rd, write_wr]
    exact inRegions_words (len := 1 + 2 * c.C.len) (by rw [hp.rd]; simp) (by have := hp.pk_fit; omega) e (by omega)
  have hd : Region.Disjoint ⟨(s.write .r12 (s.gpr .r4)).gpr .r12, c.C.len⟩
      ⟨(s.write .r12 (s.gpr .r4)).gpr .r5, size⟩ := by
    rw [hr12, hr5]; exact hp.pk_sc.sub_left (Region.sub_prefix hlen)
  have hf : ((s.write .r12 (s.gpr .r4)).gpr .r12).toNat + c.C.len ≤ 2 ^ 64 := by
    rw [hr12]; have := hp.pk_fit; omega
  have hwr : (⟨(s.write .r12 (s.gpr .r4)).gpr .r5, size⟩ : Region) ∈ (s.write .r12 (s.gpr .r4)).wr := by
    rw [hr5, write_wr, hp.wr]; simp
  have hsf : ((s.write .r12 (s.gpr .r4)).gpr .r5).toNat + size ≤ 2 ^ 64 := by rw [hr5]; exact hp.sc_fit
  exact ⟨.inl rfl, by decide, by decide, by decide, by decide, hwr, hsf, hin, hin, hin, hd, hd, hd, hf, hf, hf⟩

/-- The key's `x` and `y`. -/
abbrev keyX (c : Cfg) (s : State) : Nat :=
  ofBytes (Spec.Ecdsa.bytesAt s.mem (s.gpr .r4 + BitVec.ofNat 64 1) c.C.len)
abbrev keyY (c : Cfg) (s : State) : Nat :=
  ofBytes (Spec.Ecdsa.bytesAt s.mem (s.gpr .r4 + BitVec.ofNat 64 (1 + c.C.len)) c.C.len)

/-- The key is valid: `04`, both coordinates below `p`, and on the curve. -/
abbrev KeyOk (c : Cfg) (s : State) : Prop := Proof.Ecdh.Valid c.C (s.mem (s.gpr .r4)) (keyX c s) (keyY c s)

/-- What the function keeps: the callee-saved registers, `sp` and `lr`. -/
structure CKeep (s₀ s' : State) : Prop where
  saved : ∀ r ∈ preserved, s'.gpr r = s₀.gpr r
  sp : s'.sp = s₀.sp
  lr : s'.lr = s₀.lr

theorem compress_eq' (c : Cfg) : Impl.EcKey.Compressed.PPC64LE.compress c =
    .seq (.block (mov .r12 .r4 :: c.setupWith args))
      (.seq (.block (Impl.Ecdh.PPC64LE.Cfg.peerAt c .r12))
      (.seq (Impl.Ecdh.PPC64LE.Cfg.validate c) (.block (Impl.EcKey.Compressed.PPC64LE.compressFinish c)))) := rfl

/-- `vg_ec_<curve>_compress_public_key` writes the compressed key, or zeros,
and returns 1 or 0, restoring the callee-saved registers and `lr`. -/
theorem compress_ok (hc : CfgOk c) {s₀ : State} (hp : CPre c s₀) :
    WP isa (Impl.EcKey.Compressed.PPC64LE.compress c) s₀ fun s' => CKeep s₀ s' ∧
      Spec.Ecdsa.bytesAt s'.mem (s₀.gpr .r3) (1 + c.C.len) =
        (if KeyOk c s₀ then BitVec.ofNat 8 (2 + keyY c s₀ % 2) :: toBytes c.C.len (keyX c s₀)
          else List.replicate (1 + c.C.len) 0) ∧
      s'.gpr .r3 = (if KeyOk c s₀ then 1 else 0) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hlhi := hc.len_hi
  have hl8 := hc.len8
  have hsz : size = 8192 := rfl
  rw [compress_eq']
  -- `public` to `r12`, and the setup.
  refine WP.seq (wp_step exec_mov (WP.mono (stage₀' hc hp.setup) fun s₂ ⟨S₂, kp₂⟩ => ?_))
  have hr5 : (s₀.write .r12 (s₀.gpr .r4)).gpr .r5 = s₀.gpr .r5 := by
    simp only [write_gpr, reduceCtorEq, ite_false]
  generalize hb : (s₀.write .r12 (s₀.gpr .r4)).gpr args.sc = base at S₂
  replace hb : s₀.gpr .r5 = base := hr5.symm.trans hb
  have hn := S₂.ws.nowrap
  have r12₂ : s₂.gpr .r12 = s₀.gpr .r4 := by
    rw [kp₂.gpr _ (by decide)]; simp only [write_gpr, ite_true]
  have W₂ : Outside base 0 size s₀.mem s₂.mem :=
    S₂.whole.outside fun w hw => by rw [List.mem_singleton.mp hw]; exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  have hpsc : Region.Disjoint ⟨s₀.gpr .r4, 1 + 2 * c.C.len⟩ ⟨base, size⟩ := by rw [← hb]; exact hp.pk_sc
  -- The key.
  refine WP.seq (WP.mono (peer_ok hc S₂.ws (q := .r12) (by decide)
    (by rw [r12₂]; exact hp.pk_fit) (by rw [r12₂, S₂.rk.rd, S₂.rk.wr, write_rd, write_wr, hp.rd]; simp)
    (by rw [r12₂]; exact hpsc) S₂.fixed.mp) fun s₃ ⟨hw₃, k₃, U₃, r2₃, bp₃, x₃, y₃, f₃⟩ => ?_)
  rw [r12₂] at x₃ y₃ f₃
  have hl₃ : ∀ i ∈ [R2P, BP, E, QY], i < 45 := by decide
  have K₃ := S₂.toKeep.step h7 (k₃.rk (rs' := peerClob)) (hU := U₃)
    (hW := (fixedOk_slW (by decide)).append fixedOk_flag)
    (hWs := le_append (fun w hw => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      have := sl_le c h7 (hl₃ i hi); dsimp only; omega)
      (fun w hw => by
        rw [List.mem_singleton.mp hw]; have := sl_le c h7 (i := FLAG) (by decide); dsimp only; omega))
  have hq0 : s₂.mem (s₀.gpr .r4) = s₀.mem (s₀.gpr .r4) := by
    have := keep_of_disjoint' W₂ hpsc (by omega) (i := 0) (by omega) (by omega)
    rwa [BitVec.add_zero] at this
  have x₃' : sv c base s₃ E = keyX c s₀ := by
    rw [x₃, bytesAt_keep W₂ (hpsc.sub_left (Offset.sub_base _ (by omega))) (by omega) (by omega)]
  have y₃' : sv c base s₃ QY = keyY c s₀ := by
    rw [y₃, bytesAt_keep W₂ (hpsc.sub_left (Offset.sub_base _ (by omega))) (by omega) (by omega)]
  have hf₃ : flagW c base s₃ = mask64 ((s₀.mem (s₀.gpr .r4) = 4 ∧ sv c base s₃ E < c.C.p) ∧
      sv c base s₃ QY < c.C.p) := by
    rw [f₃, hq0, S₂.flag, BitVec.allOnes_and, mask64_and, mask64_and]
  -- The validation.
  refine WP.seq (WP.mono (validate_ok hc K₃.ws K₃.fixed r2₃ bp₃ hf₃)
    fun s₄ ⟨hw₄, k₄, U₄, f₄, _, _, _, _⟩ => ?_)
  have K₄ := K₃.step h7 k₄ (hU := U₄) (hW := fixedOk_valW h7) (hWs := valW_le h7)
  have e₄ : ∀ {i}, i < 45 → i ∉ [QXM, QYM, W0, W1, W2, W3, PY] → i ≠ FLAG → sv c base s₄ i = sv c base s₃ i :=
    fun hi hl hf => sv_unch U₄ h7 hn hi (apart_append (apart_slW hl)
      (show ∀ w ∈ [(own c.n, 64 * c.n)] ++ [(c.sl FLAG, 8)], _ from
        apart_append (apart_own h7 hi) (apart_flag h0 hf)))
  have hok : PeerOk c base s₃ ((s₀.mem (s₀.gpr .r4) = 4 ∧ sv c base s₃ E < c.C.p) ∧ sv c base s₃ QY < c.C.p) ↔
      KeyOk c s₀ := by
    unfold PeerOk
    rw [x₃', y₃']
    exact ⟨fun ⟨⟨⟨h4, hx⟩, hy⟩, he⟩ => ⟨h4, hx, hy, he⟩, fun ⟨h4, hx, hy, he⟩ => ⟨⟨⟨h4, hx⟩, hy⟩, he⟩⟩
  have hf₄ : flagW c base s₄ = mask64 (decide (KeyOk c s₀) = true) := by
    rw [f₄]; simp only [decide_eq_true_eq, hok]
  have h14 : s₄.gpr .r14 = s₀.gpr .r3 := by
    rw [K₄.r14]; simp only [write_gpr, reduceCtorEq, ite_false]
  -- The result.
  refine WP.mono (finish_ok hc K₄.ws h14 hp.out_fit
    (by rw [K₄.rk.wr, write_wr, hp.wr]; simp) (by rw [← hb]; exact hp.out_sc) _ hf₄)
    fun s' ⟨bytes, r3, lr, r14, r31, rk, _⟩ => ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro r hr
    have hsv := K₄.fixed.saved
    have hcases : ∀ r ∈ preserved, r = .r14 ∨ r = .r31 ∨
        (r ∉ [Reg.r0, .r3, .r4, .r5, .r6, .r10, .r14, .r31] ∧ r ∉ work) := by decide
    rcases hcases r hr with rfl | rfl | ⟨h₁, h₂⟩
    · rw [r14, hsv (.r14, 0) (by decide)]; simp only [write_gpr, reduceCtorEq, ite_false]
    · rw [r31, hsv (.r31, 8) (by decide)]; simp only [write_gpr, reduceCtorEq, ite_false]
    · have h12 : r ≠ .r12 := fun h => h₂ (by rw [h]; decide)
      rw [rk.gpr r h₁, K₄.rk.gpr r h₂]; simp only [write_gpr, h12, ite_false]
  · rw [rk.sp, K₄.rk.sp, write_sp]
  · rw [lr, K₄.fixed.savedLr, write_lr]
  · rw [bytes, e₄ (by decide) (by decide) (by decide), e₄ (by decide) (by decide) (by decide), x₃', y₃']
    by_cases hk : KeyOk c s₀ <;> simp [hk]
  · rw [r3]; by_cases hk : KeyOk c s₀ <;> simp [hk]

theorem compress_key (c : Cfg) (s : State) :
    Spec.EcKey.compressPublicKey c.C (Spec.EcKey.bytesAt s.mem (s.gpr .r4) (2 * c.C.len + 1)) =
      if KeyOk c s then some (BitVec.ofNat 8 (2 + keyY c s % 2) :: toBytes c.C.len (keyX c s)) else none := by
  have hlen : (Spec.Ecdsa.bytesAt s.mem (s.gpr .r4) (1 + 2 * c.C.len)).length = 2 * c.C.len + 1 := by
    rw [length_bytesAt]; omega
  have hhead : (Spec.Ecdsa.bytesAt s.mem (s.gpr .r4) (1 + 2 * c.C.len)).head? = some (s.mem (s.gpr .r4)) := by
    rw [peer_bytes]; rfl
  have hx : ofBytes (((Spec.Ecdsa.bytesAt s.mem (s.gpr .r4) (1 + 2 * c.C.len)).drop 1).take c.C.len) =
      keyX c s := by
    rw [peer_bytes, List.drop_one, List.tail_cons, List.take_left' (length_bytesAt _ _ _)]
  have hy : ofBytes ((Spec.Ecdsa.bytesAt s.mem (s.gpr .r4) (1 + 2 * c.C.len)).drop (c.C.len + 1)) =
      keyY c s := by
    rw [peer_bytes, List.drop_succ_cons, List.drop_left' (length_bytesAt _ _ _)]
  change Spec.EcKey.compressPublicKey c.C (Spec.Ecdsa.bytesAt s.mem (s.gpr .r4) (2 * c.C.len + 1)) = _
  rw [show 2 * c.C.len + 1 = 1 + 2 * c.C.len by omega, compress_eq hlen hhead hx hy]

theorem compress_correct (c : Cfg) (hc : CfgOk c) (s : State) (hs : (compressContract c.C).pre s) :
    ∃ t s', Exec isa (Impl.EcKey.Compressed.PPC64LE.compress c) s t s' ∧
      abiPreserved s s' ∧ (compressContract c.C).post s s' := by
  obtain ⟨hrd, hwr, hpo, hpw, how, hfit, hpkfit, hwfit⟩ := hs
  have hp : CPre c s :=
    ⟨by rw [hrd, show 2 * c.C.len + 1 = 1 + 2 * c.C.len by omega],
      by rw [hwr, show c.C.len + 1 = 1 + c.C.len by omega],
      by simpa only [show 2 * c.C.len + 1 = 1 + 2 * c.C.len by omega] using hpw,
      by simpa only [show c.C.len + 1 = 1 + c.C.len by omega] using how,
      by omega, by omega, hwfit⟩
  obtain ⟨t, s', he, K, bytes, ret⟩ := compress_ok hc hp
  refine ⟨t, s', he, ⟨K.saved, K.sp, K.lr⟩, ?_⟩
  show (match Spec.EcKey.compressPublicKey c.C (Spec.EcKey.bytesAt s.mem (s.gpr .r4) (2 * c.C.len + 1)) with
    | some bs => _ | none => _)
  rw [compress_key]
  change Spec.EcKey.bytesAt s'.mem (s.gpr .r3) (1 + c.C.len) = _ at bytes
  rw [show 1 + c.C.len = c.C.len + 1 by omega] at bytes
  by_cases hk : KeyOk c s
  · rw [ite_eq_left hk] at bytes ret ⊢
    exact ⟨ret, bytes⟩
  · rw [ite_eq_right hk] at bytes ret ⊢
    exact ⟨ret, bytes⟩

end VG.Proof.EcKey.Compressed.PPC64LE
