module

public import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.Contract
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Stages
public import VerifiedGarbage.Impl.EcKey.Compressed.PPC64LE
public import VerifiedGarbage.Proof.Ecdh.Exchange
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Layout
import VerifiedGarbage.Proof.EcKey.Compressed.Parity
import VerifiedGarbage.Proof.EcKey.PPC64LE.Finish
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Finish
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Setup
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.BytesLen
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Mont.PPC64LE.Row
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.EcKey.Compressed.Encode
import VerifiedGarbage.Proof.Ecdh.PPC64LE.Main
import VerifiedGarbage.Proof.Ecdh.PPC64LE.Peer
import VerifiedGarbage.Proof.Ecdh.PPC64LE.Validate

/-! ### `EcKey.Compressed.PPC64LE.Finish`, which only this module used -/

section

/-!
# SEC 1 point compression on PPC64LE: the result

`compressFinish` writes `02 + (y mod 2)` and `x` big-endian to `out` (in
`r14`), or zeros, by the flag's mask, returns the flag's low bit and restores
the callee-saved registers and `lr` (`finish_ok`): the tag by `stb`, `x` from
`out + 1` by `storeBytes`, as the public key's `finish`
(`Proof/EcKey/PPC64LE/Finish.lean`).
-/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.PPC64LE

open VG VG.PPC64LE VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE VG.Impl.Ecdsa.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Ecdsa.PPC64LE VG.Spec.Weierstrass VG.Proof.Weierstrass.PPC64LE.Mont
open VG.Proof.EcKey.PPC64LE (toNat_add_of)
open VG.Impl.Ecdh.PPC64LE (QY)

variable {c : Cfg}

theorem finish_eq (c : Cfg) : Impl.EcKey.Compressed.PPC64LE.compressFinish c =
    ([.load .d .r10 wb (c.sl FLAG), .load .d .r4 wb (c.sl QY), .li .r5 1, .logic .and .r4 .r4 .r5,
      .addi .r4 .r4 2, .logic .and .r4 .r4 .r10, .stb .r4 .r14 0] : List Instr) ++
    (storeBytes c.C.len c.n .r14 1 (c.sl E) ++
    (.li .r4 1 :: .logic .and .r4 .r10 .r4 :: (Cfg.restore ++ [mov .r3 .r4]))) := by
  simp only [Impl.EcKey.Compressed.PPC64LE.compressFinish, Impl.EcKey.Compressed.PPC64LE.compressTag,
    List.append_assoc, List.cons_append, List.nil_append]

/-- The tag or zeros, `x` or zeros, the return value and the callee-saved
registers. -/
theorem finish_ok (hc : CfgOk c) {base : Addr} {s : State} (hw : WsReg s base) {out : Addr}
    (h14 : s.gpr .r14 = out) (hofit : out.toNat + (1 + c.C.len) ≤ 2 ^ 64)
    (hwr : (⟨out, 1 + c.C.len⟩ : Region) ∈ s.wr)
    (hd : Region.Disjoint ⟨out, 1 + c.C.len⟩ ⟨base, size⟩) (b : Bool)
    (hf : flagW c base s = mask64 (b = true)) :
    WP isa (.block (Impl.EcKey.Compressed.PPC64LE.compressFinish c)) s fun s' =>
      Spec.Ecdsa.bytesAt s'.mem out (1 + c.C.len) =
        (if b then BitVec.ofNat 8 (2 + sv c base s QY % 2) :: toBytes c.C.len (sv c base s E)
          else List.replicate (1 + c.C.len) 0) ∧
      s'.gpr .r3 = (if b then 1 else 0) ∧
      s'.lr = word s.mem base Cfg.lrAt ∧ s'.gpr .r14 = word s.mem base 0 ∧ s'.gpr .r31 = word s.mem base 8 ∧
      Rk [.r0, .r3, .r4, .r5, .r6, .r10, .r14, .r31] s s' ∧
      Outside out 0 (1 + c.C.len) s.mem s'.mem := by
  have h7 := hc.n10
  have hl8 := hc.len8
  have hlhi := hc.len_hi
  have hllo := hc.len_lo
  have hn0 := hc.n0
  have hn := hw.nowrap
  have hsz : size = 8192 := rfl
  obtain hE := sl_le c h7 (i := E) (by decide)
  obtain hQ := sl_le c h7 (i := QY) (by decide)
  obtain hF := sl_le c h7 (i := FLAG) (by decide)
  have hs := hw.ws
  have h3 := hw.at3
  obtain hin : ∀ {d e m : Nat}, d + e + m ≤ 1 + c.C.len →
      InRegions s.wr (out + BitVec.ofNat 64 d + BitVec.ofNat 64 e) m := fun hd' =>
    ⟨_, hwr, by rw [Offset.add_add]; exact Offset.contains_base out hd' (by omega_using [h7, hlhi, hd'])⟩
  obtain hin0 : InRegions s.wr (out + BitVec.ofNat 64 0) 1 := by
    have := hin (d := 0) (e := 0) (m := 1) (by omega_using []); rwa [BitVec.add_zero] at this
  -- The flag and the tag.
  obtain lead : WP isa (.block [.load .d .r10 wb (c.sl FLAG), .load .d .r4 wb (c.sl QY), .li .r5 1,
      .logic .and .r4 .r4 .r5, .addi .r4 .r4 2, .logic .and .r4 .r4 .r10, .stb .r4 .r14 0]) s
      fun t => Kp [.r4, .r5, .r10] s t ∧
        t.mem = s.mem.writeW (out + BitVec.ofNat 64 0)
          (if b then BitVec.ofNat 8 (2 + sv c base s QY % 2) else 0 : BitVec 8) ∧
        t.gpr .r10 = (if b then BitVec.allOnes 64 else 0) := by
    refine wp_step (ld0_ok hs h3 (by decide) (sl_al c FLAG) (by omega_using [hF])) ?_
    refine wp_step (ld0_ok (hs.write _ _) (h3.write _) (by decide) (sl_al c QY) (by omega_using [hQ])) ?_
    refine wp_step (exec_li (by decide)) ?_
    refine wp_step exec_logic ?_
    refine wp_step (exec_addi (by decide) (by decide)) ?_
    refine wp_step exec_logic ?_
    refine wp_step (exec_stb (by decide) (by decide) (by simp only [write_gpr, write_wr, reduceCtorEq, ite_false, h14]; exact hin0))
      (WP.block_nil ⟨?_, ?_, ?_⟩)
    · exact (((((Kp.write _ _ (by decide)).trans (Kp.write _ _ (by decide))).trans (Kp.write _ _ (by decide))).trans
        (Kp.write _ _ (by decide))).trans ((Kp.write _ _ (by decide)).trans (Kp.write _ _ (by decide)))).trans
        (Kp.store _ _ _)
    · simp only [write_gpr, reduceCtorEq, ite_false, ite_true, write_mem, h14]
      rw [show word s.mem base (c.sl FLAG) = mask64 (b = true) from hf,
        ← tag_byte s.mem base (c.sl QY) c.n hn0 b]; rfl
    · simp only [write_gpr, reduceCtorEq, ite_false, ite_true]; exact hf
  rw [finish_eq]
  refine wp_append (WP.mono lead fun s₄ ⟨K₄, hm₄, hc₄⟩ => ?_)
  obtain O₄ : Outside out 0 1 s.mem s₄.mem := by
    rw [hm₄]; exact writeW8_outside s.mem out (d := 0) _ (by omega_using [])
  obtain L₄ : s₄.mem (out + BitVec.ofNat 64 0) = if b then BitVec.ofNat 8 (2 + sv c base s QY % 2) else 0 := by
    rw [hm₄, writeW8_self]
  obtain U₄ := O₄.unch_far (hd.symm.sub_right (Region.sub_prefix (by omega_using [])))
  obtain hb₄ : s₄.gpr .r14 = out := by rw [K₄.g, h14]
  obtain x₄ : wordsVal s₄.mem base (c.sl E) c.n = sv c base s E := by
    rw [U₄.wordsVal (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; omega) (by omega_using [hE])]
  obtain hs₄ := K₄.ws hs
  obtain h3₄ := K₄.at h3
  -- `x`, from `out + 1`.
  obtain hdx : Region.Disjoint ⟨off base (c.sl E), 8 * c.n⟩ ⟨out + BitVec.ofNat 64 1, c.C.len⟩ :=
    (hd.symm.sub_left (Offset.sub_base base (by omega_using [hsz, hE]))).sub_right (Offset.sub_base out (by omega_using []))
  refine wp_append (WP.mono (storeBytes_ok hs₄ h3₄ (dst := .r14) (d := 1) (a := c.sl E) (by decide) (by decide)
    (by decide) (by decide) b hc₄ (by omega_using [hE]) (sl_al c E) (by omega_using [hl8]) (by omega_using [hllo]) hlhi (by omega_using [h7, hlhi])
    (by rw [hb₄, toNat_add_of (by omega_using [hofit, hl8])]; omega_using [hofit]) (fun e m he => by rw [K₄.wr, hb₄]; exact hin (by omega_using [he]))
    (by rw [hb₄]; exact hdx)) fun s₅ ⟨e₅, k₅, O₅⟩ => ?_)
  rw [hb₄, x₄] at e₅
  rw [hb₄] at O₅
  obtain U₅ := O₅.unch_far (hd.symm.sub_right (Offset.sub_base out (d := 1) (n := c.C.len) (by omega_using [])))
  obtain hsv : ∀ d, d + 8 ≤ 24 → word s₅.mem base d = word s.mem base d := fun d hd' => by
    rw [U₅.word (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; omega) (by omega_using [hd']),
      U₄.word (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; omega) (by omega_using [hd'])]
  obtain hs₅ := k₅.ws hs₄
  obtain h3₅ := k₅.at h3₄
  -- The return value and the callee-saved registers.
  refine wp_step (exec_li (by decide)) ?_
  refine wp_step exec_logic ?_
  refine restore_ok ((hs₅.write _ _).write _ _) ((h3₅.write _).write _) (by omega_using []) fun t Kt mt lrt r14t r31t => ?_
  refine wp_step exec_mov (WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  · have lead : Spec.Ecdsa.bytesAt s₅.mem out 1 = [if b then BitVec.ofNat 8 (2 + sv c base s QY % 2) else 0] := by
      rw [bytesAt_keep O₅ (Offset.base_disjoint out (by omega_using []) (by omega_using [hofit])) (by omega_using [hofit]) (by omega_using [])]
      exact congrArg (· :: []) L₄
    simp only [write_mem]
    rw [mt]
    simp only [write_mem]
    rw [bytesAt_add, lead, e₅]
    cases b
    · simp only [Bool.false_eq_true, ite_false]
      rw [Nat.add_comm 1, List.replicate_succ]; rfl
    · simp only [ite_true]; rfl
  · simp only [write_gpr, ite_true]
    rw [Kt.gpr _ (by decide)]
    simp only [write_gpr, ite_true, reduceCtorEq, ite_false]
    rw [k₅.g, hc₄, ← mask_bit]
  · simp only [write_lr]; rw [lrt]; simp only [write_mem]; exact hsv _ (by decide)
  · simp only [write_gpr, reduceCtorEq, ite_false]; rw [r14t]; simp only [write_mem]; exact hsv _ (by decide)
  · simp only [write_gpr, reduceCtorEq, ite_false]; rw [r31t]; simp only [write_mem]; exact hsv _ (by decide)
  · have R₁ : Rk [.r0, .r3, .r4, .r5, .r6, .r10, .r14, .r31] s s₅ :=
      (K₄.rk (rs' := [.r0, .r3, .r4, .r5, .r6, .r10, .r14, .r31])).trans
        (k₅.rk (rs' := [.r0, .r3, .r4, .r5, .r6, .r10, .r14, .r31]))
    exact ((R₁.trans (((Kp.write s₅ (d := .r4) (BitVec.ofNat 64 1) (rs := [.r4]) (by decide)).trans
      (Kp.write _ (d := .r4) _ (rs := [.r4]) (by decide))).rk)).trans (Kt.mono (by decide))).trans
      ((Kp.write t (d := .r3) _ (rs := [.r3]) (by decide)).rk)
  · simp only [write_mem]
    rw [mt]
    simp only [write_mem]
    exact (O₄.mono (Nat.zero_le _) (by omega_using [])).trans ((outside_shift O₅ (by omega_using [hofit])).mono (Nat.zero_le _)
      (by omega_using []))

end VG.Proof.EcKey.Compressed.PPC64LE

end

end


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
  obtain hr12 : (s.write .r12 (s.gpr .r4)).gpr .r12 = s.gpr .r4 := by simp only [write_gpr, ite_true]
  obtain hr5 : (s.write .r12 (s.gpr .r4)).gpr .r5 = s.gpr .r5 := by
    simp only [write_gpr, reduceCtorEq, ite_false]
  obtain hlen : c.C.len ≤ 1 + 2 * c.C.len := by omega_arith
  obtain hin : ∀ e, e + 8 ≤ c.C.len → InRegions ((s.write .r12 (s.gpr .r4)).rd ++ (s.write .r12 (s.gpr .r4)).wr)
      ((s.write .r12 (s.gpr .r4)).gpr .r12 + BitVec.ofNat 64 e) 8 := fun e he => by
    rw [hr12, write_rd, write_wr]
    exact inRegions_words (len := 1 + 2 * c.C.len) (by rw [hp.rd]; simp) (by have := hp.pk_fit; omega_arith) e (by omega_arith)
  obtain hd : Region.Disjoint ⟨(s.write .r12 (s.gpr .r4)).gpr .r12, c.C.len⟩
      ⟨(s.write .r12 (s.gpr .r4)).gpr .r5, size⟩ := by
    rw [hr12, hr5]; exact hp.pk_sc.sub_left (Region.sub_prefix hlen)
  obtain hf : ((s.write .r12 (s.gpr .r4)).gpr .r12).toNat + c.C.len ≤ 2 ^ 64 := by
    rw [hr12]; have := hp.pk_fit; omega_arith
  obtain hwr : (⟨(s.write .r12 (s.gpr .r4)).gpr .r5, size⟩ : Region) ∈ (s.write .r12 (s.gpr .r4)).wr := by
    rw [hr5, write_wr, hp.wr]; simp
  obtain hsf : ((s.write .r12 (s.gpr .r4)).gpr .r5).toNat + size ≤ 2 ^ 64 := by rw [hr5]; exact hp.sc_fit
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
  obtain hr5 : (s₀.write .r12 (s₀.gpr .r4)).gpr .r5 = s₀.gpr .r5 := by
    simp only [write_gpr, reduceCtorEq, ite_false]
  generalize hb : (s₀.write .r12 (s₀.gpr .r4)).gpr args.sc = base at S₂
  replace hb : s₀.gpr .r5 = base := hr5.symm.trans hb
  have hn := S₂.ws.nowrap
  obtain r12₂ : s₂.gpr .r12 = s₀.gpr .r4 := by
    rw [kp₂.gpr _ (by decide)]; simp only [write_gpr, ite_true]
  obtain W₂ : Outside base 0 size s₀.mem s₂.mem :=
    S₂.whole.outside fun w hw => by rw [List.mem_singleton.mp hw]; exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  obtain hpsc : Region.Disjoint ⟨s₀.gpr .r4, 1 + 2 * c.C.len⟩ ⟨base, size⟩ := by rw [← hb]; exact hp.pk_sc
  -- The key.
  refine WP.seq (WP.mono (peer_ok hc S₂.ws (q := .r12) (by decide)
    (by rw [r12₂]; exact hp.pk_fit) (by rw [r12₂, S₂.rk.rd, S₂.rk.wr, write_rd, write_wr, hp.rd]; simp)
    (by rw [r12₂]; exact hpsc) S₂.fixed.mp) fun s₃ ⟨hw₃, k₃, U₃, r2₃, bp₃, x₃, y₃, f₃⟩ => ?_)
  rw [r12₂] at x₃ y₃ f₃
  obtain hl₃ : ∀ i ∈ [R2P, BP, E, QY], i < 45 := by decide
  obtain K₃ := S₂.toKeep.step h7 (k₃.rk (rs' := peerClob)) (hU := U₃)
    (hW := (fixedOk_slW (by decide)).append fixedOk_flag)
    (hWs := le_append (fun w hw => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      have := sl_le c h7 (hl₃ i hi); dsimp only; omega_arith)
      (fun w hw => by
        rw [List.mem_singleton.mp hw]; have := sl_le c h7 (i := FLAG) (by decide); dsimp only; omega_arith))
  obtain hq0 : s₂.mem (s₀.gpr .r4) = s₀.mem (s₀.gpr .r4) := by
    have := keep_of_disjoint' W₂ hpsc (by omega_arith) (i := 0) (by omega_arith) (by omega_arith)
    rwa [BitVec.add_zero] at this
  obtain x₃' : sv c base s₃ E = keyX c s₀ := by
    rw [x₃, bytesAt_keep W₂ (hpsc.sub_left (Offset.sub_base _ (by omega_arith))) (by omega_arith) (by omega_arith)]
  obtain y₃' : sv c base s₃ QY = keyY c s₀ := by
    rw [y₃, bytesAt_keep W₂ (hpsc.sub_left (Offset.sub_base _ (by omega_arith))) (by omega_arith) (by omega_arith)]
  obtain hf₃ : flagW c base s₃ = mask64 ((s₀.mem (s₀.gpr .r4) = 4 ∧ sv c base s₃ E < c.C.p) ∧
      sv c base s₃ QY < c.C.p) := by
    rw [f₃, hq0, S₂.flag, BitVec.allOnes_and, mask64_and, mask64_and]
  -- The validation.
  refine WP.seq (WP.mono (validate_ok hc K₃.ws K₃.fixed r2₃ bp₃ hf₃)
    fun s₄ ⟨hw₄, k₄, U₄, f₄, _, _, _, _⟩ => ?_)
  obtain K₄ := K₃.step h7 k₄ (hU := U₄) (hW := fixedOk_valW h7) (hWs := valW_le h7)
  obtain e₄ : ∀ {i}, i < 45 → i ∉ [QXM, QYM, W0, W1, W2, W3, PY] → i ≠ FLAG → sv c base s₄ i = sv c base s₃ i :=
    fun hi hl hf => sv_unch U₄ h7 hn hi (apart_append (apart_slW hl)
      (show ∀ w ∈ [(own c.n, 64 * c.n)] ++ [(c.sl FLAG, 8)], _ from
        apart_append (apart_own h7 hi) (apart_flag h0 hf)))
  obtain hok : PeerOk c base s₃ ((s₀.mem (s₀.gpr .r4) = 4 ∧ sv c base s₃ E < c.C.p) ∧ sv c base s₃ QY < c.C.p) ↔
      KeyOk c s₀ := by
    unfold PeerOk
    rw [x₃', y₃']
    exact ⟨fun ⟨⟨⟨h4, hx⟩, hy⟩, he⟩ => ⟨h4, hx, hy, he⟩, fun ⟨h4, hx, hy, he⟩ => ⟨⟨⟨h4, hx⟩, hy⟩, he⟩⟩
  obtain hf₄ : flagW c base s₄ = mask64 (decide (KeyOk c s₀) = true) := by
    rw [f₄]; simp only [decide_eq_true_eq, hok]
  obtain h14 : s₄.gpr .r14 = s₀.gpr .r3 := by
    rw [K₄.r14]; simp only [write_gpr, reduceCtorEq, ite_false]
  -- The result.
  refine WP.mono (finish_ok hc K₄.ws h14 hp.out_fit
    (by rw [K₄.rk.wr, write_wr, hp.wr]; simp) (by rw [← hb]; exact hp.out_sc) _ hf₄)
    fun s' ⟨bytes, r3, lr, r14, r31, rk, _⟩ => ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro r hr
    have hsv := K₄.fixed.saved
    obtain hcases : ∀ r ∈ preserved, r = .r14 ∨ r = .r31 ∨
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
  obtain hlen : (Spec.Ecdsa.bytesAt s.mem (s.gpr .r4) (1 + 2 * c.C.len)).length = 2 * c.C.len + 1 := by
    rw [length_bytesAt]; omega_arith
  obtain hhead : (Spec.Ecdsa.bytesAt s.mem (s.gpr .r4) (1 + 2 * c.C.len)).head? = some (s.mem (s.gpr .r4)) := by
    rw [peer_bytes]; rfl
  obtain hx : ofBytes (((Spec.Ecdsa.bytesAt s.mem (s.gpr .r4) (1 + 2 * c.C.len)).drop 1).take c.C.len) =
      keyX c s := by
    rw [peer_bytes, List.drop_one, List.tail_cons, List.take_left' (length_bytesAt _ _ _)]
  obtain hy : ofBytes ((Spec.Ecdsa.bytesAt s.mem (s.gpr .r4) (1 + 2 * c.C.len)).drop (c.C.len + 1)) =
      keyY c s := by
    rw [peer_bytes, List.drop_succ_cons, List.drop_left' (length_bytesAt _ _ _)]
  change Spec.EcKey.compressPublicKey c.C (Spec.Ecdsa.bytesAt s.mem (s.gpr .r4) (2 * c.C.len + 1)) = _
  rw [show 2 * c.C.len + 1 = 1 + 2 * c.C.len by omega_arith, compress_eq hlen hhead hx hy]

theorem compress_correct (c : Cfg) (hc : CfgOk c) (s : State) (hs : (compressContract c.C).pre s) :
    ∃ t s', Exec isa (Impl.EcKey.Compressed.PPC64LE.compress c) s t s' ∧
      abiPreserved s s' ∧ (compressContract c.C).post s s' := by
  obtain ⟨hrd, hwr, hpo, hpw, how, hfit, hpkfit, hwfit⟩ := hs
  obtain hp : CPre c s :=
    ⟨by rw [hrd, show 2 * c.C.len + 1 = 1 + 2 * c.C.len by omega_arith],
      by rw [hwr, show c.C.len + 1 = 1 + c.C.len by omega_arith],
      by simpa only [show 2 * c.C.len + 1 = 1 + 2 * c.C.len by omega_arith] using hpw,
      by simpa only [show c.C.len + 1 = 1 + c.C.len by omega_arith] using how,
      by omega_arith, by omega_arith, hwfit⟩
  obtain ⟨t, s', he, K, bytes, ret⟩ := compress_ok hc hp
  refine ⟨t, s', he, ⟨K.saved, K.sp, K.lr⟩, ?_⟩
  show (match Spec.EcKey.compressPublicKey c.C (Spec.EcKey.bytesAt s.mem (s.gpr .r4) (2 * c.C.len + 1)) with
    | some bs => _ | none => _)
  rw [compress_key]
  change Spec.EcKey.bytesAt s'.mem (s.gpr .r3) (1 + c.C.len) = _ at bytes
  rw [show 1 + c.C.len = c.C.len + 1 by omega_arith] at bytes
  by_cases hk : KeyOk c s
  · rw [ite_eq_left hk] at bytes ret ⊢
    exact ⟨ret, bytes⟩
  · rw [ite_eq_right hk] at bytes ret ⊢
    exact ⟨ret, bytes⟩

end VG.Proof.EcKey.Compressed.PPC64LE
