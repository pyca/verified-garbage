module

public import VerifiedGarbage.Impl.EcKey.Compressed.PPC64LE.Decompress
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Pow
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Layout
public import VerifiedGarbage.Spec.EcKey.Compressed.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.EcKey.Compressed
public import VerifiedGarbage.Proof.EcKey.Compressed.Root
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Stages
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontCall
public import VerifiedGarbage.Proof.Weierstrass.Unch
public import VerifiedGarbage.Proof.Ecdh.PPC64LE.Peer
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Flags
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Setup
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Copy
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.BytesLen
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Mont.PPC64LE.Row
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.Poly
import VerifiedGarbage.Proof.EcKey.Compressed.Decode
import VerifiedGarbage.Proof.EcKey.PPC64LE.Finish
import VerifiedGarbage.Proof.Ecdh.PPC64LE.Main
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Mont.PPC64LE.Const
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.SlotOps
import VerifiedGarbage.Proof.EcKey.Compressed.Parity
public import VerifiedGarbage.Impl.Ecdsa.PPC64LE
public import VerifiedGarbage.Proof.Weierstrass.Env
public import VerifiedGarbage.Impl.EcKey.Compressed.PPC64LE
public import VerifiedGarbage.Proof.Ecdh.Exchange
import VerifiedGarbage.Proof.EcKey.Compressed.Encode

/-! ### `EcKey.Compressed.PPC64LE.Main`, which this module and modules that import it used -/

section

/-! ### `EcKey.Compressed.PPC64LE.Contract`, which this module and modules that import it used -/

section

/-!
# SEC 1 point compression on PPC64LE: the contract the proof is written against

The facts of `Spec.EcKey.Instance.compressPublicKeyContract` on PPC64LE, by
name, for any curve: `vg_ec_<curve>_compress_public_key(out, public,
scratch)`, with the arguments in `r3`–`r5` and the result in `r3` (ELFv2).
-/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.PPC64LE

open VG VG.PPC64LE

def compressContract (C : Spec.Weierstrass.Curve) : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .r3, C.len + 1⟩
    let pk : Region := ⟨s.gpr .r4, 2 * C.len + 1⟩
    let ws : Region := ⟨s.gpr .r5, 8192⟩
    s.rd = [pk] ∧ s.wr = [out, ws] ∧
      pk.Disjoint out ∧ pk.Disjoint ws ∧ out.Disjoint ws ∧
      (s.gpr .r3).toNat + (C.len + 1) ≤ 2 ^ 64 ∧
      (s.gpr .r4).toNat + (2 * C.len + 1) ≤ 2 ^ 64 ∧
      (s.gpr .r5).toNat + 8192 ≤ 2 ^ 64
  post s s' :=
    match Spec.EcKey.compressPublicKey C (Spec.EcKey.bytesAt s.mem (s.gpr .r4) (2 * C.len + 1)) with
    | some bs => s'.gpr .r3 = 1 ∧ Spec.EcKey.bytesAt s'.mem (s.gpr .r3) (C.len + 1) = bs
    | none => s'.gpr .r3 = 0 ∧
        Spec.EcKey.bytesAt s'.mem (s.gpr .r3) (C.len + 1) = List.replicate (C.len + 1) 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
    s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5

theorem compress_implies (I : Spec.EcKey.Instance)
    (hsat : ∃ s, (I.compressPublicKeyContract abi 0).pre s) :
    (compressContract I.curve).Implies (I.compressPublicKeyContract abi 0) where
  pre := by
    sig_implies_pre [Spec.EcKey.Instance.compressPublicKeyContract,
      Spec.EcKey.Instance.compressPublicKeySig, Spec.EcKey.scratchWords,
      abi, argRegs, compressContract]
  post := by
    intro s s' _ h
    sig_post [Spec.EcKey.Instance.compressPublicKeyContract,
      Spec.EcKey.Instance.compressPublicKeySig, Spec.EcKey.scratchWords,
      abi, argRegs, compressContract]
    simp only [compressContract] at h
    revert h
    generalize Spec.EcKey.compressPublicKey _ _ = q
    rcases q with _ | z <;> exact fun h => ⟨by rw [h.1]; rfl, h.2⟩
  pub := by
    sig_implies_pub [Spec.EcKey.Instance.compressPublicKeyContract,
      Spec.EcKey.Instance.compressPublicKeySig, Spec.EcKey.scratchWords,
      abi, argRegs, compressContract]
  sat := hsat

/-- A state satisfying the precondition, for encodings of `len` bytes. -/
def satState (len : Nat) : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x8000 | _ => 0
  lr := 0
  sp := 0x20000
  mem _ := 0
  rd := [⟨0x2000, 2 * len + 1⟩]
  wr := [⟨0x1000, len + 1⟩, ⟨0x8000, 8192⟩]

end VG.Proof.EcKey.Compressed.PPC64LE

end

end

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

end

end

/-! ### `EcKey.Compressed.PPC64LE.Select`, which only this module used -/

section

/-!
# SEC 1 point decompression on PPC64LE: the root of the tag's parity

`parityMask_ok`: the mask `r10` of `QY`'s parity differing from the tag's;
`selectRoot_ok`: the candidate out of Montgomery form, and it or `p` minus
it by that mask, to `QY`.
-/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Ecdsa.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont VG.Proof.Ecdsa.PPC64LE VG.Spec.Weierstrass VG.Proof.EcKey.Compressed
open VG.Impl.Ecdh.PPC64LE (QY W0)

variable {c : Cfg}

/-- The mask `r10` of `QY`'s parity differing from the tag's (`D`'s first
word). -/
theorem parityMask_ok (c : Cfg) {s : State} {base : Addr} {size : Nat} (hs : Ws s base size)
    (h3 : At s base .r3 0) (hn0 : 0 < c.n) (hQ : c.sl QY + 8 ≤ size) (hD : c.sl D + 8 ≤ size) :
    WP isa (.block (Impl.EcKey.Compressed.PPC64LE.parityMask c)) s fun s' =>
      s'.gpr .r10 = mask64 ((word s.mem base (c.sl D)).toNat % 2 ≠ sv c base s QY % 2) ∧
      Kp [.r4, .r5, .r10] s s' ∧ s'.mem = s.mem := by
  simp only [Impl.EcKey.Compressed.PPC64LE.parityMask]
  refine wp_step (ld0_ok hs h3 (by decide) (sl_al c QY) hQ) ?_
  refine wp_step (ld0_ok (hs.write _ _) (h3.write _) (by decide) (sl_al c D) hD) ?_
  refine wp_step exec_logic ?_
  refine wp_step (exec_li (by decide)) ?_
  refine wp_step exec_logic ?_
  refine wp_step (exec_li (by decide)) ?_
  refine wp_step exec_sub (WP.block_nil ⟨?_, ?_, ?_⟩)
  · simp only [write_gpr, ite_true, reduceCtorEq, ite_false, write_mem]
    rw [show BitVec.ofNat 64 1 = 1 from rfl, show BitVec.ofNat 64 0 = 0 from rfl, xor_low_mask,
      slot_parity s.mem base (c.sl QY) c.n hn0]
  · exact (((((Kp.write _ _ (by decide)).trans (Kp.write _ _ (by decide))).trans (Kp.write _ _ (by decide))).trans
      (Kp.write _ _ (by decide))).trans ((Kp.write _ _ (by decide)).trans (Kp.write _ _ (by decide)))).trans
      (Kp.write _ _ (by decide))
  · simp only [write_mem]

/-- What `selectRoot` writes. -/
abbrev selectW (c : Cfg) : List (Nat × Nat) := slW c [QY, W0] ++ [(own c.n, 64 * c.n)]

/-- The candidate in `ACC`, out of Montgomery form, or `p` minus it, by the
tag's parity, to `QY`. -/
theorem selectRoot_ok (hc : CfgOk c) {base : Addr} {s : State} (hw : WsReg s base)
    (hOne : sv c base s ONE = 1) (hZero : sv c base s ZERO = 0) :
    WP isa (Impl.EcKey.Compressed.PPC64LE.selectRoot c) s fun s' =>
      WsReg s' base ∧ Rk fnClob s s' ∧ Unch base (selectW c) s.mem s'.mem ∧ sv c base s' QY < c.C.p ∧
      Fin.ofNat c.C.p (sv c base s' QY) =
        (let y := toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC)
         if y.val % 2 = (word s.mem base (c.sl D)).toNat % 2 then y else -y) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hw.nowrap
  have hp3 := hc.p_ge
  have hsz : size = 8192 := rfl
  have hY := sl_le c h7 (i := QY) (by decide)
  have hW := sl_le c h7 (i := W0) (by decide)
  have hD := sl_le c h7 (i := D) (by decide)
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  change WP isa (.seq (mulCall c.SP (c.sl QY) (c.sl ACC) (c.sl ONE))
    (.seq (subCall c.SP (c.sl W0) (c.sl ZERO) (c.sl QY))
      (.block (Impl.EcKey.Compressed.PPC64LE.parityMask c ++ sel c.n (c.sl QY) (c.sl QY) (c.sl W0))))) s _
  -- `QY = ACC · 1`, out of Montgomery form.
  refine WP.seq (WP.mono (slMul_ok hc.fp hc.fpk hc.fpm h7 hw (o := QY) (a := ACC) (b := ONE)
    (by decide) (by decide) (by decide) (by rw [hOne]; omega_using [hp3])) fun s₁ ⟨k₁, U₁, lt₁, e₁⟩ => ?_)
  have hw₁ := hw.of_rk k₁
  have v₁ : ∀ {i}, i < 45 → i ≠ QY → sv c base s₁ i = sv c base s i := fun hi h₁ =>
    sv_unch U₁ h7 hn hi (apart_callW h7 hi h₁)
  have normal : Fin.ofNat c.C.p (sv c base s₁ QY) = toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC) :=
    toM_one_mul hpR (by rw [e₁, hOne])
  have normalVal : sv c base s₁ QY = (toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC)).val := by
    simpa only [Fin.val_ofNat, Nat.mod_eq_of_lt lt₁] using congrArg Fin.val normal
  -- `W0 = 0 - QY`.
  refine WP.seq (WP.mono (slSub_ok hc.fp hc.fpk hc.fpm h7 hw₁ (o := W0) (a := ZERO) (b := QY)
    (by decide) (by decide) (by decide) (by rw [v₁ (by decide) (by decide), hZero]; omega_using [hp3]) lt₁)
    fun s₂ ⟨k₂, U₂, e₂⟩ => ?_)
  have hw₂ := hw₁.of_rk k₂
  have v₂ : ∀ {i}, i < 45 → i ≠ W0 → sv c base s₂ i = sv c base s₁ i := fun hi h₁ =>
    sv_unch U₂ h7 hn hi (apart_callW h7 hi h₁)
  have y₂ : sv c base s₂ QY = sv c base s₁ QY := v₂ (by decide) (by decide)
  have zero₁ : sv c base s₁ ZERO = 0 := (v₁ (by decide) (by decide)).trans hZero
  have negLt : sv c base s₂ W0 < c.C.p := by rw [e₂]; exact Nat.mod_lt _ (by omega_using [hp3])
  have negVal : Fin.ofNat c.C.p (sv c base s₂ W0) = -(Fin.ofNat c.C.p (sv c base s₁ QY)) := by
    apply Fin.ext
    simp only [Fin.val_ofNat, Fin.neg_def]
    rw [e₂, zero₁, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt lt₁]
  have hDw : ∀ w ∈ callW c QY ++ callW c W0, c.sl D + 8 ≤ w.1 ∨ w.1 + w.2 ≤ c.sl D := fun w hw' =>
    (apart_append (apart_callW h7 (i := D) (o := QY) (by decide) (by decide))
      (apart_callW h7 (i := D) (o := W0) (by decide) (by decide)) w hw').imp (fun h => by omega_using [h0, h]) id
  have tag₂ : word s₂.mem base (c.sl D) = word s.mem base (c.sl D) := (U₁.trans U₂).word hDw (by omega_using [hD])
  -- The parity's mask, and the selection.
  rw [WP.block_append_iff]
  refine WP.mono (parityMask_ok c hw₂.ws hw₂.at3 h0 (by omega_using [hY]) (by omega_using [hD])) fun s₃ ⟨mask₃, k₃, m₃⟩ => ?_
  refine WP.mono (sel_ok (decide ((word s₂.mem base (c.sl D)).toNat % 2 ≠ sv c base s₂ QY % 2)) c.n
    (k₃.ws hw₂.ws) (k₃.at hw₂.at3) (by rw [mask₃]; simp only [mask64, decide_eq_true_eq])
    (sl_al c _) (sl_al c _) (sl_al c _) (by omega_using [hY]) (by omega_using [hY]) (by omega_using [hW]) (Or.inl (Nat.le_refl _))
    (by have := sl_apart c (i := QY) (j := W0) (by decide); omega_using [this])) fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  rw [m₃] at e₄
  have K : Rk fnClob s s₄ := (k₁.trans k₂).trans ((k₃.rk (rs' := fnClob)).trans (k₄.rk (rs' := fnClob)))
  refine ⟨hw.of_rk K, K, ?_, ?_, ?_⟩
  · have U := (U₁.trans U₂).trans (show Unch base [(c.sl QY, 8 * c.n)] s₂.mem s₄.mem by rw [← m₃]; exact O₄.unch)
    refine U.mono fun w hw' => ?_
    simp only [callW, slW, List.map_cons, List.map_nil, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hw' ⊢
    grind
  · show wordsVal s₄.mem base (c.sl QY) c.n < c.C.p
    rw [e₄]
    split
    · exact negLt
    · rw [show wordsVal s₂.mem base (c.sl QY) c.n = sv c base s₂ QY from rfl, y₂]; exact lt₁
  · show Fin.ofNat c.C.p (wordsVal s₄.mem base (c.sl QY) c.n) = _
    rw [e₄, tag₂, show wordsVal s₂.mem base (c.sl QY) c.n = sv c base s₂ QY from rfl, y₂, normalVal]
    by_cases hm : (toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC)).val % 2 = (word s.mem base (c.sl D)).toNat % 2
    · simp only [hm.symm, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ite_false, ite_true]
      exact Fin.ext (Nat.mod_eq_of_lt (toM _ _ _).isLt)
    · have hm' : ¬ (word s.mem base (c.sl D)).toNat % 2 =
          (toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC)).val % 2 := fun h => hm h.symm
      simp only [hm, hm', ne_eq, not_false_eq_true, decide_true, ite_true, ite_false]
      rw [show wordsVal s₂.mem base (c.sl W0) c.n = sv c base s₂ W0 from rfl, negVal, normal]

end VG.Proof.EcKey.Compressed.PPC64LE

end

end

/-! ### `EcKey.Compressed.PPC64LE.RootPow`, which this module and modules that import it used -/

section

/-!
# SEC 1 point decompression on PPC64LE: powers of the right-hand side

`rootPower_ok`: `rootPower e j` writes `e` to `EXPP`, its bits to table `j`,
and `W2^e` (in Montgomery form) to `ACC`, by the signature's power
(`pow_ok`); `rootThree_ok`: the candidate `rhs^((p+1)/4)` for `p ≡ 3 mod 4`.
-/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Ecdsa.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont VG.Proof.Ecdsa.PPC64LE VG.Spec.Weierstrass
open VG.Impl.Ecdh.PPC64LE (W2)
open VG.Impl.EcKey.Compressed.PPC64LE (rootPow rootPower)

variable {c : Cfg}

theorem rootPowLay (hc : CfgOk c) {j : Nat} (hj : j < 3) : PowLayP (rootPow c j) c.n where
  acc := sl_below_own c hc.n10 (by decide)
  tmp := sl_below_own c hc.n10 (by decide)
  base := sl_below_own c hc.n10 (by decide)
  one := sl_below_own c hc.n10 (by decide)
  own := own_below_bits c hc.n10 j
  bits := bitsAt_le c hc.n10 hj
  nbits := by show 1 ≤ 64 * c.n ∧ 64 * c.n < 2 ^ 15; have := hc.n0; have := hc.n10; omega_arith
  acc_tmp := sl_apart c (by decide)
  acc_one := sl_apart c (by decide)
  base_acc := sl_apart c (by decide)
  base_tmp := sl_apart c (by decide)
  acc4 := sl_al c _
  tmp4 := sl_al c _
  one4 := sl_al c _

/-- What `rootPower e j` writes. -/
abbrev rootPowerW (c : Cfg) (j : Nat) : List (Nat × Nat) :=
  [(c.sl EXPP, 8 * c.n), (bitsAt c.n j, 64 * c.n), (c.sl ACC, 8 * c.n), (c.sl PT, 8 * c.n),
    (own c.n, 64 * c.n)]

/-- `ACC = W2^e`, in Montgomery form. -/
theorem rootPower_ok (hc : CfgOk c) {e j : Nat} (hj : j < 3) (he : e < 2 ^ (64 * c.n)) {base : Addr}
    {s : State} (hw : WsReg s base) (hB : sv c base s W2 < c.C.p)
    (hO : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p) :
    WP isa (rootPower c e j) s fun s' =>
      WsReg s' base ∧ Rk powClob s s' ∧ Unch base (rootPowerW c j) s.mem s'.mem ∧
      sv c base s' ACC < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s' ACC) = toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2) ^ e := by
  have h7 := hc.n10
  have hn := hw.nowrap
  have hE := sl_le c h7 (i := EXPP) (by decide)
  have hsz : size = 8192 := rfl
  change WP isa (.seq (.block (VG.Impl.Mont.PPC64LE.setConst c.n (c.sl EXPP) e))
    (.seq (bits (c.sl EXPP) (bitsAt c.n j) (8 * c.n)) (pow (rootPow c j) c.SP))) s _
  refine WP.seq (WP.mono (setConst_ok hw.ws hw.at3 (o := c.sl EXPP) (by omega_using [hE]) he) fun s₁ ⟨O₁, v₁, k₁⟩ => ?_)
  rw [← wordsVal_eq_val32] at v₁
  have hw₁ := hw.of_kp k₁
  refine WP.seq (WP.mono (tbl_bits_ok hc hw₁ (i := EXPP) (j := j) (by decide) hj) fun s₂ ⟨b₂, k₂, O₂⟩ => ?_)
  rw [v₁] at b₂
  have hw₂ := hw₁.of_kp k₂
  have keep₂ : ∀ {i}, i < 45 → i ≠ EXPP → sv c base s₂ i = sv c base s i := fun hi hiE =>
    (sv_unch O₂.unch h7 hn hi (apart_tbl h7 hi j)).trans
      (sv_unch O₁.unch h7 hn hi (fun w hw' => by
        rw [List.mem_singleton.mp hw']; have := sl_apart c hiE; dsimp only; omega_using [this]))
  refine WP.mono (pow_ok hc.fpk hc.fpm (modP hc) rfl (rootPowLay hc hj) (unitMod_pow_two hc.p_odd _) hw₂
    (by show sv c base s₂ W2 < _; rw [keep₂ (by decide) (by decide)]; exact hB)
    (by show sv c base s₂ ONEP = _; rw [keep₂ (by decide) (by decide)]; exact hO) b₂ he)
    fun s₃ ⟨k₃, U₃, lt₃, v₃⟩ => ⟨hw₂.of_rk k₃, ((k₁.rk (rs' := powClob)).trans (k₂.rk (rs' := powClob))).trans k₃,
      (O₁.unch.trans O₂.unch).trans U₃, lt₃, ?_⟩
  change toM c.C.p (2 ^ (64 * c.n)) (sv c base s₃ ACC) =
    toM c.C.p (2 ^ (64 * c.n)) (sv c base s₂ W2) ^ e at v₃
  rw [v₃, keep₂ (by decide) (by decide)]

/-- The candidate `rhs^((p+1)/4)`, for `p ≡ 3 mod 4`. -/
theorem rootThree_ok (hc : CfgOk c) (hp : c.C.p % 4 = 3) {base : Addr} {s : State} (hw : WsReg s base)
    (hB : sv c base s W2 < c.C.p) (hO : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p) :
    WP isa (Impl.EcKey.Compressed.PPC64LE.rootCandidate c) s fun s' =>
      WsReg s' base ∧ Rk powClob s s' ∧ Unch base (rootPowerW c 2) s.mem s'.mem ∧
      sv c base s' ACC < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s' ACC) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2) ^ ((c.C.p + 1) / 4) := by
  simp only [Impl.EcKey.Compressed.PPC64LE.rootCandidate, hp, ↓reduceIte]
  exact rootPower_ok hc (by decide) (by have := hc.p_lt; have := hc.p_ge; omega_arith) hw hB hO

end VG.Proof.EcKey.Compressed.PPC64LE

end

end

/-! ### `EcKey.Compressed.PPC64LE.Peer`, which only this module used -/

section

/-!
# SEC 1 point decompression on PPC64LE: reading the compressed key

`decompressTag_ok`: the tag (the byte `r12` points to) to `D`'s first word,
and the mask of it being `02` or `03`; `decompressPeer_ok`: `decompressPeer`
stores `R² mod p` and `b R mod p`, reads `x` into the hash's slot, the tag
into `D`, and ands into the flag the masks of the tag and of `x < p`, as
ECDH's `peer_ok` (`Proof/Ecdh/PPC64LE/Peer.lean`).
-/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Ecdsa.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont VG.Proof.Ecdsa.PPC64LE VG.Proof.Ecdh.PPC64LE VG.Spec.Weierstrass
open VG.Impl.Ecdh.PPC64LE (R2P BP)

/-- `-((((b | 1) ^ 3) - 1) >>> 63)` is the mask of `b ∈ {2, 3}`, for a byte
`b`. -/
theorem tag_mask (b : BitVec 8) :
    BitVec.ofNat 64 0 - (((b.setWidth 64 ||| BitVec.ofNat 64 1) ^^^ BitVec.ofNat 64 3) - BitVec.ofNat 64 1) >>> 63 =
      mask64 (b = 2 ∨ b = 3) := by
  revert b; decide +kernel

/-- The tag to `D`'s first word, and the mask `r5` of it being `02` or `03`. -/
theorem decompressTag_ok (c : Cfg) {s : State} {base : Addr} {size : Nat} (hs : Ws s base size)
    (h3 : At s base .r3 0) (hin : InRegions (s.rd ++ s.wr) (s.gpr .r12) 1) (hD : c.sl D + 8 ≤ size) :
    WP isa (.block (Impl.EcKey.Compressed.PPC64LE.decompressTag c)) s fun s' =>
      s'.gpr .r5 = mask64 (s.mem (s.gpr .r12) = 2 ∨ s.mem (s.gpr .r12) = 3) ∧ Kp [.r4, .r5] s s' ∧
      s'.mem = s.mem.writeW (off base (c.sl D)) ((s.mem (s.gpr .r12)).setWidth 64) := by
  simp only [Impl.EcKey.Compressed.PPC64LE.decompressTag]
  refine wp_step (exec_lbz (by decide) (by decide) (by rw [BitVec.add_zero]; exact hin)) ?_
  refine wp_step (std0_ok (hs.write _ _) (h3.write _) (by decide) (sl_al c D) hD) ?_
  refine wp_step (exec_li (by decide)) ?_
  refine wp_step exec_logic ?_
  refine wp_step (exec_li (by decide)) ?_
  refine wp_step exec_logic ?_
  refine wp_step (exec_subi (by decide) (by decide)) ?_
  refine wp_step (exec_lsr_d (by decide)) ?_
  refine wp_step (exec_li (by decide)) ?_
  refine wp_step exec_sub (WP.block_nil ⟨?_, ?_, ?_⟩)
  · simp only [write_gpr, ite_true, reduceCtorEq, ite_false, BitVec.add_zero, read_one]
    exact tag_mask _
  · exact ((((((((((Kp.write _ _ (by decide)).trans (Kp.store _ _ _)).trans (Kp.write _ _ (by decide))).trans
      (Kp.write _ _ (by decide))).trans (Kp.write _ _ (by decide))).trans (Kp.write _ _ (by decide))).trans
      (Kp.write _ _ (by decide))).trans (Kp.write _ _ (by decide))).trans (Kp.write _ _ (by decide))).trans
      (Kp.write _ _ (by decide)))
  · simp only [write_mem, write_gpr, ite_true, BitVec.add_zero, read_one]

theorem decompressPeer_eq (c : Cfg) : Impl.EcKey.Compressed.PPC64LE.decompressPeer c =
    (Impl.Ecdh.PPC64LE.Cfg.consts c).flatMap (fun (i, x) => VG.Impl.Mont.PPC64LE.setConst c.n (c.sl i) x) ++
    (.addi .r6 .r12 1 :: (loadBytes c.C.len c.n (c.sl E) .r6 ++
    (Impl.EcKey.Compressed.PPC64LE.decompressTag c ++ (c.andFlag ++
    Impl.Ecdh.PPC64LE.Cfg.checkLtP c (c.sl E))))) := by
  simp only [Impl.EcKey.Compressed.PPC64LE.decompressPeer, List.append_assoc, List.cons_append,
    List.nil_append]

variable {c : Cfg}

/-- The constants, the key's `x` and tag, and the checks of the tag and `x`,
for a key that `r12` points to. -/
theorem decompressPeer_ok (hc : CfgOk c) {base : Addr} {s : State} (hw : WsReg s base)
    (hqfit : (s.gpr .r12).toNat + (1 + c.C.len) ≤ 2 ^ 64)
    (hin : (⟨s.gpr .r12, 1 + c.C.len⟩ : Region) ∈ s.rd ++ s.wr)
    (hd : Region.Disjoint ⟨s.gpr .r12, 1 + c.C.len⟩ ⟨base, size⟩) (hmp : sv c base s MP = c.C.p) :
    WP isa (.block (Impl.EcKey.Compressed.PPC64LE.decompressPeer c)) s fun s' =>
      WsReg s' base ∧ Kp peerClob s s' ∧
      Unch base (slW c [R2P, BP, E, D] ++ [(c.sl FLAG, 8)]) s.mem s'.mem ∧
      sv c base s' R2P = c.R * c.R % c.C.p ∧ sv c base s' BP = c.mont c.C.b ∧
      sv c base s' E = ofBytes (Spec.Ecdsa.bytesAt s.mem (s.gpr .r12 + BitVec.ofNat 64 1) c.C.len) ∧
      word s'.mem base (c.sl D) = (s.mem (s.gpr .r12)).setWidth 64 ∧
      flagW c base s' = flagW c base s &&& mask64 (s.mem (s.gpr .r12) = 2 ∨ s.mem (s.gpr .r12) = 3) &&&
        mask64 (sv c base s' E < c.C.p) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hw.nowrap
  have hsz : size = 8192 := rfl
  have hpl := hc.p_lt
  have hp3 := hc.p_ge
  have hl8 := hc.len8
  have hlhi := hc.len_hi
  obtain hF : c.sl FLAG + 8 ≤ size := by have := sl_le c h7 (i := FLAG) (by decide); omega_arith
  obtain hR2 := sl_le c h7 (i := R2P) (by decide)
  obtain hB := sl_le c h7 (i := BP) (by decide)
  obtain hD := sl_le c h7 (i := D) (by decide)
  obtain hE := sl_le c h7 (i := E) (by decide)
  obtain hM := sl_le c h7 (i := MP) (by decide)
  generalize hqa : s.gpr .r12 = qa at hqfit hin hd ⊢
  rw [decompressPeer_eq]
  -- The constants.
  refine wp_append (WP.mono (setupConsts_ok hc (Impl.Ecdh.PPC64LE.Cfg.consts c) hw (fun ix hix => by
      simp only [Impl.Ecdh.PPC64LE.Cfg.consts, List.mem_cons, List.not_mem_nil, or_false] at hix
      rcases hix with rfl | rfl
      · exact ⟨show R2P < 45 by decide, Nat.lt_trans (Nat.mod_lt _ (by omega_arith)) hpl⟩
      · exact ⟨show BP < 45 by decide, Nat.lt_trans (Nat.mod_lt _ (by omega_arith)) hpl⟩)
      (show [R2P, BP].Nodup by decide))
    fun s₁ ⟨e₁, k₁, U₁⟩ => ?_)
  obtain hw₁ := hw.of_kp k₁
  have U₁' : Unch base (slW c [R2P, BP]) s.mem s₁.mem := U₁
  -- `public + 1`
  refine wp_step (exec_addi (by decide) (by decide)) ?_
  obtain k₂ : Kp [.r6, .r11] s (s₁.write .r6 (s₁.gpr .r12 + BitVec.ofNat 64 1)) :=
    (k₁.mono (by decide)).trans (Kp.write _ _ (by decide))
  obtain hq₁ : s₁.gpr .r12 = qa := by rw [k₁.gpr _ (by decide), hqa]
  obtain hrw : ∀ {t : State} {rs : List Reg}, Kp rs s t → t.rd ++ t.wr = s.rd ++ s.wr := fun K => by
    rw [K.rd, K.wr]
  obtain O₁ : Outside base 0 4096 s.mem s₁.mem := U₁'.outside fun w hw => by
    simp only [slW, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl <;> exact ⟨Nat.zero_le _, by dsimp only; omega_arith⟩
  obtain hfit₁ : (qa + BitVec.ofNat 64 1).toNat + c.C.len ≤ 2 ^ 64 := by
    rw [Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (show 1 < 2 ^ 64 by decide), Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith
  -- `x`
  refine wp_append (WP.mono (setupLoad_ok hc (s := s) (i := E) (src := .r6) (p := qa + BitVec.ofNat 64 1)
    (hw₁.of_kp (Kp.write _ (d := .r6) (rs := [.r6]) _ (by decide))) (by decide) (by decide)
    (by simp only [write_gpr, ite_true, hq₁]) hfit₁
    (fun e he => ⟨_, by rw [hrw k₂]; exact hin, by
      rw [Offset.add_add]; exact Offset.contains_base qa (by omega_arith) (by omega_arith)⟩)
    (hd.sub_left (Offset.sub_base qa (by omega_arith))) (by simp only [write_mem]; exact O₁))
    fun s₃ ⟨e₃, k₃, O₃⟩ => ?_)
  obtain K₃ : Kp [.r6, .r8, .r9, .r11] s s₃ :=
    (k₂.mono (by decide)).trans (k₃.mono (by decide))
  obtain hw₃ := hw.of_kp K₃
  obtain hq₃ : s₃.gpr .r12 = qa := by rw [K₃.gpr _ (by decide), hqa]
  obtain O₃' : Outside base 0 size s.mem s₃.mem :=
    (O₁.mono (Nat.le_refl _) (by omega_arith)).trans (O₃.mono (Nat.zero_le _) (by omega_arith))
  -- the tag
  refine wp_append (WP.mono (decompressTag_ok c hw₃.ws hw₃.at3
    ⟨_, by rw [hrw K₃]; exact hin, by
      have := Offset.contains_base qa (d := 0) (n := 1) (k := 1 + c.C.len) (by omega_arith) (by omega_arith)
      rw [BitVec.add_zero] at this; rw [hq₃]; exact this⟩ (by omega_arith)) fun s₄ ⟨m₄, k₄, h₄⟩ => ?_)
  rw [hq₃] at m₄ h₄
  obtain hw₄ := hw₃.of_kp k₄
  obtain lead₃ : s₃.mem qa = s.mem qa := by
    have := keep_of_disjoint' O₃' hd (by omega_arith) (i := 0) (by omega_arith) (by omega_arith)
    rwa [BitVec.add_zero] at this
  rw [lead₃] at m₄ h₄
  obtain O₄ : Outside base (c.sl D) 8 s₃.mem s₄.mem := by rw [h₄]; exact writeW_outside _ _ _ (by omega_arith)
  -- the flag `&=` the tag's mask
  refine wp_append (WP.mono (andFlag_ok c hw₄.ws hw₄.at3 hF) fun s₅ ⟨f₅, k₅, m₅⟩ => ?_)
  rw [m₄] at f₅
  obtain hw₅ := hw₄.of_kp k₅
  obtain O₅ : Outside base (c.sl FLAG) 8 s₄.mem s₅.mem := by rw [m₅]; exact writeW_outside _ _ _ (by omega_arith)
  -- `x < p`
  refine WP.mono (checkLtP_ok c hw₅.ws hw₅.at3 (by omega_arith) (by omega_arith) hF) fun s₆ ⟨f₆, k₆, O₆⟩ => ?_
  -- The slots.
  obtain U₃₆ : Unch base ([(c.sl D, 8)] ++ [(c.sl FLAG, 8)] ++ [(c.sl FLAG, 8)]) s₃.mem s₆.mem :=
    (O₄.unch.trans O₅.unch).trans O₆.unch
  obtain apDF : ∀ {i}, i < 45 → i ≠ FLAG → i ≠ D →
      ∀ w ∈ [(c.sl D, 8)] ++ [(c.sl FLAG, 8)] ++ [(c.sl FLAG, 8)],
        c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := fun hi hf hD' =>
    apart_append (apart_append (fun w hw => by
      rw [List.mem_singleton.mp hw]; have := sl_apart c hD'; dsimp only; omega_arith) (apart_flag h0 hf))
      (apart_flag h0 hf)
  obtain v₆ : ∀ {i}, i < 45 → i ≠ FLAG → i ≠ D → sv c base s₆ i = sv c base s₃ i := fun hi hf hD' =>
    sv_unch U₃₆ h7 hn hi (apDF hi hf hD')
  obtain v₃ : ∀ {i}, i < 45 → i ≠ E → sv c base s₃ i = sv c base s₁ i := fun hi hl =>
    sv_unch O₃.unch h7 hn hi (apart_slW (c := c) (l := [E]) (by simpa using hl))
  obtain v₁ : ∀ {i}, i < 45 → i ∉ [R2P, BP] → sv c base s₁ i = sv c base s i := fun hi hl =>
    sv_unch U₁' h7 hn hi (apart_slW (c := c) (l := [R2P, BP]) hl)
  obtain xE : sv c base s₆ E = ofBytes (Spec.Ecdsa.bytesAt s.mem (qa + BitVec.ofNat 64 1) c.C.len) := by
    rw [v₆ (by decide) (by decide) (by decide)]; exact e₃
  obtain hsD := sl_apart c (i := D) (j := FLAG) (by decide)
  refine ⟨hw₅.of_kp k₆, ?_, ?_, ?_, ?_, xE, ?_, ?_⟩
  · exact (((K₃.mono (by decide)).trans (k₄.mono (by decide))).trans (k₅.mono (by decide))).trans
      (k₆.mono (by decide))
  · refine ((U₁'.trans O₃.unch).trans U₃₆).cover fun w hw => ?_
    simp only [slW, List.map_cons, List.map_nil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      or_assoc] at hw
    obtain h8 : 8 ≤ 8 * c.n := by omega_arith
    rcases hw with h | h | h | h | h | h <;> subst h
    · exact ⟨_, by simp [slW], Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨_, by simp [slW], Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨_, by simp [slW], Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨(c.sl D, 8 * c.n), by simp [slW], Nat.le_refl _, by dsimp only; omega_arith⟩
    · exact ⟨_, by simp [slW], Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨_, by simp [slW], Nat.le_refl _, Nat.le_refl _⟩
  · rw [v₆ (by decide) (by decide) (by decide), v₃ (by decide) (by decide)]
    exact e₁ (R2P, c.R * c.R % c.C.p) List.mem_cons_self
  · rw [v₆ (by decide) (by decide) (by decide), v₃ (by decide) (by decide)]
    exact e₁ (BP, c.mont c.C.b) (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  · have U₄₆ : Unch base ([(c.sl FLAG, 8)] ++ [(c.sl FLAG, 8)]) s₄.mem s₆.mem := O₅.unch.trans O₆.unch
    rw [U₄₆.word (fun w hw => by
      simp only [List.mem_append, List.mem_singleton, or_self] at hw; subst hw; dsimp only; omega_arith) (by omega_arith),
      h₄, word_writeW_self]
  · have mp₅ : wordsVal s₅.mem base (c.sl MP) c.n = c.C.p := by
      rw [sv_unch O₅.unch h7 hn (i := MP) (by decide) (apart_flag h0 (by decide)),
        sv_unch O₄.unch h7 hn (i := MP) (by decide) (fun w hw => by
          rw [List.mem_singleton.mp hw]; have := sl_apart c (i := MP) (j := D) (by decide); dsimp only; omega_arith)]
      exact (v₃ (by decide) (by decide)).trans ((v₁ (by decide) (by decide)).trans hmp)
    obtain e₅ : wordsVal s₅.mem base (c.sl E) c.n = sv c base s₆ E :=
      (sv_unch O₆.unch h7 hn (i := E) (by decide) (apart_flag h0 (by decide))).symm
    obtain hFl := sl_le c h7 (i := FLAG) (by decide)
    obtain fl₄ : flagW c base s₄ = flagW c base s := by
      obtain ap : ∀ w ∈ slW c [R2P, BP] ++ [(c.sl E, 8 * c.n)] ++ [(c.sl D, 8)],
          c.sl FLAG + 8 ≤ w.1 ∨ w.1 + w.2 ≤ c.sl FLAG := fun w hw => by
        simp only [slW, List.map_cons, List.map_nil, List.mem_append, List.mem_cons, List.not_mem_nil,
          or_false, or_assoc] at hw
        rcases hw with h | h | h | h <;> subst h <;> dsimp only
        · have := sl_lt c (i := R2P) (j := FLAG) (by decide); omega_arith
        · have := sl_lt c (i := BP) (j := FLAG) (by decide); omega_arith
        · have := sl_lt c (i := E) (j := FLAG) (by decide); omega_arith
        · have := sl_lt c (i := D) (j := FLAG) (by decide); omega_arith
      exact ((U₁'.trans O₃.unch).trans O₄.unch).word ap (by omega_arith)
    rw [f₆, f₅, fl₄, e₅, mp₅]

end VG.Proof.EcKey.Compressed.PPC64LE

end

end

/-! ### `EcKey.Compressed.PPC64LE.Check`, which only this module used -/

section

/-!
# SEC 1 point decompression on PPC64LE: the checks of the root

`checkRoot_ok`: `checkRoot` computes `y² - rhs` (`checkPoly_ok`) and ands
into the flag the masks of it being zero and of `y`'s parity being the
tag's.
-/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Ecdsa.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont VG.Proof.Ecdsa.PPC64LE VG.Spec.Weierstrass VG.Proof.Ecdh.PPC64LE
open VG.Impl.Ecdh.PPC64LE (QY QYM R2P W1 W2 W3)

variable {c : Cfg}

theorem invert_mask (P : Prop) [Decidable P] :
    BitVec.ofNat 64 0 - (mask64 P + BitVec.ofNat 64 1) = mask64 ¬P := by
  by_cases h : P <;> simp only [mask64, h, not_true, not_false_eq_true, ite_true, ite_false] <;> decide

/-- The mask `r5` of `r10`'s mask being clear. -/
theorem invertMask_ok {s : State} {P : Prop} [Decidable P] (h : s.gpr .r10 = mask64 P) :
    WP isa (.block Impl.EcKey.Compressed.PPC64LE.invertMask) s fun s' =>
      s'.gpr .r5 = mask64 ¬P ∧ Kp [.r4, .r5] s s' ∧ s'.mem = s.mem := by
  simp only [Impl.EcKey.Compressed.PPC64LE.invertMask]
  refine wp_step (exec_addi (by decide) (by decide)) ?_
  refine wp_step (exec_li (by decide)) ?_
  refine wp_step exec_sub (WP.block_nil ⟨?_, ?_, ?_⟩)
  · simp only [write_gpr, ite_true, reduceCtorEq, ite_false, h]; exact invert_mask P
  · exact ((Kp.write _ _ (by decide)).trans (Kp.write _ _ (by decide))).trans (Kp.write _ _ (by decide))
  · simp only [write_mem]

/-- What `checkRoot` writes. -/
abbrev checkRootW (c : Cfg) : List (Nat × Nat) := checkW c ++ [(c.sl FLAG, 8)]

/-- The checks of `QY`: `y² = rhs` and `y`'s parity the tag's, anded into
the flag. -/
theorem checkRoot_ok (hc : CfgOk c) {base : Addr} {s : State} (hw : WsReg s base)
    (hy : sv c base s QY < c.C.p) (hr : sv c base s W2 < c.C.p) (hr2 : sv c base s R2P = c.R * c.R % c.C.p)
    {P : Prop} [Decidable P] (hf : flagW c base s = mask64 P) :
    WP isa (Impl.EcKey.Compressed.PPC64LE.checkRoot c) s fun s' =>
      WsReg s' base ∧ Rk fnClob s s' ∧ Unch base (checkRootW c) s.mem s'.mem ∧
      flagW c base s' = mask64
        ((P ∧ Fin.ofNat c.C.p (sv c base s QY) * Fin.ofNat c.C.p (sv c base s QY) =
          toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2)) ∧
          sv c base s QY % 2 = (word s.mem base (c.sl D)).toNat % 2) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hw.nowrap
  have hsz : size = 8192 := rfl
  obtain hF := sl_le c h7 (i := FLAG) (by decide)
  obtain hW := sl_le c h7 (i := W3) (by decide)
  obtain hY := sl_le c h7 (i := QY) (by decide)
  obtain hD := sl_le c h7 (i := D) (by decide)
  change WP isa (.seq (fprog c.SP (Impl.EcKey.Compressed.PPC64LE.checkRootOps c))
    (.block (Impl.Ecdh.PPC64LE.Cfg.checkZero c (c.sl W3) ++ (Impl.EcKey.Compressed.PPC64LE.parityMask c ++
      (Impl.EcKey.Compressed.PPC64LE.invertMask ++ c.andFlag))))) s _
  refine WP.seq (WP.mono (checkPoly_ok hc hw hy hr hr2) fun s₁ ⟨hw₁, k₁, U₁, lt₁, v₁⟩ => ?_)
  obtain ap₁ : ∀ {i}, i < 45 → i ∉ [QYM, W1, W3] →
      ∀ w ∈ checkW c, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := fun hi hl =>
    apart_append (apart_slW hl) (apart_own h7 hi)
  obtain flag₁ : flagW c base s₁ = mask64 P := by
    rw [flagW, U₁.word (fun w hw' => (ap₁ (i := FLAG) (by decide) (by decide) w hw').imp (fun h => by omega_using [h0, h]) id)
      (by omega_using [hF]), ← flagW, hf]
  obtain hz : sv c base s₁ W3 = 0 ↔
      Fin.ofNat c.C.p (sv c base s QY) * Fin.ofNat c.C.p (sv c base s QY) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2) := by
    rw [← toM_eq_zero_iff (unitMod_pow_two hc.p_odd (64 * c.n)) lt₁, v₁]
    constructor <;> intro h <;> grind
  obtain y₁ : sv c base s₁ QY = sv c base s QY := sv_unch U₁ h7 hn (by decide) (ap₁ (by decide) (by decide))
  obtain d₁ : word s₁.mem base (c.sl D) = word s.mem base (c.sl D) :=
    U₁.word (fun w hw' => (ap₁ (i := D) (by decide) (by decide) w hw').imp (fun h => by omega_using [h0, h]) id) (by omega_using [hD])
  rw [WP.block_append_iff]
  refine WP.mono (checkZero_ok c hw₁.ws hw₁.at3 (sl_al c W3) h0 (by omega_using [hW]) (by omega_using [hF])) fun s₂ ⟨f₂, k₂, O₂⟩ => ?_
  obtain y₂ : sv c base s₂ QY = sv c base s QY :=
    (sv_unch O₂.unch h7 hn (by decide) (apart_flag h0 (by decide))).trans y₁
  obtain d₂ : word s₂.mem base (c.sl D) = word s.mem base (c.sl D) :=
    (O₂.unch.word (fun w hw' => by
      rw [List.mem_singleton.mp hw']; have := sl_lt c (i := D) (j := FLAG) (by decide); dsimp only; omega_using [h0, this])
      (by omega_using [hD])).trans d₁
  obtain hw₂ := hw₁.of_kp k₂
  rw [WP.block_append_iff]
  refine WP.mono (parityMask_ok c hw₂.ws hw₂.at3 h0 (by omega_using [hY]) (by omega_using [hD])) fun s₃ ⟨mask₃, k₃, m₃⟩ => ?_
  rw [y₂, d₂] at mask₃
  rw [WP.block_append_iff]
  refine WP.mono (invertMask_ok mask₃) fun s₄ ⟨mask₄, k₄, m₄⟩ => ?_
  obtain hw₄ := (hw₂.of_kp k₃).of_kp k₄
  refine WP.mono (andFlag_ok c hw₄.ws hw₄.at3 (by omega_using [hF])) fun s₅ ⟨flag₅, k₅, m₅⟩ => ?_
  obtain fl₄ : flagW c base s₄ = flagW c base s₂ := by simp only [flagW, m₄, m₃]
  refine ⟨hw₄.of_kp k₅, k₁.trans ((((k₂.rk (rs' := fnClob)).trans (k₃.rk (rs' := fnClob))).trans
    (k₄.rk (rs' := fnClob))).trans (k₅.rk (rs' := fnClob))), ?_, ?_⟩
  · have O₅ : Outside base (c.sl FLAG) 8 s₄.mem s₅.mem := by rw [m₅]; exact writeW_outside _ _ _ (by omega_using [hF])
    obtain U₂₅ : Unch base [(c.sl FLAG, 8)] s₂.mem s₅.mem := by
      have := O₅.unch; rw [m₄, m₃] at this; exact this
    exact (U₁.trans (O₂.unch.trans U₂₅ |>.mono fun w hw' => by
      simp only [List.mem_append, List.mem_singleton, or_self] at hw'; exact List.mem_singleton.mpr hw'))
  · have key : ((P ∧ wordsVal s₁.mem base (c.sl W3) c.n = 0) ∧
        ¬((word s.mem base (c.sl D)).toNat % 2 ≠ sv c base s QY % 2)) ↔
        ((P ∧ Fin.ofNat c.C.p (sv c base s QY) * Fin.ofNat c.C.p (sv c base s QY) =
          toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2)) ∧
          sv c base s QY % 2 = (word s.mem base (c.sl D)).toNat % 2) := by
      rw [show wordsVal s₁.mem base (c.sl W3) c.n = sv c base s₁ W3 from rfl, hz]
      constructor
      · rintro ⟨⟨a, b⟩, h⟩; exact ⟨⟨a, b⟩, by omega_using [h]⟩
      · rintro ⟨⟨a, b⟩, h⟩; exact ⟨⟨a, b⟩, by omega_using [h]⟩
    rw [flag₅, fl₄, f₂, flag₁, mask₄, mask64_and, mask64_and]
    simp only [mask64, key]

end VG.Proof.EcKey.Compressed.PPC64LE

end

end

/-!
# SEC 1 point decompression on PPC64LE: the whole function

`decompress_ok`: `decompress` writes `04 ‖ x ‖ y`, for `y` the root of the
tag's parity that a square-root method `root` gives (`CandidateCorrect`:
the code's candidate computes it), or zeros, and returns 1 or 0, restoring
the callee-saved registers and `lr`: the signature's setup, the key's
parsing (`decompressPeer_ok`), `x³ + a x + b` (`rhs_ok`), the candidate,
the root of the tag's parity (`selectRoot_ok`), its checks
(`checkRoot_ok`), and the public key's result (`pkFinishWith_ok`).
`decompress_correct`: the same, against `decompressContract`.
-/

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/PPC64LE/DecompressContract.lean`, which only this module imported.
section

/-!
# SEC 1 point decompression on PPC64LE: the contract the proof is written against

`vg_ec_<curve>_decompress_public_key(out, public, scratch)`, with the
arguments in `r3`–`r5` and the result in `r3` (ELFv2), for any curve, whose
result is the functional decoder's (`Impl.EcKey.Compressed.decode`) with a
square root `root`; `decompress_implies` moves it to
`Spec.EcKey.Instance.decompressPublicKeyContract` by the root's facts
(`RootFacts`).
-/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.PPC64LE

open VG VG.PPC64LE

def decompressContract (C : Spec.Weierstrass.Curve)
    (root : Spec.Weierstrass.Fe C → Spec.Weierstrass.Fe C) : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .r3, 2 * C.len + 1⟩
    let pk : Region := ⟨s.gpr .r4, C.len + 1⟩
    let ws : Region := ⟨s.gpr .r5, 8192⟩
    s.rd = [pk] ∧ s.wr = [out, ws] ∧
      pk.Disjoint out ∧ pk.Disjoint ws ∧ out.Disjoint ws ∧
      (s.gpr .r3).toNat + (2 * C.len + 1) ≤ 2 ^ 64 ∧
      (s.gpr .r4).toNat + (C.len + 1) ≤ 2 ^ 64 ∧
      (s.gpr .r5).toNat + 8192 ≤ 2 ^ 64
  post s s' :=
    match Impl.EcKey.Compressed.decode C root (Spec.EcKey.bytesAt s.mem (s.gpr .r4) (C.len + 1)) with
    | some Q => s'.gpr .r3 = 1 ∧
        Spec.EcKey.bytesAt s'.mem (s.gpr .r3) (2 * C.len + 1) = Spec.EcKey.encodePoint Q
    | none => s'.gpr .r3 = 0 ∧
        Spec.EcKey.bytesAt s'.mem (s.gpr .r3) (2 * C.len + 1) = List.replicate (2 * C.len + 1) 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
    s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5

theorem decompress_implies (I : Spec.EcKey.Instance)
    (root : Spec.Weierstrass.Fe I.curve → Spec.Weierstrass.Fe I.curve)
    (hf : RootFacts root)
    (hsat : ∃ s, (I.decompressPublicKeyContract abi 0).pre s) :
    (decompressContract I.curve root).Implies (I.decompressPublicKeyContract abi 0) where
  pre := by
    sig_implies_pre [Spec.EcKey.Instance.decompressPublicKeyContract,
      Spec.EcKey.Instance.decompressPublicKeySig, Spec.EcKey.scratchWords,
      abi, argRegs, decompressContract]
  post := by
    intro s s' _ h
    sig_post [Spec.EcKey.Instance.decompressPublicKeyContract,
      Spec.EcKey.Instance.decompressPublicKeySig, Spec.EcKey.scratchWords,
      abi, argRegs, decompressContract]
    cases he : Impl.EcKey.Compressed.decode I.curve root
        (Spec.EcKey.bytesAt s.mem (s.gpr .r4) (I.curve.len + 1)) with
    | none =>
      simp only [decompressContract, he] at h
      exact Or.inr ⟨by rw [h.1]; rfl, (decode_none_iff hf _).mp he, h.2⟩
    | some Q =>
      simp only [decompressContract, he] at h
      exact Or.inl ⟨by rw [h.1]; rfl, Q, decode_sound he, h.2⟩
  pub := by
    sig_implies_pub [Spec.EcKey.Instance.decompressPublicKeyContract,
      Spec.EcKey.Instance.decompressPublicKeySig, Spec.EcKey.scratchWords,
      abi, argRegs, decompressContract]
  sat := hsat

/-- A state satisfying the precondition, for encodings of `len` bytes. -/
def decompressSatState (len : Nat) : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x8000 | _ => 0
  lr := 0
  sp := 0x20000
  mem _ := 0
  rd := [⟨0x2000, len + 1⟩]
  wr := [⟨0x1000, 2 * len + 1⟩, ⟨0x8000, 8192⟩]

end VG.Proof.EcKey.Compressed.PPC64LE
end

end

@[expose] public section

namespace VG.Proof.EcKey.Compressed.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Ecdsa.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont VG.Proof.Ecdsa.PPC64LE VG.Proof.Ecdh.PPC64LE VG.Spec.Weierstrass
open VG.Impl.Ecdh.PPC64LE (QY R2P BP QXM QYM W0 W1 W2 W3)
open VG.Impl.EcKey.Compressed.PPC64LE (args)
open VG.Impl.EcKey.Compressed (chooseRoot)

variable {c : Cfg}

/-! ## The square root's candidate -/

/-- The slots the candidate may write. -/
abbrev candSlots : List Nat := [EXPP, ACC, PT, T0, T1, T3, T4, T5, W0]

/-- What the candidate may write: its slots, the tables of `p - 2` and
`n - 2`, and the functions' own working space. -/
abbrev candW (c : Cfg) : List (Nat × Nat) :=
  slW c candSlots ++ [(bitsAt c.n 1, 64 * c.n), (bitsAt c.n 2, 64 * c.n), (own c.n, 64 * c.n)]

/-- The code's candidate computes `root` of what `W2` holds, in Montgomery
form, writing only `candW`. -/
def CandidateCorrect (c : Cfg) (root : Fe c.C → Fe c.C) : Prop :=
  ∀ (base : Addr) (s : State), WsReg s base → sv c base s W2 < c.C.p →
    sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p →
    WP isa (Impl.EcKey.Compressed.PPC64LE.rootCandidate c) s fun s' =>
      WsReg s' base ∧ Rk powClob s s' ∧ Unch base (candW c) s.mem s'.mem ∧ sv c base s' ACC < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s' ACC) = root (toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2))

theorem candW_fixed (h7 : c.n < 10) : FixedOk c (candW c) :=
  (fixedOk_slW (by decide)).append (fun w hw => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact fixedOk_tbl h7 1 _ (List.mem_singleton_self _)
    · exact fixedOk_tbl h7 2 _ (List.mem_singleton_self _)
    · exact fixedOk_own h7 _ (List.mem_singleton_self _))

theorem candW_le (h7 : c.n < 10) : ∀ w ∈ candW c, w.1 + w.2 ≤ size := by
  have hsz : size = 8192 := rfl
  have := own_below_bits c h7 0
  have := bitsAt_le c h7 (j := 0) (by decide)
  have := bitsAt_le c h7 (j := 1) (by decide)
  have := bitsAt_le c h7 (j := 2) (by decide)
  refine le_append (fun w hw => ?_) (fun w hw => ?_)
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    obtain hl : ∀ i ∈ candSlots, i < 45 := by decide
    have := sl_le c h7 (hl i hi)
    dsimp only; omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl <;> (dsimp only; omega_arith)

theorem apart_candW (h7 : c.n < 10) {i : Nat} (hi : i < 45) (hw : i ∉ candSlots) :
    ∀ w ∈ candW c, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i :=
  apart_append (apart_slW hw) (fun w h => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl
    · exact apart_tbl h7 hi 1 _ (List.mem_singleton_self _)
    · exact apart_tbl h7 hi 2 _ (List.mem_singleton_self _)
    · exact apart_own h7 hi _ (List.mem_singleton_self _))

/-- For `p ≡ 3 mod 4`, the candidate is `rhs^((p+1)/4)`. -/
theorem candidateThree_correct (hc : CfgOk c) (hp : c.C.p % 4 = 3) :
    CandidateCorrect c Impl.EcKey.Compressed.rootThreeModFour := fun base s hw hB hO =>
  WP.mono (rootThree_ok hc hp hw hB hO) fun s' ⟨hw', k, U, lt, v⟩ =>
    ⟨hw', k, U.mono (fun w hw'' => by
      simp only [rootPowerW, List.mem_cons, List.not_mem_nil, or_false] at hw''
      rcases hw'' with rfl | rfl | rfl | rfl | rfl <;> simp [candW, slW]), lt,
      by rw [v]; simp only [Impl.EcKey.Compressed.rootThreeModFour, pow_eq_npow]⟩

/-! ## The key and its point -/

/-- The key's tag and `x`. -/
abbrev keyTag (s : State) : Byte := s.mem (s.gpr .r4)

/-- `x³ + a x + b`, for the key's `x`. -/
def keyRhs (c : Cfg) (s : State) : Fe c.C :=
  let x := Fin.ofNat c.C.p (keyX c s)
  x * x * x + Fin.ofNat c.C.p c.C.a * x + Fin.ofNat c.C.p c.C.b

/-- The root of the tag's parity, if there is one. -/
def keyRoot (c : Cfg) (root : Fe c.C → Fe c.C) (s : State) : Fe c.C :=
  chooseRoot (root (keyRhs c s)) ((keyTag s).toNat % 2)

/-- The code accepts the key: its tag `02` or `03`, `x < p`, and the root
squares to `x³ + a x + b` and has the tag's parity. -/
def DAccept (c : Cfg) (root : Fe c.C → Fe c.C) (s : State) : Prop :=
  ((keyTag s = 2 ∨ keyTag s = 3) ∧ keyX c s < c.C.p) ∧
    (keyRoot c root s * keyRoot c root s = keyRhs c s ∧ (keyRoot c root s).val % 2 = (keyTag s).toNat % 2)

instance (c : Cfg) (root : Fe c.C → Fe c.C) (s : State) : Decidable (DAccept c root s) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The arguments: `out` (`1 + 2 len` bytes), `public` (`1 + len` bytes)
and `scratch`, readable and writable as the contract says and apart from
each other as it says. -/
structure DPre (c : Cfg) (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .r4, 1 + c.C.len⟩]
  wr : s.wr = [⟨s.gpr .r3, 1 + 2 * c.C.len⟩, ⟨s.gpr .r5, size⟩]
  pk_sc : Region.Disjoint ⟨s.gpr .r4, 1 + c.C.len⟩ ⟨s.gpr .r5, size⟩
  out_sc : Region.Disjoint ⟨s.gpr .r3, 1 + 2 * c.C.len⟩ ⟨s.gpr .r5, size⟩
  out_fit : (s.gpr .r3).toNat + (1 + 2 * c.C.len) ≤ 2 ^ 64
  pk_fit : (s.gpr .r4).toNat + (1 + c.C.len) ≤ 2 ^ 64
  sc_fit : (s.gpr .r5).toNat + size ≤ 2 ^ 64

theorem DPre.setup {s : State} (hp : DPre c s) : SetupPre c args (s.write .r12 (s.gpr .r4)) := by
  obtain hr12 : (s.write .r12 (s.gpr .r4)).gpr .r12 = s.gpr .r4 := by simp only [write_gpr, ite_true]
  obtain hr5 : (s.write .r12 (s.gpr .r4)).gpr .r5 = s.gpr .r5 := by
    simp only [write_gpr, reduceCtorEq, ite_false]
  obtain hlen : c.C.len ≤ 1 + c.C.len := by omega_arith
  obtain hin : ∀ e, e + 8 ≤ c.C.len → InRegions ((s.write .r12 (s.gpr .r4)).rd ++ (s.write .r12 (s.gpr .r4)).wr)
      ((s.write .r12 (s.gpr .r4)).gpr .r12 + BitVec.ofNat 64 e) 8 := fun e he => by
    rw [hr12, write_rd, write_wr]
    exact inRegions_words (len := 1 + c.C.len) (by rw [hp.rd]; simp) (by have := hp.pk_fit; omega_arith) e (by omega_arith)
  obtain hd : Region.Disjoint ⟨(s.write .r12 (s.gpr .r4)).gpr .r12, c.C.len⟩
      ⟨(s.write .r12 (s.gpr .r4)).gpr .r5, size⟩ := by
    rw [hr12, hr5]; exact hp.pk_sc.sub_left (Region.sub_prefix hlen)
  obtain hf : ((s.write .r12 (s.gpr .r4)).gpr .r12).toNat + c.C.len ≤ 2 ^ 64 := by
    rw [hr12]; have := hp.pk_fit; omega_arith
  obtain hwr : (⟨(s.write .r12 (s.gpr .r4)).gpr .r5, size⟩ : Region) ∈ (s.write .r12 (s.gpr .r4)).wr := by
    rw [hr5, write_wr, hp.wr]; simp
  obtain hsf : ((s.write .r12 (s.gpr .r4)).gpr .r5).toNat + size ≤ 2 ^ 64 := by rw [hr5]; exact hp.sc_fit
  exact ⟨.inl rfl, by decide, by decide, by decide, by decide, hwr, hsf, hin, hin, hin, hd, hd, hd, hf, hf, hf⟩

theorem decompress_eq' (c : Cfg) : Impl.EcKey.Compressed.PPC64LE.decompress c =
    .seq (.block (mov .r12 .r4 :: c.setupWith args))
      (.seq (.block (Impl.EcKey.Compressed.PPC64LE.decompressPeer c))
      (.seq (fprog c.SP (Impl.EcKey.Compressed.PPC64LE.rhsOps c))
      (.seq (.seq (Impl.EcKey.Compressed.PPC64LE.rootCandidate c)
        (.seq (Impl.EcKey.Compressed.PPC64LE.selectRoot c) (Impl.EcKey.Compressed.PPC64LE.checkRoot c)))
      (.block (Impl.EcKey.Compressed.PPC64LE.decompressFinish c))))) := rfl

/-- `vg_ec_<curve>_decompress_public_key` writes the uncompressed key, or
zeros, and returns 1 or 0, restoring the callee-saved registers and `lr`. -/
theorem decompress_ok (hc : CfgOk c) {root : Fe c.C → Fe c.C} (hroot : CandidateCorrect c root)
    {s₀ : State} (hp : DPre c s₀) :
    WP isa (Impl.EcKey.Compressed.PPC64LE.decompress c) s₀ fun s' => CKeep s₀ s' ∧
      Spec.Ecdsa.bytesAt s'.mem (s₀.gpr .r3) (1 + 2 * c.C.len) =
        (if DAccept c root s₀ then 4 :: (toBytes c.C.len (keyX c s₀) ++ toBytes c.C.len (keyRoot c root s₀).val)
          else List.replicate (1 + 2 * c.C.len) 0) ∧
      s'.gpr .r3 = (if DAccept c root s₀ then 1 else 0) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hlhi := hc.len_hi
  have hl8 := hc.len8
  have hp3 := hc.p_ge
  have hsz : size = 8192 := rfl
  obtain hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  rw [decompress_eq']
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
  obtain hpsc : Region.Disjoint ⟨s₀.gpr .r4, 1 + c.C.len⟩ ⟨base, size⟩ := by rw [← hb]; exact hp.pk_sc
  -- The key.
  refine WP.seq (WP.mono (decompressPeer_ok hc S₂.ws
    (by rw [r12₂]; exact hp.pk_fit) (by rw [r12₂, S₂.rk.rd, S₂.rk.wr, write_rd, write_wr, hp.rd]; simp)
    (by rw [r12₂]; exact hpsc) S₂.fixed.mp) fun s₃ ⟨hw₃, k₃, U₃, r2₃, bp₃, x₃, d₃, f₃⟩ => ?_)
  rw [r12₂] at x₃ d₃ f₃
  obtain K₃ := S₂.toKeep.step h7 (k₃.rk (rs' := peerClob)) (hU := U₃)
    (hW := (fixedOk_slW (by decide)).append fixedOk_flag)
    (hWs := le_append (fun w hw => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      obtain hl₃ : ∀ i ∈ [R2P, BP, E, D], i < 45 := by decide
      have := sl_le c h7 (hl₃ i hi); dsimp only; omega_arith)
      (fun w hw => by
        rw [List.mem_singleton.mp hw]; have := sl_le c h7 (i := FLAG) (by decide); dsimp only; omega_arith))
  obtain hq0 : s₂.mem (s₀.gpr .r4) = keyTag s₀ := by
    have := keep_of_disjoint' W₂ hpsc (by omega_arith) (i := 0) (by omega_arith) (by omega_arith)
    rwa [BitVec.add_zero] at this
  obtain x₃' : sv c base s₃ E = keyX c s₀ := by
    rw [x₃, bytesAt_keep W₂ (hpsc.sub_left (Offset.sub_base _ (by omega_arith))) (by omega_arith) (by omega_arith)]
  rw [hq0] at d₃ f₃
  obtain hf₃ : flagW c base s₃ = mask64 ((keyTag s₀ = 2 ∨ keyTag s₀ = 3) ∧ keyX c s₀ < c.C.p) := by
    rw [f₃, S₂.flag, BitVec.allOnes_and, mask64_and, x₃']
  -- `x³ + a x + b`.
  refine WP.seq (WP.mono (rhs_ok hc K₃.ws r2₃ K₃.fixed.ap bp₃) fun s₄ ⟨hw₄, k₄, U₄, lt₄, v₄⟩ => ?_)
  obtain K₄ := K₃.step h7 k₄ (hU := U₄) (hW := (fixedOk_slW (by decide)).append (fixedOk_own h7))
    (hWs := le_append (fun w hw => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      obtain hl₄ : ∀ i ∈ [QXM, W1, W2, W3], i < 45 := by decide
      have := sl_le c h7 (hl₄ i hi); dsimp only; omega_arith)
      (fun w hw => by rw [List.mem_singleton.mp hw]; have := own_below_bits c h7 0; have := bitsAt_le c h7 (j := 0) (by decide); dsimp only; omega_arith))
  obtain e₄ : ∀ {i}, i < 45 → i ∉ [QXM, W1, W2, W3] → sv c base s₄ i = sv c base s₃ i := fun hi hl =>
    sv_unch U₄ h7 hn hi (apart_append (apart_slW hl) (apart_own h7 hi))
  obtain ew₄ : ∀ {i}, i < 45 → i ∉ [QXM, W1, W2, W3] → word s₄.mem base (c.sl i) = word s₃.mem base (c.sl i) :=
    fun hi hl => U₄.word (fun w hw => (apart_append (apart_slW hl) (apart_own h7 hi) w hw).imp
      (fun h => by omega_arith) id) (by have := sl_le c h7 hi; omega_arith)
  rw [x₃'] at v₄
  -- The candidate.
  refine WP.seq (WP.seq (WP.mono (hroot base s₄ K₄.ws lt₄ K₄.fixed.onep) fun s₅ ⟨hw₅, k₅, U₅, lt₅, v₅⟩ => ?_))
  obtain K₅ := K₄.step h7 k₅ (hU := U₅) (hW := candW_fixed h7) (hWs := candW_le h7)
  obtain e₅ : ∀ {i}, i < 45 → i ∉ candSlots → sv c base s₅ i = sv c base s₄ i := fun hi hl =>
    sv_unch U₅ h7 hn hi (apart_candW h7 hi hl)
  obtain ew₅ : ∀ {i}, i < 45 → i ∉ candSlots → word s₅.mem base (c.sl i) = word s₄.mem base (c.sl i) :=
    fun hi hl => U₅.word (fun w hw => (apart_candW h7 hi hl w hw).imp (fun h => by omega_arith) id)
      (by have := sl_le c h7 hi; omega_arith)
  rw [v₄] at v₅
  -- The root of the tag's parity.
  refine WP.seq (WP.mono (selectRoot_ok hc K₅.ws K₅.fixed.one K₅.fixed.zero) fun s₆ ⟨hw₆, k₆, U₆, lt₆, v₆⟩ => ?_)
  obtain K₆ := K₅.step h7 k₆ (hU := U₆) (hW := (fixedOk_slW (by decide)).append (fixedOk_own h7))
    (hWs := le_append (fun w hw => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      obtain hl₆ : ∀ i ∈ [QY, W0], i < 45 := by decide
      have := sl_le c h7 (hl₆ i hi); dsimp only; omega_arith)
      (fun w hw => by rw [List.mem_singleton.mp hw]; have := own_below_bits c h7 0; have := bitsAt_le c h7 (j := 0) (by decide); dsimp only; omega_arith))
  obtain e₆ : ∀ {i}, i < 45 → i ∉ [QY, W0] → sv c base s₆ i = sv c base s₅ i := fun hi hl =>
    sv_unch U₆ h7 hn hi (apart_append (apart_slW hl) (apart_own h7 hi))
  obtain ew₆ : ∀ {i}, i < 45 → i ∉ [QY, W0] → word s₆.mem base (c.sl i) = word s₅.mem base (c.sl i) :=
    fun hi hl => U₆.word (fun w hw => (apart_append (apart_slW hl) (apart_own h7 hi) w hw).imp
      (fun h => by omega_arith) id) (by have := sl_le c h7 hi; omega_arith)
  obtain tagD : word s₅.mem base (c.sl D) = (keyTag s₀).setWidth 64 := by
    rw [ew₅ (by decide) (by decide), ew₄ (by decide) (by decide), d₃]
  obtain tagN : (word s₅.mem base (c.sl D)).toNat = (keyTag s₀).toNat := by
    rw [tagD, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans (BitVec.isLt _) (by decide))]
  rw [v₅, tagN] at v₆
  have y₆ : Fin.ofNat c.C.p (sv c base s₆ QY) = keyRoot c root s₀ := v₆
  obtain yv₆ : sv c base s₆ QY = (keyRoot c root s₀).val := by
    simpa only [Fin.val_ofNat, Nat.mod_eq_of_lt lt₆] using congrArg Fin.val y₆
  -- The checks.
  obtain w2₆ : sv c base s₆ W2 = sv c base s₄ W2 :=
    (e₆ (by decide) (by decide)).trans (e₅ (by decide) (by decide))
  obtain r2₆ : sv c base s₆ R2P = c.R * c.R % c.C.p := by
    rw [e₆ (by decide) (by decide), e₅ (by decide) (by decide), e₄ (by decide) (by decide)]; exact r2₃
  obtain fl₆ : flagW c base s₆ = mask64 ((keyTag s₀ = 2 ∨ keyTag s₀ = 3) ∧ keyX c s₀ < c.C.p) := by
    rw [flagW, ew₆ (i := FLAG) (by decide) (by decide), ew₅ (by decide) (by decide),
      ew₄ (by decide) (by decide), ← flagW, hf₃]
  refine WP.mono (checkRoot_ok hc K₆.ws lt₆ (by rw [w2₆]; exact lt₄) r2₆ fl₆) fun s₇ ⟨hw₇, k₇, U₇, f₇⟩ => ?_
  obtain K₇ := K₆.step h7 k₇ (hU := U₇) (hW := ((fixedOk_slW (by decide)).append (fixedOk_own h7)).append fixedOk_flag)
    (hWs := le_append (le_append (fun w hw => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      obtain hl₇ : ∀ i ∈ [QYM, W1, W3], i < 45 := by decide
      have := sl_le c h7 (hl₇ i hi); dsimp only; omega_arith)
      (fun w hw => by rw [List.mem_singleton.mp hw]; have := own_below_bits c h7 0; have := bitsAt_le c h7 (j := 0) (by decide); dsimp only; omega_arith))
      (fun w hw => by rw [List.mem_singleton.mp hw]; have := sl_le c h7 (i := FLAG) (by decide); dsimp only; omega_arith))
  obtain e₇ : ∀ {i}, i < 45 → i ∉ [QYM, W1, W3] → i ≠ FLAG → sv c base s₇ i = sv c base s₆ i := fun hi hl hf =>
    sv_unch U₇ h7 hn hi (apart_append (apart_append (apart_slW hl) (apart_own h7 hi)) (apart_flag h0 hf))
  obtain hacc : flagW c base s₇ = mask64 (decide (DAccept c root s₀) = true) := by
    obtain hD₆ : (word s₆.mem base (c.sl D)).toNat = (keyTag s₀).toNat := by
      rw [ew₆ (by decide) (by decide), tagN]
    rw [f₇, y₆, w2₆, v₄, yv₆, hD₆]
    simp only [mask64, decide_eq_true_eq, DAccept, keyRhs, and_assoc]
  obtain h14 : s₇.gpr .r14 = s₀.gpr .r3 := by
    rw [K₇.r14]; simp only [write_gpr, reduceCtorEq, ite_false]
  obtain x₇ : sv c base s₇ E = keyX c s₀ := by
    rw [e₇ (by decide) (by decide) (by decide), e₆ (by decide) (by decide), e₅ (by decide) (by decide),
      e₄ (by decide) (by decide), x₃']
  obtain y₇ : sv c base s₇ QY = (keyRoot c root s₀).val := by
    rw [e₇ (by decide) (by decide) (by decide), yv₆]
  -- The result.
  refine WP.mono (VG.Proof.EcKey.PPC64LE.pkFinishWith_ok hc (x := E) (y := QY) (by decide) (by decide) K₇.ws h14
    hp.out_fit (by rw [K₇.rk.wr, write_wr, hp.wr]; simp) (by rw [← hb]; exact hp.out_sc) _ hacc)
    fun s' ⟨bytes, r3, lr, r14, r31, rk, _⟩ => ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro r hr
    have hsv := K₇.fixed.saved
    obtain hcases : ∀ r ∈ preserved, r = .r14 ∨ r = .r31 ∨
        (r ∉ [Reg.r0, .r3, .r4, .r5, .r6, .r10, .r14, .r31] ∧ r ∉ work) := by decide
    rcases hcases r hr with rfl | rfl | ⟨h₁, h₂⟩
    · rw [r14, hsv (.r14, 0) (by decide)]; simp only [write_gpr, reduceCtorEq, ite_false]
    · rw [r31, hsv (.r31, 8) (by decide)]; simp only [write_gpr, reduceCtorEq, ite_false]
    · have h12 : r ≠ .r12 := fun h => h₂ (by rw [h]; decide)
      rw [rk.gpr r h₁, K₇.rk.gpr r h₂]; simp only [write_gpr, h12, ite_false]
  · rw [rk.sp, K₇.rk.sp, write_sp]
  · rw [lr, K₇.fixed.savedLr, write_lr]
  · rw [bytes, x₇, y₇]
    by_cases hk : DAccept c root s₀ <;> simp [hk]
  · rw [r3]; by_cases hk : DAccept c root s₀ <;> simp [hk]

/-- The key's bytes: its tag, then `x`. -/
theorem key_bytes (m : Mem) (p : Addr) (L : Nat) :
    Spec.Ecdsa.bytesAt m p (L + 1) = m p :: Spec.Ecdsa.bytesAt m (p + BitVec.ofNat 64 1) L := by
  rw [Nat.add_comm L 1, bytesAt_add]
  simp only [Spec.Ecdsa.bytesAt, List.range_one, List.map_cons, List.map_nil, BitVec.add_zero,
    List.cons_append, List.nil_append]

theorem decompress_key (c : Cfg) (root : Fe c.C → Fe c.C) (s : State) :
    Impl.EcKey.Compressed.decode c.C root (Spec.EcKey.bytesAt s.mem (s.gpr .r4) (c.C.len + 1)) =
      if DAccept c root s then some (.affine (Fin.ofNat c.C.p (keyX c s)) (keyRoot c root s)) else none := by
  obtain hb := key_bytes s.mem (s.gpr .r4) c.C.len
  exact decode_checked_eq root (length_bytesAt _ _ _)
    (by change (Spec.Ecdsa.bytesAt _ _ _).head? = _; rw [hb]; rfl)
    (by change ofBytes ((Spec.Ecdsa.bytesAt _ _ _).drop 1) = _; rw [hb]; rfl)

theorem decompress_correct (c : Cfg) (hc : CfgOk c) (root : Fe c.C → Fe c.C) (hroot : CandidateCorrect c root)
    (s : State) (hs : (decompressContract c.C root).pre s) :
    ∃ t s', Exec isa (Impl.EcKey.Compressed.PPC64LE.decompress c) s t s' ∧
      abiPreserved s s' ∧ (decompressContract c.C root).post s s' := by
  obtain ⟨hrd, hwr, hpo, hpw, how, hfit, hpkfit, hwfit⟩ := hs
  obtain hp : DPre c s :=
    ⟨by rw [hrd, show c.C.len + 1 = 1 + c.C.len by omega_arith],
      by rw [hwr, show 2 * c.C.len + 1 = 1 + 2 * c.C.len by omega_arith],
      by simpa only [show c.C.len + 1 = 1 + c.C.len by omega_arith] using hpw,
      by simpa only [show 2 * c.C.len + 1 = 1 + 2 * c.C.len by omega_arith] using how,
      by omega_arith, by omega_arith, hwfit⟩
  obtain ⟨t, s', he, K, bytes, ret⟩ := decompress_ok hc hroot hp
  refine ⟨t, s', he, ⟨K.saved, K.sp, K.lr⟩, ?_⟩
  dsimp only [decompressContract]
  rw [decompress_key]
  change Spec.EcKey.bytesAt s'.mem (s.gpr .r3) (1 + 2 * c.C.len) = _ at bytes
  rw [show 1 + 2 * c.C.len = 2 * c.C.len + 1 by omega_arith] at bytes
  by_cases hk : DAccept c root s
  · rw [ite_eq_left hk] at bytes ret ⊢
    refine ⟨ret, ?_⟩
    rw [bytes]
    simp only [Spec.EcKey.encodePoint, Fin.val_ofNat, Nat.mod_eq_of_lt hk.1.2]
  · rw [ite_eq_right hk] at bytes ret ⊢
    exact ⟨ret, bytes⟩

end VG.Proof.EcKey.Compressed.PPC64LE
