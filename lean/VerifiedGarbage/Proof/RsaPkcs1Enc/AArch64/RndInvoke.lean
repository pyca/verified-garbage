module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.RndCall
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callee
public import VerifiedGarbage.Impl.RsaPkcs1Enc.AArch64.Precomputed
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.PcVerified
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on AArch64: the call

The call of `vg_rsa_pkcs1_encrypt_precomputed`, calling the precomputed
public operation `c`, by its contract (`call_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Rnd

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Random
open VG.Proof.RsaPkcs1Sig.AArch64 (PdChecked)

/-- The callee, `vg_rsa_pkcs1_encrypt_precomputed` calling `c`. -/
def encName (c : PdChecked) : String := "vg_rsa_pkcs1_encrypt_precomputed" ++ c.suffix
def encCode (c : PdChecked) : Prog isa := Impl.RsaPkcs1Enc.AArch64.Precomputed.code c.name c.code

/-- What the callee reads: `n`, `e`, `msg`, `PS`, `pre` and its stack
arguments. -/
def callRd (s : State) : List Region :=
  [nR s, eR s, msgR s, ⟨off (Q s) oBuf, psLen s⟩, preR s, ⟨Q s, 48⟩]

/-- What it writes: `out` and `scratch`. -/
def callWr (s : State) : List Region := [outR s, scrR s]

theorem stackArg_call {s w : State} {i : Nat} {pad : List Byte} (h : Args s w i pad) (rd wr : List Region)
    {j : Nat} (hj : j < 6) : stackArg (w.callEntry.withRegions rd wr) j = callArg s j := by
  show w.mem.readW (w.sp + BitVec.ofNat 64 (8 * j)) 64 = _
  rw [h.sp]; exact h.args j hj

theorem Q_sub (P : Nat) (s : State) : Q s - BitVec.ofNat 64 (P + 1087 + 1) = kb P s := by
  rw [Q_kb P s, off]; exact BitVec.add_sub_cancel _ _

theorem call_pre {P : Nat} {s w : State} (hp : RPre P s) {i : Nat} {pad : List Byte} (h : Args s w i pad) :
    (Proof.RsaPkcs1Enc.encryptPrecomputedContract AArch64.abi (P + 1088)).pre
      (w.callEntry.withRegions (callRd s) (callWr s)) := by
  have hP := hp.ps
  have hQ := Q_toNat hp
  have hK := kb_toNat hp
  have hbuf : off (Q s) oBuf = off (kb P s) (P + 1088 + oBuf) := by rw [Q_kb P s, off_off]
  have sBuf : Region.Sub ⟨off (Q s) oBuf, psLen s⟩ (stkR P s) := frame_sub s (by unfold oBuf; omega)
  have sA : Region.Sub ⟨Q s, 48⟩ (stkR P s) := by
    have := frame_sub (P := P) s (d := 0) (n := 48) (by decide)
    rwa [off, add_zero'] at this
  have sStk : Region.Sub ⟨kb P s, P + 1087 + 1⟩ (stkR P s) := by
    rw [stkR_eq]; exact Region.sub_prefix (by unfold rndStack; omega)
  have wK : (kb P s).toNat + P + 2192 ≤ 2 ^ 64 := by
    have := hp.sp2
    have h' : (kb P s).toNat + P + 2192 = s.sp.toNat := by rw [Nat.add_assoc]; exact hK
    omega
  have dSB : (⟨kb P s, P + 1087 + 1⟩ : Region).Disjoint ⟨off (Q s) oBuf, psLen s⟩ := by
    rw [hbuf]; exact Offset.base_disjoint _ (by omega) (by unfold oBuf; omega)
  have dSA : (⟨kb P s, P + 1087 + 1⟩ : Region).Disjoint ⟨Q s, 48⟩ := by
    have := Offset.base_disjoint (kb P s) (e := P + 1088) (n := 48) (k := P + 1087 + 1) (by omega)
      (by omega)
    rwa [show kb P s + BitVec.ofNat 64 (P + 1088) = Q s from (Q_kb P s).symm] at this
  sig_pre [Proof.RsaPkcs1Enc.encryptPrecomputedContract, Proof.RsaPkcs1Enc.encryptPrecomputedSig,
    AArch64.abi, AArch64.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq]
  have hP := hp.ps
  have hQ := Q_toNat hp
  have hK := kb_toNat hp
  have hpsN : (BitVec.ofNat 64 (psLen s)).toNat = psLen s := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hA : stackArgAddr (w.callEntry.withRegions (callRd s) (callWr s)) 0 = Q s := by
    show w.sp + BitVec.ofNat 64 (8 * 0) = _
    rw [h.sp]; exact add_zero' _
  simp only [h.x0, h.x1, h.x2, h.x3, h.x4, h.x5, h.x6, h.x7, h.sp, hA, Q_sub,
    stackArg_call h _ _ (j := 0) (by decide), stackArg_call h _ _ (j := 1) (by decide),
    stackArg_call h _ _ (j := 2) (by decide), stackArg_call h _ _ (j := 3) (by decide),
    stackArg_call h _ _ (j := 4) (by decide), stackArg_call h _ _ (j := 5) (by decide), callArg, hpsN]
  refine ⟨hQ.2, by have := hp.sp2; omega, rfl, rfl,
    hp.dOn, hp.dOe, hp.dOm, (hp.dKo.sub_left sBuf).symm, hp.dOs, hp.dOq, (hp.dKo.sub_left sA).symm,
    hp.dNs, hp.dEs, hp.dMs, hp.dKs.sub_left sBuf, hp.dSq, (hp.dKs.sub_left sA).symm,
    hp.dKo.sub_left sStk, hp.dKn.sub_left sStk, hp.dKe.sub_left sStk, hp.dKm.sub_left sStk, dSB,
    hp.dKs.sub_left sStk, hp.dKq.sub_left sStk, dSA,
    hp.wO, hp.wN, hp.wE, hp.wM, ?_, hp.wS, hp.wQ,
    ⟨hp.k1, hp.k2⟩, hp.hsi, hp.L1, hp.L2, hp.hml, rfl, hp.hsl, hp.hql⟩
  rw [off_toNat (by unfold oBuf; omega)]
  unfold oBuf; omega

theorem enc_depth (c : PdChecked) : (encCode c).aarch64Depth = c.code.aarch64Depth + 68 := by
  simp only [encCode, Impl.RsaPkcs1Enc.AArch64.Precomputed.code, Impl.RsaPkcs1Enc.AArch64.Precomputed.body,
    Impl.RsaPkcs1Enc.AArch64.Encrypt.psLoop, Impl.RsaPkcs1Enc.AArch64.Encrypt.msgCopy,
    Impl.RsaPkcs1Enc.AArch64.Encrypt.msgLoop,
    Impl.RsaPkcs1Enc.AArch64.Encrypt.maskLoop, Code.aarch64Depth, Instr.frameUnits,
    Impl.RsaPkcs1Enc.AArch64.Encrypt.frameBytes, Nat.zero_max, Nat.max_zero, Nat.reduceDiv, Nat.add_assoc,
    Nat.reduceAdd]

theorem call_covers {P : Nat} {s w : State} (hp : RPre P s) {i : Nat} {pad : List Byte} (h : Args s w i pad) :
    Covers (callRd s) (w.rd ++ w.wr) ∧ Covers (callWr s) w.wr := by
  have hP := hp.ps
  have hfr : (⟨Q s, frameBytes⟩ : Region) ∈ w.rd ++ w.wr := by rw [h.wr, entered_wr]; simp
  have cw : Covers (callWr s) w.wr := Covers.of_mem fun r hr => by
    simp only [callWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [h.wr, entered_wr, hp.hwr]
    rcases hr with rfl | rfl <;> simp
  have z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (add_zero' p).symm
  have cr : Covers (callRd s) (w.rd ++ w.wr) := Covers.of_forall fun r hr => by
    simp only [callRd, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr, h.rd, hp.hrd]; simp
    · exact Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr, h.rd, hp.hrd]; simp
    · exact Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr, h.rd, hp.hrd]; simp
    · exact Covers.of_sub fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact ⟨_, hfr, oBuf, rfl, by dsimp only; unfold frameBytes oBuf; omega⟩
    · exact Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr, h.rd, hp.hrd]; simp
    · exact Covers.of_sub fun r hr => by
        rw [List.mem_singleton.mp hr]; exact ⟨_, hfr, 0, z _, by dsimp only; unfold frameBytes; omega⟩
  exact ⟨cr, cw⟩

/-- What the callee reads, as on entry. -/
theorem args_read {P : Nat} {s w : State} (hp : RPre P s) {i : Nat} {pad : List Byte} (h : Args s w i pad) :
    Spec.Rsa.bytesAt w.mem (s.gpr .x3) (s.gpr .x4).toNat = nB s ∧
      Spec.Rsa.bytesAt w.mem (s.gpr .x5) (s.gpr .x6).toNat = eB s ∧
      Spec.Rsa.bytesAt w.mem (s.gpr .x7) (stackArg s 0).toNat = msgB s ∧
      Spec.Rsa.wordsAt w.mem (stackArg s 5) (stackArg s 6).toNat = preW s := by
  have dQ : ∀ {R : Region}, (stkR P s).Disjoint R → (tapeR s).Disjoint R →
      ∀ r ∈ [(⟨Q s, 1104⟩ : Region), tapeR s], R.Disjoint r := fun h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have := frame_sub (P := P) s (d := 0) (n := 1104) (by decide)
      rw [off, add_zero'] at this
      exact (h₁.sub_left this).symm
    · exact h₂.symm
  have bytes_eq : ∀ {R : Region}, (stkR P s).Disjoint R → (tapeR s).Disjoint R → R.len ≤ 2 ^ 64 →
      Spec.Rsa.bytesAt w.mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len := fun h₁ h₂ hl => by
    simp only [Spec.Rsa.bytesAt]
    exact List.map_congr_left fun j hj => h.fr.bytes (dQ h₁ h₂) hl (List.mem_range.mp hj)
  have nE : Spec.Rsa.bytesAt w.mem (s.gpr .x3) (s.gpr .x4).toNat = nB s :=
    bytes_eq (R := nR s) hp.dKn hp.dTn (by have := hp.wN; unfold nR; dsimp only; omega)
  have eE : Spec.Rsa.bytesAt w.mem (s.gpr .x5) (s.gpr .x6).toNat = eB s :=
    bytes_eq (R := eR s) hp.dKe hp.dTe (by have := hp.wE; unfold eR; dsimp only; omega)
  have mE : Spec.Rsa.bytesAt w.mem (s.gpr .x7) (stackArg s 0).toNat = msgB s :=
    bytes_eq (R := msgR s) hp.dKm hp.dTm (by have := hp.wM; unfold msgR; dsimp only; omega)
  have qE : Spec.Rsa.wordsAt w.mem (stackArg s 5) (stackArg s 6).toNat = preW s := by
    unfold Spec.Rsa.wordsAt preW Spec.Rsa.wordsAt
    refine List.map_congr_left fun j hj => ?_
    have hj := List.mem_range.mp hj
    have hw := hp.wQ
    exact h.fr.readW (r := preR s) (Offset.contains_base _ (by omega) (by omega))
      (dQ hp.dKq hp.dTq) (by decide)
  exact ⟨nE, eE, mE, qE⟩

/-- After the call. -/
structure AfterCall (P : Nat) (s u : State) (i : Nat) (pad : List Byte) : Prop where
  sp : u.sp = Q s
  rd : u.rd = s.rd
  wr : u.wr = (entered s).wr
  cs : ∀ r ∈ preserved, r ≠ .x30 → u.gpr r = s.gpr r
  vs : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  fr : Frame [stkR P s, tapeR s, outR s, scrR s] s.mem u.mem
  ps : u.mem.readW (off (Q s) oPs) 64 = BitVec.ofNat 64 (psLen s)
  lr : u.mem.readW (off (Q s) 1088) 64 = s.gpr .x30
  tape0 : u.mem.readW (s.gpr .x2) 64 = BitVec.ofNat 64 i
  tape1 : u.mem.readW (s.gpr .x2 + BitVec.ofNat 64 8) 64 = 0
  res : Spec.Rsa.publicPrecompute (nB s) = some (preW s) →
    Spec.Rsa.written u.mem (s.gpr .x0) (kOf s) ((u.gpr .x0).setWidth 32)
      (Spec.RsaPkcs1Enc.encrypt (nB s) (eB s) (msgB s) pad)

theorem call_ok (c : PdChecked)
    (hsat : ∃ s, (Proof.RsaPkcs1Enc.encryptPrecomputedContract AArch64.abi (c.stack + 1088)).pre s)
    {s w : State} (hp : RPre c.stack s) {i : Nat} {pad : List Byte} (h : Args s w i pad) :
    WP isa (.call (encName c) (encCode c)) w (AfterCall c.stack s · i pad) := by
  have hpre := call_pre hp h
  have hv := (Enc.Pc.code_verified c hsat).1
  have hdp := c.depth
  have hP := hp.ps
  have hQ := Q_toNat hp
  have hd16 : 16 * (encCode c).aarch64Depth ≤ c.stack + 1088 := by rw [enc_depth]; omega
  obtain ⟨cr, cw⟩ := call_covers hp h
  have z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (add_zero' p).symm
  refine WP.callFV hv hpre (Covers.append_left cr cw.right) cw (fun u hrd hwr hsp hf hcs hvs hpost => ?_)
    (by show 16 * (encCode c).aarch64Depth < 2 ^ 64; have := c.le; omega)
  sig_post [Proof.RsaPkcs1Enc.encryptPrecomputedContract, Proof.RsaPkcs1Enc.encryptPrecomputedSig,
    AArch64.abi, AArch64.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq] at hpost
  have hpsN : (BitVec.ofNat 64 (psLen s)).toNat = psLen s := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  simp only [h.x0, h.x2, h.x3, h.x4, h.x5, h.x6, h.x7,
    stackArg_call h _ _ (j := 0) (by decide), stackArg_call h _ _ (j := 1) (by decide),
    stackArg_call h _ _ (j := 4) (by decide), stackArg_call h _ _ (j := 5) (by decide), callArg, hpsN,
    h.buf] at hpost
  obtain ⟨nE, eE, mE, qE⟩ := args_read hp h
  rw [nE, eE, mE, qE] at hpost
  -- what the call leaves
  have sB : Region.Sub (below w.sp (16 * (encCode c).aarch64Depth)) (stkR c.stack s) := by
    rw [h.sp]
    have := Offset.sub_below (Q s) (a := 16 * (encCode c).aarch64Depth) (n := 16 * (encCode c).aarch64Depth)
      (b := c.stack + 1087 + 1) (m := c.stack + 1087 + 1) (by omega) (by omega)
    rw [Q_sub] at this
    rw [stkR_eq]
    exact fun x hx => Region.sub_prefix (by unfold rndStack; omega) x (this x hx)
  have hws : ∀ r ∈ callWr s ++ [below w.sp (16 * (encCode c).aarch64Depth)],
      r = outR s ∨ r = scrR s ∨ Region.Sub r (stkR c.stack s) := fun r hr => by
    simp only [callWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl rfl
    · exact .inr (.inl rfl)
    · exact .inr (.inr sB)
  have apart : ∀ {R : Region}, R.Disjoint (outR s) → R.Disjoint (scrR s) →
      R.Disjoint (below w.sp (16 * (encCode c).aarch64Depth)) →
      ∀ {a : Addr}, R.Contains a 8 → u.mem.readW a 64 = w.mem.readW a 64 := fun h₁ h₂ h₃ _ ha =>
    hf.readW ha (fun r hr => by
      simp only [callWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h₁
      · exact h₂
      · exact h₃) (by decide)
  have slot : ∀ (d : Nat), d + 8 ≤ 1104 → u.mem.readW (off (Q s) d) 64 = w.mem.readW (off (Q s) d) 64 :=
    fun d hd => apart (R := ⟨off (Q s) d, 8⟩) (hp.dKo.sub_left (frame_sub s hd))
      (hp.dKs.sub_left (frame_sub s hd)) (by
        rw [h.sp]; exact Offset.disjoint_below _ (by omega)) (Region.contains_self _ _)
  have tB : (tapeR s).Disjoint (below w.sp (16 * (encCode c).aarch64Depth)) := hp.dKt.symm.sub_right sB
  have hpk : ∀ r ∈ preserved, r ≠ .x30 →
      r ∉ [Reg.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] := by
    decide
  refine ⟨hsp.trans h.sp, hrd.trans h.rd, hwr.trans h.wr, fun r hr h30 => (hcs r hr h30).trans (h.keep r (hpk r hr h30)),
    fun r hr => by rw [hvs r hr, h.v], ?_, (slot _ (by decide)).trans h.ps, (slot _ (by decide)).trans h.lr,
    (apart hp.dOt.symm hp.dTs tB (by
      rw [z (s.gpr .x2)]; exact Offset.contains_base _ (by decide) (by decide))).trans h.tape0,
    (apart hp.dOt.symm hp.dTs tB (Offset.contains_base _ (by decide) (by decide))).trans h.tape1,
    fun hq => hpost hq⟩
  refine (h.fr.sub fun r hr => ?_).trans (hf.sub fun r hr => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · refine ⟨stkR c.stack s, by simp, ?_⟩
      have := frame_sub (P := c.stack) s (d := 0) (n := 1104) (by decide)
      rwa [off, add_zero'] at this
    · exact ⟨tapeR s, by simp, fun _ h => h⟩
  · rcases hws r hr with rfl | rfl | hs
    · exact ⟨outR s, by simp, fun _ h => h⟩
    · exact ⟨scrR s, by simp, fun _ h => h⟩
    · exact ⟨stkR c.stack s, by simp, hs⟩

end VG.Proof.RsaPkcs1Enc.AArch64.Rnd
