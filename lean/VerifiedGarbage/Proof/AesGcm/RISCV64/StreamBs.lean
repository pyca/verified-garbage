module

public import VerifiedGarbage.Proof.AesGcm.RISCV64.Verified
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Contract
public import VerifiedGarbage.Proof.AesGcm.RISCV64.CTSeal
public import VerifiedGarbage.Impl.AesGcm.RISCV64
public import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamCrypt
public import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamFinish
import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamVerify
import VerifiedGarbage.Proof.AesGcm.RISCV64.CryptOk
import VerifiedGarbage.Proof.AesGcm.RISCV64.J0
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.AesGcm.RISCV64.InitCT
import VerifiedGarbage.Proof.AesGcm.RISCV64.Compare
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Verified
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Contract
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTSeal
meta import VerifiedGarbage.Impl.AesGcm.RISCV64
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamCrypt
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamFinish
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamVerify
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CryptOk
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.J0
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.RISCV64.Spill
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.InitCT
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Compare
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint

/-!
# AES-GCM on RISC-V: the streaming functions with the round keys bitsliced

Untrusted: everything here is checked by Lean. `vg_aes_gcm_stream_encrypt_bitsliced`,
`…_decrypt_bitsliced`, `…_finish_bitsliced` and `…_verify_bitsliced` take the
buffer of `Spec/Gcm/Bitsliced.lean` and run the code of the plain functions
with `vg_aes_ctr32_bs` for `vg_aes_ctr32` (`streamEncryptB true`, …), whose
proofs take the buffer's round keys (`BsAt`, from `CtxSlicedRepr` by
`keysAt_of_sliced`). `bsPre` moves the buffer's address to `t2` and loads the
working space's, the first stack argument, into `a7`, where the plain code
takes it.
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64
open VG.Spec.Aes (bytesAt)

/-! ## The entry -/

/-- `bsPre`: `t2 := a7`, `a7 := [sp]`. -/
theorem bsPre_ok {σ : State} (hsa : σ.sp.toNat % 16 = 0)
    (hi : InRegions (σ.rd ++ σ.wr) (σ.sp + BitVec.ofNat 64 0) 8) :
    WP isa (.block bsPre) σ fun s₀ => s₀.gpr .t2 = σ.gpr .a7 ∧ s₀.gpr .a7 = stackArg σ 0 ∧
      (∀ r, r ≠ .t2 → r ≠ .a7 → s₀.gpr r = σ.gpr r) ∧ Keeps σ s₀ := by
  refine Steps.wp_mv fun sA uA => Steps.wp_addSp (imm := 0) (by decide) fun sB uB => ?_
  refine Steps.wp_ld (off := 0) (a := σ.sp + BitVec.ofNat 64 0) (by decide)
    (by rw [uB.gpr, uA.sp, add_ofNat_zero, add_ofNat_zero])
    (Spill.al8 (B := σ.sp) (by omega_using [hsa]) (by decide)) (by rw [uB.rd, uB.wr, uA.rd, uA.wr]; exact hi)
    fun sC uC => WP.block_nil ⟨by rw [uC.other _ (by decide), uB.other _ (by decide), uA.gpr],
      by rw [uC.gpr, uB.mem, uA.mem]; rfl,
      fun r h2 h7 => by rw [uC.other r h7, uB.other r h7, uA.other r h2],
      ⟨by rw [uC.mem, uB.mem, uA.mem], by rw [uC.rd, uB.rd, uA.rd], by rw [uC.wr, uB.wr, uA.wr],
        by rw [uC.sp, uB.sp, uA.sp]⟩⟩

/-- After `bsPre`: the registers but `t2` and `a7` kept. -/
structure BsPreOut (σ s₀ : State) : Prop where
  t2 : s₀.gpr .t2 = σ.gpr .a7
  a7 : s₀.gpr .a7 = stackArg σ 0
  other : ∀ r, r ≠ .t2 → r ≠ .a7 → s₀.gpr r = σ.gpr r
  keeps : Keeps σ s₀

theorem BsPreOut.abi {σ s₀ s' : State} (h : BsPreOut σ s₀) (ha : abiPreserved s₀ s') : abiPreserved σ s' :=
  ⟨fun r hr => (ha.1 r hr).trans (h.other r (by revert hr; revert r; decide) (by revert hr; revert r; decide)),
    ha.2.1.trans h.keeps.sp, ha.2.2.trans (h.other _ (by decide) (by decide))⟩

/-- `streamCryptBsPre`, after `bsPre`: the plain functions' precondition and the buffer's round keys. -/
theorem scBs_pre {σ s₀ : State} (h : streamCryptBsPre σ) (h0 : BsPreOut σ s₀) :
    streamCryptPreX [⟨σ.gpr .a7, 1248⟩, args σ 1] s₀ ∧ BsAt s₀ := by
  obtain ⟨hrd, hwr, dcs, dcd, dcw, dsd, dsw, ddw, dbs, dbd, dbw, fc, fs, fd, fw, hR, ⟨hsa, hsp, k1, k2, k3, k4, k5, -⟩,
    a0, a2, a7w, a7b, hsl⟩ := h
  obtain e0 := h0.other .a0 (by decide) (by decide)
  obtain e1 := h0.other .a1 (by decide) (by decide)
  obtain e2 := h0.other .a2 (by decide) (by decide)
  obtain e5 := h0.other .a5 (by decide) (by decide)
  obtain e6 := h0.other .a6 (by decide) (by decide)
  obtain k := h0.keeps
  have hR14 : (σ.gpr .a1).toNat ≤ 14 := by rcases hR with h | h | h <;> omega_using [h]
  refine ⟨?_, ?_⟩
  · simp only [streamCryptPreX, stkOk, stkAll, e0, e1, e2, e5, e6, h0.a7, k.rd, k.wr, k.sp, and_true]
    exact ⟨hrd, hwr, dcs, dcd, dcw, dsd, dsw, ddw, fc, fs, fd, fw, hR, ⟨hsa, hsp, k1, k2, k3, k4⟩, a0, a2, a7w⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h0.t2, k.rd, hrd]; exact covers_prefix (k := 1248) (covers_mem (by simp)) (by decide)
    · rw [h0.t2]; exact a7b
    · rw [h0.t2, e2]; exact dbs.sub_left (Region.sub_prefix (by decide))
    · rw [h0.t2, h0.a7]; exact dbw.sub_left (Region.sub_prefix (by decide))
    · rw [h0.t2, k.sp]; exact k5.symm.sub_left (Region.sub_prefix (by decide))
    · rw [h0.t2, e5, e6]; exact dbd.sub_left (Region.sub_prefix (by decide))
    · rw [h0.t2, e1, e0, k.mem]; exact keysAt_of_sliced hR14 hsl

theorem scBs_in {σ : State} (h : streamCryptBsPre σ) : InRegions (σ.rd ++ σ.wr) (σ.sp + BitVec.ofNat 64 0) 8 := by
  obtain ⟨hrd, -⟩ := h
  refine ⟨args σ 1, List.mem_append_left _ (by rw [hrd]; simp), ?_⟩
  simp only [args, stackArgAddr]
  exact Region.contains_self _ _

theorem scBs_sa {σ : State} (h : streamCryptBsPre σ) : σ.sp.toNat % 16 = 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨hsa, -⟩, -⟩ := h
  exact hsa

/-! ## Correctness -/

theorem streamEncryptBs_wp [VG.Proof.Gcm.RISCV64.GhashLaw] {σ : State} (h : streamEncryptBsRISCV64.pre σ) :
    WP isa streamEncryptBs σ fun s' => abiPreserved σ s' ∧ streamEncryptBsRISCV64.post σ s' := by
  have h' : streamCryptBsPre σ := h
  refine WP.seq (WP.mono (bsPre_ok (scBs_sa h') (scBs_in h')) fun s₀ ⟨t2, a7, ho, k⟩ => ?_)
  obtain h0 : BsPreOut σ s₀ := ⟨t2, a7, ho, k⟩
  obtain ⟨hx, hb⟩ := scBs_pre h' h0
  refine WP.mono (streamEncryptB_wp hx fun _ => hb) fun s' ⟨ha, hp⟩ => ⟨h0.abi ha, ?_⟩
  simp only [streamEncryptBsRISCV64, streamEncryptRISCV64] at hp ⊢
  rwa [ho .a0 (by decide) (by decide), ho .a1 (by decide) (by decide), ho .a2 (by decide) (by decide),
    ho .a3 (by decide) (by decide), ho .a4 (by decide) (by decide), ho .a5 (by decide) (by decide),
    ho .a6 (by decide) (by decide), k.mem] at hp

theorem streamDecryptBs_wp [VG.Proof.Gcm.RISCV64.GhashLaw] {σ : State} (h : streamDecryptBsRISCV64.pre σ) :
    WP isa streamDecryptBs σ fun s' => abiPreserved σ s' ∧ streamDecryptBsRISCV64.post σ s' := by
  have h' : streamCryptBsPre σ := h
  refine WP.seq (WP.mono (bsPre_ok (scBs_sa h') (scBs_in h')) fun s₀ ⟨t2, a7, ho, k⟩ => ?_)
  obtain h0 : BsPreOut σ s₀ := ⟨t2, a7, ho, k⟩
  obtain ⟨hx, hb⟩ := scBs_pre h' h0
  refine WP.mono (streamDecryptB_wp hx fun _ => hb) fun s' ⟨ha, hp⟩ => ⟨h0.abi ha, ?_⟩
  simp only [streamDecryptBsRISCV64, streamDecryptRISCV64] at hp ⊢
  rwa [ho .a0 (by decide) (by decide), ho .a1 (by decide) (by decide), ho .a2 (by decide) (by decide),
    ho .a3 (by decide) (by decide), ho .a4 (by decide) (by decide), ho .a5 (by decide) (by decide),
    ho .a6 (by decide) (by decide), k.mem] at hp

/-! ## Constant time -/

/-- The layout, from the precondition. -/
theorem bsLay {σ : State} (h : streamCryptBsPre σ) : Lay (σ.gpr .a0) (σ.gpr .a2) (stackArg σ 0) := by
  obtain ⟨-, -, dcs, -, dcw, -, dsw, -, -, -, -, fc, fs, -, fw, -, -, a0, a2, a7w, -⟩ := h
  exact Lay.of fc fs fw dcs dcw dsw a0 a2 a7w

/-- After `bsPre`, in terms of the first run's arguments: the plain functions' precondition, the
buffer's round keys, and the registers the code reads. -/
def SCB (σ : State) (s : State) : Prop :=
  (∃ ex, streamCryptPreX ex s) ∧ BsAt s ∧ s.gpr .a0 = σ.gpr .a0 ∧ s.gpr .a1 = σ.gpr .a1 ∧
    s.gpr .a2 = σ.gpr .a2 ∧ s.gpr .a3 = σ.gpr .a3 ∧ s.gpr .a4 = σ.gpr .a4 ∧ s.gpr .a5 = σ.gpr .a5 ∧
    s.gpr .a6 = σ.gpr .a6 ∧ s.gpr .a7 = stackArg σ 0 ∧ s.gpr .t2 = σ.gpr .a7 ∧ s.sp = σ.sp

theorem scb_of {σ s s₀ : State} (h : streamCryptBsPre s) (hq : onePub 1 σ s) (h0 : BsPreOut s s₀) : SCB σ s₀ := by
  obtain ⟨hx, hb⟩ := scBs_pre h h0
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, qsp, qa⟩ := hq
  refine ⟨⟨_, hx⟩, hb, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [h0.keeps.sp, qsp]⟩
  · rw [h0.other _ (by decide) (by decide), q0]
  · rw [h0.other _ (by decide) (by decide), q1]
  · rw [h0.other _ (by decide) (by decide), q2]
  · rw [h0.other _ (by decide) (by decide), q3]
  · rw [h0.other _ (by decide) (by decide), q4]
  · rw [h0.other _ (by decide) (by decide), q5]
  · rw [h0.other _ (by decide) (by decide), q6]
  · rw [h0.a7, qa 0 (by decide)]
  · rw [h0.t2, q7]

/-- `bsPre` is constant time, and leads to `SCB`. -/
theorem bsPre_ct {σ : State} :
    CT (fun s => streamCryptBsPre s ∧ onePub 1 σ s) (.block bsPre) := by
  obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.a7]) (.block bsPre) h).isSome = true :=
    ⟨_, by taint_decide⟩
  exact CT.taintEq _ σ.gpr σ.sp (fun s ⟨_, _, _, _, _, _, _, _, q7, qsp, _⟩ =>
    ⟨qsp.symm, by simp [q7]⟩) hc

theorem bsPre_scb {σ s : State} (h : streamCryptBsPre s ∧ onePub 1 σ s) : WP isa (.block bsPre) s (SCB σ) :=
  WP.mono (bsPre_ok (scBs_sa h.1) (scBs_in h.1)) fun _ ⟨t2, a7, ho, k⟩ => scb_of h.1 h.2 ⟨t2, a7, ho, k⟩

/-- Before `cryptB true false`: `crypt`'s invariant, with the buffer at `b` in `s7`. -/
def CIB (b c st w sp D : Addr) (R : Nat) (N A T : BitVec 64) (s : State) : Prop :=
  ∃ V icb P, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧ V .s9 = D ∧ V .s8 = N ∧ V .s10 = A ∧ V .s11 = T ∧
    P % 16 = T.toNat % 16 ∧ CrIn false V sp R icb P D D N.toNat s ∧ BkB true b V sp R s.mem D D N.toNat s

/-- After the entry of `decrypt`: `DI`, with the buffer at `b` in `s7`. -/
def DIB (b c st w sp D : Addr) (R : Nat) (N A T : BitVec 64) (s : State) : Prop :=
  ∃ V : Reg → BitVec 64, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧ V .s9 = D ∧ V .s8 = N ∧ V .s10 = A ∧
    V .s11 = T ∧ V .s3 = BitVec.ofNat 64 R ∧ (R = 10 ∨ R = 12 ∨ R = 14) ∧ Env V sp s ∧ DataW c st w s D N.toNat ∧
    BkB true b V sp R s.mem D D N.toNat s

theorem BkIn.taFrame {B c st w sp : Addr} {R : Nat} {m₀ : Mem} {S D : Addr} {n : Nat} {s : State}
    (hb : BkIn B c st w sp R m₀ S D n s) : ∀ r ∈ taFrame st w sp, (⟨B, 960⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact hb.st.sub_right (Lay.stSub (by decide))
  · exact hb.st.sub_right (Lay.stSub (by decide))
  · exact hb.w.sub_right (Lay.wSub (by decide))
  · exact hb.w.sub_right (Lay.wSub (by decide))
  · exact hb.sk

/-- The entry of `decrypt`. -/
theorem scB_DIB {ex : List Region} {s₀ : State} (h : streamCryptPreX ex s₀) (hb : BsAt s₀) :
    WP isa (.block (cryptEntryB true)) s₀ (DIB (s₀.gpr .t2) (s₀.gpr .a0) (s₀.gpr .a2) (s₀.gpr .a7) s₀.sp
      (s₀.gpr .a5) (s₀.gpr .a1).toNat (s₀.gpr .a6) (s₀.gpr .a3) (s₀.gpr .a4)) := by
  obtain L₀ := scLay h
  obtain hR := sc_R h
  refine WP.mono (entryB_wp (bs := true) (sc_W h) (sc_al h)) fun s₁ ⟨h1, h17⟩ => ?_
  obtain f₁ : Frame [savedR (s₀.gpr .a7)] s₀.mem s₁.mem := h1.en.frame
  refine ⟨s₁.gpr, h1.s2, h1.s1, h1.s0, h1.s9, h1.s8, h1.s10, h1.s11,
    by rw [h1.s3, BitVec.ofNat_toNat, BitVec.setWidth_eq], hR, sc_env h h1,
    sc_dataW h h1.en.keeps.wr h1.en.keeps.sp, fun _ => ⟨h17 rfl, ?_⟩⟩
  rw [h17 rfl, h1.s2, h1.s1, h1.s0]
  exact ⟨covers_appL (by rw [h1.en.keeps.rd]; exact hb.rd), hb.al, hb.st, hb.w, hb.sk, hb.d, hb.d,
    keysAt_ctx_frame hR f₁ hb.saved (ctx_saved L₀) hb.keys⟩

section
variable {b c st w sp D : Addr} {R : Nat} {N A T : BitVec 64}

/-- The arguments of `crypt`, with the buffer kept. -/
theorem dib_textArgs {s : State} (h : DIB b c st w sp D R N A T s) :
    WP isa (.block textArgs) s (CIB b c st w sp D R N A T) := by
  obtain ⟨V, h29, h30, h31, h20, h19, h22, h23, h28, hR, he, hd, hb⟩ := h
  refine WP.mono textArgs_ok fun s₂ ⟨h24, h25, h26, hg, hk⟩ => ?_
  have he₂ := he.keep (fun r hr => hg r (by revert r; decide) (by revert r; decide) (by revert r; decide))
    hk.sp hk.rd hk.wr
  exact ⟨V, 0, T.toNat, h29, h30, h31, h20, h19, h22, h23, rfl, ⟨he₂, by rw [h24, he.fr _ (by decide), h20],
    by rw [h25, he.fr _ (by decide), h19, BitVec.ofNat_toNat, BitVec.setWidth_eq],
    by rw [h26, he.fr _ (by decide), h23], h28, hR, by rw [h29, h30, h31]; exact hd.of_eq hk.rd hk.wr hk.sp,
    by rw [h30, h31]; exact (hd.of_eq hk.rd hk.wr hk.sp).ok, rfl, Bool.noConfusion⟩,
    fun hbs => ⟨(hb hbs).1, ((hb hbs).2.of_eq hk.rd hk.wr).memEq hk.mem⟩⟩

theorem dib_ta {s : State} (h : DIB b c st w sp D R N A T s) : TA c st w sp D N A T s :=
  let ⟨V, h29, h30, h31, h20, h19, h22, h23, _, _, he, hd, _⟩ := h
  ⟨V, h29, h30, h31, h20, h19, h22, h23, he, hd.ok⟩

theorem cib_crIB {s : State} (h : CIB b c st w sp D R N A T s) :
    CrIB true false b c st w sp R D D N.toNat (T.toNat % 16) s :=
  let ⟨V, icb, P, h29, h30, h31, _, _, _, _, hP, ci, hb⟩ := h
  ⟨V, icb, P, h29, h30, h31, hP, ci, hb⟩

variable (L : Lay c st w)
include L

theorem cib_crypt {s : State} (h : CIB b c st w sp D R N A T s) : WP isa (cryptB true false) s (TA c st w sp D N A T) := by
  obtain ⟨V, icb, P, h29, h30, h31, h20, h19, h22, h23, _, ci, hb⟩ := h
  refine WP.mono (WP.with_rdwr (cryptB_ok (L.v h29 h30 h31) ci fun hbs => (hb hbs).2))
    fun s' ⟨co, rd, wr, sp'⟩ => ⟨V, h29, h30, h31, h20, h19, h22, h23, co.env, ?_⟩
  have := ci.data.ok.of_eq rd wr sp'
  rw [h30, h31] at this
  exact this

theorem dib_textAbsorb [VG.Proof.Gcm.RISCV64.GhashLaw] {s : State} (h : DIB b c st w sp D R N A T s) :
    WP isa textAbsorb s (DIB b c st w sp D R N A T) := by
  obtain ⟨V, h29, h30, h31, h20, h19, h22, h23, h28, hR, he, hd, hb⟩ := h
  refine WP.mono (WP.with_rdwr (textAbsorb_ok (L.v h29 h30 h31) (a := List.replicate (A.toNat % 16) 0)
    (ct := List.replicate T.toNat 0) he rfl (by rw [h20, h19, h30, h31]; exact hd.ok) (by simp [h22])
    (by simp [h23]))) fun s' ⟨ta, rd, wr, sp'⟩ => ⟨V, h29, h30, h31, h20, h19, h22, h23, h28, hR, ta.env,
      hd.of_eq rd wr sp', fun hbs => ⟨(hb hbs).1, (hb hbs).2.frame hR ta.frame (hb hbs).2.taFrame
        (ctx_taFrame (L.v h29 h30 h31) he.stk') rd wr⟩⟩

end

/-- The entry and `crypt`'s arguments of `encrypt`. -/
theorem scB_CIB {ex : List Region} {s₀ : State} (h : streamCryptPreX ex s₀) (hb : BsAt s₀) :
    WP isa (.block (cryptEntryB true ++ textArgs)) s₀ (CIB (s₀.gpr .t2) (s₀.gpr .a0) (s₀.gpr .a2) (s₀.gpr .a7)
      s₀.sp (s₀.gpr .a5) (s₀.gpr .a1).toNat (s₀.gpr .a6) (s₀.gpr .a3) (s₀.gpr .a4)) :=
  WP.block_append (WP.mono (scB_DIB h hb) fun _ h' => dib_textArgs h')

theorem streamEncryptBs_ct [VG.Proof.Gcm.RISCV64.GhashLaw] :
    ConstantTime isa streamEncryptBsRISCV64.pre streamEncryptBsRISCV64.pub streamEncryptBs := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  have h₁' : streamCryptBsPre σ₁ := h₁
  have L := bsLay h₁'
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, qsp, qa⟩ := hq
  refine ⟨fun s => streamCryptBsPre s ∧ onePub 1 σ₁ s, ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    fun _ _ => rfl⟩, ⟨h₂, q0, q1, q2, q3, q4, q5, q6, q7, qsp, qa⟩, ?_⟩
  refine CT.seq (J := SCB σ₁) bsPre_ct (fun _ h => bsPre_scb h) ?_
  let ci := CIB (σ₁.gpr .a7) (σ₁.gpr .a0) (σ₁.gpr .a2) (stackArg σ₁ 0) σ₁.sp (σ₁.gpr .a5) (σ₁.gpr .a1).toNat
    (σ₁.gpr .a6) (σ₁.gpr .a3) (σ₁.gpr .a4)
  refine CT.seq (J := ci) ?_ (fun s ⟨⟨_, hx⟩, hb, e0, e1, e2, e3, e4, e5, e6, e7, e8, esp⟩ => by
    have := scB_CIB hx hb
    rw [e0, e1, e2, e3, e4, e5, e6, e7, e8, esp] at this
    exact this) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint
        (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t2]) (.block (cryptEntryB true ++ textArgs)) h).isSome =
        true := ⟨_, by taint_decide⟩
    exact CT.taintEq _ (fun r => if r = .a7 then stackArg σ₁ 0 else if r = .t2 then σ₁.gpr .a7 else σ₁.gpr r) σ₁.sp
      (fun s ⟨_, _, e0, e1, e2, e3, e4, e5, e6, e7, e8, esp⟩ => ⟨esp, by simp [e0, e1, e2, e3, e4, e5, e6, e7, e8]⟩) hc
  refine CT.seq ((cryptB_ct L).mono fun _ h => cib_crIB h) (fun _ h => cib_crypt L h) ?_
  refine CT.seq (J := fun s => s.gpr .s0 = stackArg σ₁ 0 ∧ s.sp = σ₁.sp) (textAbsorb_ct L)
    (fun _ h => ta_textAbsorb L h) ?_
  obtain ⟨_, hc⟩ := restore_taint
  exact CT.taintEq _ (fun _ => stackArg σ₁ 0) σ₁.sp (fun s ⟨e31, esp⟩ => ⟨esp, by simp [e31]⟩) hc

theorem streamDecryptBs_ct [VG.Proof.Gcm.RISCV64.GhashLaw] :
    ConstantTime isa streamDecryptBsRISCV64.pre streamDecryptBsRISCV64.pub streamDecryptBs := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  have h₁' : streamCryptBsPre σ₁ := h₁
  have L := bsLay h₁'
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, qsp, qa⟩ := hq
  refine ⟨fun s => streamCryptBsPre s ∧ onePub 1 σ₁ s, ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    fun _ _ => rfl⟩, ⟨h₂, q0, q1, q2, q3, q4, q5, q6, q7, qsp, qa⟩, ?_⟩
  refine CT.seq (J := SCB σ₁) bsPre_ct (fun _ h => bsPre_scb h) ?_
  let di := DIB (σ₁.gpr .a7) (σ₁.gpr .a0) (σ₁.gpr .a2) (stackArg σ₁ 0) σ₁.sp (σ₁.gpr .a5) (σ₁.gpr .a1).toNat
    (σ₁.gpr .a6) (σ₁.gpr .a3) (σ₁.gpr .a4)
  refine CT.seq (J := di) ?_ (fun s ⟨⟨_, hx⟩, hb, e0, e1, e2, e3, e4, e5, e6, e7, e8, esp⟩ => by
    have := scB_DIB hx hb
    rw [e0, e1, e2, e3, e4, e5, e6, e7, e8, esp] at this
    exact this) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint
        (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t2]) (.block (cryptEntryB true)) h).isSome =
        true := ⟨_, by taint_decide⟩
    exact CT.taintEq _ (fun r => if r = .a7 then stackArg σ₁ 0 else if r = .t2 then σ₁.gpr .a7 else σ₁.gpr r) σ₁.sp
      (fun s ⟨_, _, e0, e1, e2, e3, e4, e5, e6, e7, e8, esp⟩ => ⟨esp, by simp [e0, e1, e2, e3, e4, e5, e6, e7, e8]⟩) hc
  refine CT.seq ((textAbsorb_ct L).mono fun _ h => dib_ta h) (fun _ h => dib_textAbsorb L h) ?_
  refine CT.seq ?_ (fun _ h => dib_textArgs h) ?_
  · obtain ⟨_, hc⟩ := textArgs_taint
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, a20, a19, _, a23, _, _, e₁, _, _⟩
      ⟨_, _, _, _, b20, b19, _, b23, _, _, e₂, _, _⟩ => ⟨e₁.sp.trans e₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [e₁.fr _ (by decide), e₂.fr _ (by decide), a19, b19]
    · rw [e₁.fr _ (by decide), e₂.fr _ (by decide), a20, b20]
    · rw [e₁.fr _ (by decide), e₂.fr _ (by decide), a23, b23]
  refine CT.seq ((cryptB_ct L).mono fun _ h => cib_crIB h) (fun _ h => cib_crypt L h) ?_
  obtain ⟨_, hc⟩ := restore_taint
  exact CT.taintEq _ (fun _ => stackArg σ₁ 0) σ₁.sp (fun s h => ⟨(ta_exit h).2, by simp [(ta_exit h).1]⟩) hc

/-! ## `finish` -/

/-- `t2 := a6`, `a6 := a7`. -/
theorem finMv_ok {σ : State} :
    WP isa (.block [mov .t2 .a6, mov .a6 .a7]) σ fun s₀ => s₀.gpr .t2 = σ.gpr .a6 ∧ s₀.gpr .a6 = σ.gpr .a7 ∧
      (∀ r, r ≠ .t2 → r ≠ .a6 → s₀.gpr r = σ.gpr r) ∧ Keeps σ s₀ :=
  Steps.wp_mv fun sA uA => Steps.wp_mv fun sB uB => WP.block_nil
    ⟨by rw [uB.other _ (by decide), uA.gpr], by rw [uB.gpr, uA.other _ (by decide)],
      fun r h2 h6 => by rw [uB.other r h6, uA.other r h2],
      ⟨by rw [uB.mem, uA.mem], by rw [uB.rd, uA.rd], by rw [uB.wr, uA.wr], by rw [uB.sp, uA.sp]⟩⟩

/-- After `finMv`: the registers but `t2` and `a6` kept. -/
structure FinMvOut (σ s₀ : State) : Prop where
  t2 : s₀.gpr .t2 = σ.gpr .a6
  a6 : s₀.gpr .a6 = σ.gpr .a7
  other : ∀ r, r ≠ .t2 → r ≠ .a6 → s₀.gpr r = σ.gpr r
  keeps : Keeps σ s₀

theorem FinMvOut.abi {σ s₀ s' : State} (h : FinMvOut σ s₀) (ha : abiPreserved s₀ s') : abiPreserved σ s' :=
  ⟨fun r hr => (ha.1 r hr).trans (h.other r (by revert hr; revert r; decide) (by revert hr; revert r; decide)),
    ha.2.1.trans h.keeps.sp, ha.2.2.trans (h.other _ (by decide) (by decide))⟩

theorem finBs_pre {σ s₀ : State} (h : finBsPre σ) (h0 : FinMvOut σ s₀) :
    finPreX [⟨σ.gpr .a6, 1248⟩] s₀ ∧ BsAtW s₀ .a6 := by
  obtain ⟨hrd, hwr, dcs, dct, dcw, dst, dsw, dtw, dbs, dbw, fc, fs, ft, fw, hR, ⟨hsa, hsp, k1, k2, k3, k4, k5, -⟩,
    a0, a2, a7w, a6b, hsl⟩ := h
  obtain e0 := h0.other .a0 (by decide) (by decide)
  obtain e1 := h0.other .a1 (by decide) (by decide)
  obtain e2 := h0.other .a2 (by decide) (by decide)
  obtain e5 := h0.other .a5 (by decide) (by decide)
  obtain k := h0.keeps
  have hR14 : (σ.gpr .a1).toNat ≤ 14 := by rcases hR with h | h | h <;> omega_using [h]
  refine ⟨?_, ?_⟩
  · simp only [finPreX, stkOk, stkAll, e0, e1, e2, e5, h0.a6, k.rd, k.wr, k.sp, and_true]
    exact ⟨hrd, hwr, dcs, dct, dcw, dst, dsw, dtw, fc, fs, ft, fw, hR, ⟨hsa, hsp, k1, k2, k3, k4⟩, a0, a2, a7w⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h0.t2, k.rd, hrd]; exact covers_prefix (k := 1248) (covers_mem (by simp)) (by decide)
    · rw [h0.t2]; exact a6b
    · rw [h0.t2, e2]; exact dbs.sub_left (Region.sub_prefix (by decide))
    · rw [h0.t2, h0.a6]; exact dbw.sub_left (Region.sub_prefix (by decide))
    · rw [h0.t2, k.sp]; exact k5.symm.sub_left (Region.sub_prefix (by decide))
    · rw [h0.t2, e1, e0, k.mem]; exact keysAt_of_sliced hR14 hsl

theorem streamFinishBs_wp [VG.Proof.Gcm.RISCV64.GhashLaw] {σ : State} (h : streamFinishBsRISCV64.pre σ) :
    WP isa streamFinishBs σ fun s' => abiPreserved σ s' ∧ streamFinishBsRISCV64.post σ s' := by
  have h' : finBsPre σ := h
  refine WP.seq (WP.mono finMv_ok fun s₀ ⟨t2, a6, ho, k⟩ => ?_)
  obtain h0 : FinMvOut σ s₀ := ⟨t2, a6, ho, k⟩
  obtain ⟨hx, hb⟩ := finBs_pre h' h0
  refine WP.mono (streamFinishB_wp hx fun _ => hb) fun s' ⟨ha, hp⟩ => ⟨h0.abi ha, ?_⟩
  simp only [streamFinishBsRISCV64, streamFinishRISCV64] at hp ⊢
  rwa [ho .a0 (by decide) (by decide), ho .a1 (by decide) (by decide), ho .a2 (by decide) (by decide),
    ho .a3 (by decide) (by decide), ho .a4 (by decide) (by decide), ho .a5 (by decide) (by decide), k.mem] at hp

/-- After `finMv`, in terms of the first run's arguments. -/
def FSB (σ : State) (s : State) : Prop :=
  (∃ ex, finPreX ex s) ∧ BsAtW s .a6 ∧ s.gpr .a0 = σ.gpr .a0 ∧ s.gpr .a1 = σ.gpr .a1 ∧
    s.gpr .a2 = σ.gpr .a2 ∧ s.gpr .a3 = σ.gpr .a3 ∧ s.gpr .a4 = σ.gpr .a4 ∧ s.gpr .a5 = σ.gpr .a5 ∧
    s.gpr .a6 = σ.gpr .a7 ∧ s.gpr .t2 = σ.gpr .a6 ∧ s.sp = σ.sp

/-- `FinI`, with the buffer at `b` in `s7`. -/
def FinIB (b c st w sp : Addr) (R : Nat) (A T Tp : BitVec 64) (s : State) : Prop :=
  ∃ V : Reg → BitVec 64, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧ V .s3 = BitVec.ofNat 64 R ∧ V .s10 = A ∧
    V .s11 = T ∧ V .s9 = Tp ∧ Env V sp s ∧ Covers [⟨Tp, 16⟩] s.wr ∧ BkB true b V sp R s.mem w w 16 s

theorem finB_FIB {ex : List Region} {s₀ : State} (h : finPreX ex s₀) (hb : BsAtW s₀ .a6) :
    WP isa (.block (finEntryB true)) s₀ (FinIB (s₀.gpr .t2) (s₀.gpr .a0) (s₀.gpr .a2) (s₀.gpr .a6) s₀.sp
      (s₀.gpr .a1).toNat (s₀.gpr .a3) (s₀.gpr .a4) (s₀.gpr .a5)) := by
  obtain L₀ := finLay h
  obtain hR := fin_R h
  refine WP.mono (fin1B_wp' (bs := true) (fin_W h) (fin_al h)) fun s₁ ⟨h1, h17⟩ => ?_
  have hT : Covers [⟨s₀.gpr .a5, 16⟩] s₁.wr := by
    rw [h1.en.keeps.wr, h.2.1]; exact covers_mem (by simp)
  refine ⟨s₁.gpr, h1.s2, h1.s1, h1.s0, by rw [h1.s3, BitVec.ofNat_toNat, BitVec.setWidth_eq], h1.s10, h1.s11, h1.s9,
    fin_env h h1, hT, fun _ => ⟨h17 rfl, ?_⟩⟩
  rw [h17 rfl, h1.s2, h1.s1, h1.s0]
  exact hb.bkIn L₀ hR h1.en.keeps.rd h1.en.frame

theorem streamFinishBs_ct [VG.Proof.Gcm.RISCV64.GhashLaw] :
    ConstantTime isa streamFinishBsRISCV64.pre streamFinishBsRISCV64.pub streamFinishBs := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨⟨q3, q4, q5, q6, q7, q8, q9, qsp⟩, q10⟩ := hq
  have h₁' : finBsPre σ₁ := h₁
  obtain ⟨-, -, dcs, -, dcw, -, dsw, dtw, -, -, fc, fs, -, fw, hR, -, a0, a2, a7w, -, -⟩ := h₁'
  have L : Lay (σ₁.gpr .a0) (σ₁.gpr .a2) (σ₁.gpr .a7) := Lay.of fc fs fw dcs dcw dsw a0 a2 a7w
  have dtw' : (⟨σ₁.gpr .a5, 16⟩ : Region).Disjoint ⟨σ₁.gpr .a7, 16⟩ := dtw.sub_right (Region.sub_prefix (by decide))
  let I₀ : State → Prop := fun s => finBsPre s ∧ s.gpr .a0 = σ₁.gpr .a0 ∧ s.gpr .a1 = σ₁.gpr .a1 ∧
    s.gpr .a2 = σ₁.gpr .a2 ∧ s.gpr .a3 = σ₁.gpr .a3 ∧ s.gpr .a4 = σ₁.gpr .a4 ∧ s.gpr .a5 = σ₁.gpr .a5 ∧
    s.gpr .a6 = σ₁.gpr .a6 ∧ s.gpr .a7 = σ₁.gpr .a7 ∧ s.sp = σ₁.sp
  refine ⟨I₀, ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨h₂, q3.symm, q4.symm, q5.symm, q6.symm, q7.symm,
    q8.symm, q9.symm, q10.symm, qsp.symm⟩, ?_⟩
  refine CT.seq (J := FSB σ₁) ?_ (fun s ⟨hs, e0, e1, e2, e3, e4, e5, e6, e7, esp⟩ =>
    WP.mono finMv_ok fun s₀ ⟨t2, a6, ho, k⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.a6, .a7])
        (.block [mov .t2 .a6, mov .a6 .a7]) h).isSome = true := ⟨_, by taint_decide⟩
    exact CT.taintEq (I := I₀) _ σ₁.gpr σ₁.sp (fun s ⟨_, _, _, _, _, _, _, e6, e7, esp⟩ =>
      ⟨esp, by simp [e6, e7]⟩) hc
  · obtain ⟨hx, hb⟩ := finBs_pre hs ⟨t2, a6, ho, k⟩
    exact ⟨⟨_, hx⟩, hb, by rw [ho _ (by decide) (by decide), e0], by rw [ho _ (by decide) (by decide), e1],
      by rw [ho _ (by decide) (by decide), e2], by rw [ho _ (by decide) (by decide), e3],
      by rw [ho _ (by decide) (by decide), e4], by rw [ho _ (by decide) (by decide), e5], by rw [a6, e7],
      by rw [t2, e6], by rw [k.sp, esp]⟩
  let FB := FinIB (σ₁.gpr .a6) (σ₁.gpr .a0) (σ₁.gpr .a2) (σ₁.gpr .a7) σ₁.sp (σ₁.gpr .a1).toNat (σ₁.gpr .a3)
    (σ₁.gpr .a4) (σ₁.gpr .a5)
  refine CT.seq (J := FB) ?_ (fun s ⟨⟨_, hx⟩, hb, e0, e1, e2, e3, e4, e5, e6, e8, esp⟩ => by
    have := finB_FIB hx hb
    rw [e0, e1, e2, e3, e4, e5, e6, e8, esp] at this
    exact this) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint
        (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .t2]) (.block (finEntryB true)) h).isSome = true :=
      ⟨_, by taint_decide⟩
    exact CT.taintEq _ (fun r => if r = .a6 then σ₁.gpr .a7 else if r = .t2 then σ₁.gpr .a6 else σ₁.gpr r) σ₁.sp
      (fun s ⟨_, _, e0, e1, e2, e3, e4, e5, e6, e8, esp⟩ => ⟨esp, by simp [e0, e1, e2, e3, e4, e5, e6, e8]⟩) hc
  let FI := FinI (σ₁.gpr .a0) (σ₁.gpr .a2) (σ₁.gpr .a7) σ₁.sp (σ₁.gpr .a1).toNat (σ₁.gpr .a3) (σ₁.gpr .a4)
    (σ₁.gpr .a5)
  refine CT.seq (J := FI)
    ((finTagB_ct L (o := 0) (.inl rfl) hR).mono fun s ⟨V, a, b, d, e, f, g, _, he, _, hb⟩ =>
      ⟨V, a, b, d, e, f, g, he, hb⟩)
    (fun s ⟨V, a, b, d, e, f, g, i, he, hT, hb⟩ => WP.mono (WP.with_rdwr (finTagB_ok (L.v a b d) (o := 0) (.inl rfl)
      (a := List.replicate ((σ₁.gpr .a3).toNat % 16) 0) (ct := List.replicate (σ₁.gpr .a4).toNat 0) he e hR rfl
      (by simp [f]) (by simp [g]) fun hbs => (hb hbs).2)) fun s' ⟨fo, _, wr, _⟩ =>
        ⟨V, a, b, d, e, f, g, i, fo.env, by rw [wr]; exact hT⟩) ?_
  refine CT.seq (J := fun s => s.gpr .s0 = σ₁.gpr .a7 ∧ s.sp = σ₁.sp) ?_
    (fun s ⟨V, a, b, d, e, f, g, i, he, hT⟩ => WP.mono (tagOut_ok he (by rw [i]; exact hT)
      (by rw [i, d]; exact dtw')) fun s' ⟨_, _, hg, hk⟩ =>
        ⟨by rw [hg _ (by decide), he.s0, d], by rw [hk.sp, he.sp]⟩) ?_
  · obtain ⟨_, hc⟩ := tagOut_taint
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, d₁, _, _, _, i₁, h₁, _⟩ ⟨_, _, _, d₂, _, _, _, i₂, h₂, _⟩ =>
      ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), i₁, i₂]
    · rw [h₁.s0, h₂.s0, d₁, d₂]
  obtain ⟨_, hc⟩ := restore_taint
  exact CT.taintEq _ (fun _ => σ₁.gpr .a7) σ₁.sp (fun s ⟨e31, esp⟩ => ⟨esp, by simp [e31]⟩) hc

/-! ## `verify` -/

theorem verBs_pre {σ s₀ : State} (h : verBsPre σ) (h0 : BsPreOut σ s₀) :
    verPreX [⟨σ.gpr .a7, 1248⟩, args σ 1] s₀ ∧ BsAtW s₀ .a7 := by
  obtain ⟨hrd, hwr, dcs, dcw, dst, dsw, dtw, dbs, dbw, fc, fs, ft, fw, hR, ⟨hsa, hsp, k1, k2, k3, k4, k5, -⟩,
    a0, a2, a7w, a7b, hsl⟩ := h
  obtain e0 := h0.other .a0 (by decide) (by decide)
  obtain e1 := h0.other .a1 (by decide) (by decide)
  obtain e2 := h0.other .a2 (by decide) (by decide)
  obtain e5 := h0.other .a5 (by decide) (by decide)
  obtain e6 := h0.other .a6 (by decide) (by decide)
  obtain k := h0.keeps
  have hR14 : (σ.gpr .a1).toNat ≤ 14 := by rcases hR with h | h | h <;> omega_using [h]
  refine ⟨?_, ?_⟩
  · simp only [verPreX, stkOk, stkAll, e0, e1, e2, e5, e6, h0.a7, k.rd, k.wr, k.sp, and_true]
    exact ⟨hrd, hwr, dcs, dcw, dst, dsw, dtw, fc, fs, ft, fw, hR, ⟨hsa, hsp, k1, k2, k3, k4⟩, a0, a2, a7w⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h0.t2, k.rd, hrd]; exact covers_prefix (k := 1248) (covers_mem (by simp)) (by decide)
    · rw [h0.t2]; exact a7b
    · rw [h0.t2, e2]; exact dbs.sub_left (Region.sub_prefix (by decide))
    · rw [h0.t2, h0.a7]; exact dbw.sub_left (Region.sub_prefix (by decide))
    · rw [h0.t2, k.sp]; exact k5.symm.sub_left (Region.sub_prefix (by decide))
    · rw [h0.t2, e1, e0, k.mem]; exact keysAt_of_sliced hR14 hsl

theorem verBs_in {σ : State} (h : verBsPre σ) : InRegions (σ.rd ++ σ.wr) (σ.sp + BitVec.ofNat 64 0) 8 := by
  obtain ⟨hrd, -⟩ := h
  refine ⟨args σ 1, List.mem_append_left _ (by rw [hrd]; simp), ?_⟩
  simp only [args, stackArgAddr]
  exact Region.contains_self _ _

theorem verBs_sa {σ : State} (h : verBsPre σ) : σ.sp.toNat % 16 = 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨hsa, -⟩, -⟩ := h
  exact hsa

theorem streamVerifyBs_wp [VG.Proof.Gcm.RISCV64.GhashLaw] {σ : State} (h : streamVerifyBsRISCV64.pre σ) :
    WP isa streamVerifyBs σ fun s' => abiPreserved σ s' ∧ streamVerifyBsRISCV64.post σ s' := by
  have h' : verBsPre σ := h
  refine WP.seq (WP.mono (bsPre_ok (verBs_sa h') (verBs_in h')) fun s₀ ⟨t2, a7, ho, k⟩ => ?_)
  obtain h0 : BsPreOut σ s₀ := ⟨t2, a7, ho, k⟩
  obtain ⟨hx, hb⟩ := verBs_pre h' h0
  refine WP.mono (streamVerifyB_wp hx fun _ => hb) fun s' ⟨ha, hp⟩ => ⟨h0.abi ha, ?_⟩
  simp only [streamVerifyBsRISCV64, streamVerifyRISCV64] at hp ⊢
  rwa [ho .a0 (by decide) (by decide), ho .a1 (by decide) (by decide), ho .a2 (by decide) (by decide),
    ho .a3 (by decide) (by decide), ho .a4 (by decide) (by decide), ho .a5 (by decide) (by decide),
    ho .a6 (by decide) (by decide), k.mem] at hp

/-- After `bsPre`, in terms of the first run's arguments. -/
def SVB (σ : State) (s : State) : Prop :=
  (∃ ex, verPreX ex s) ∧ BsAtW s .a7 ∧ s.gpr .a0 = σ.gpr .a0 ∧ s.gpr .a1 = σ.gpr .a1 ∧
    s.gpr .a2 = σ.gpr .a2 ∧ s.gpr .a3 = σ.gpr .a3 ∧ s.gpr .a4 = σ.gpr .a4 ∧ s.gpr .a5 = σ.gpr .a5 ∧
    s.gpr .a6 = σ.gpr .a6 ∧ s.gpr .a7 = stackArg σ 0 ∧ s.gpr .t2 = σ.gpr .a7 ∧ s.sp = σ.sp

theorem verB_VIB {ex : List Region} {s₀ : State} (h : verPreX ex s₀) (hb : BsAtW s₀ .a7) :
    WP isa (.block (verEntryB true)) s₀ (VerIB true (s₀.gpr .t2) (s₀.gpr .a0) (s₀.gpr .a2) (s₀.gpr .a7) s₀.sp
      (s₀.gpr .a1).toNat (s₀.gpr .a3) (s₀.gpr .a4) (s₀.gpr .a5) (s₀.gpr .a6).toNat) := by
  obtain L₀ := verLay h
  obtain hR := ver_R h
  refine WP.mono (ver1B_wp' (bs := true) (ver_W h) (ver_al h)) fun s₁ ⟨h1, h17⟩ => ?_
  have hT : Covers [⟨s₀.gpr .a5, (s₀.gpr .a6).toNat⟩] (s₁.rd ++ s₁.wr) := by
    rw [h1.en.keeps.rd, h1.en.keeps.wr, h.1]; exact covers_mem (List.mem_append_left _ (by simp))
  have hTd : (⟨s₀.gpr .a5, (s₀.gpr .a6).toNat⟩ : Region).Disjoint ⟨s₀.gpr .a7, 2560⟩ := h.2.2.2.2.2.2.1
  refine ⟨s₁.gpr, h1.s2, h1.s1, h1.s0, by rw [h1.s3, BitVec.ofNat_toNat, BitVec.setWidth_eq], h1.s10, h1.s11, h1.s9,
    by rw [h1.s8, BitVec.ofNat_toNat, BitVec.setWidth_eq], ver_env h h1, hT, hTd, fun _ => ⟨h17 rfl, ?_⟩⟩
  rw [h17 rfl, h1.s2, h1.s1, h1.s0]
  exact hb.bkIn L₀ hR h1.en.keeps.rd h1.en.frame

theorem streamVerifyBs_ct [VG.Proof.Gcm.RISCV64.GhashLaw] :
    ConstantTime isa streamVerifyBsRISCV64.pre streamVerifyBsRISCV64.pub streamVerifyBs := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  have h₁' : verBsPre σ₁ := h₁
  obtain ⟨-, -, dcs, dcw, -, dsw, -, -, -, fc, fs, -, fw, hR, -, a0, a2, a7w, -, -⟩ := h₁'
  have L : Lay (σ₁.gpr .a0) (σ₁.gpr .a2) (stackArg σ₁ 0) := Lay.of fc fs fw dcs dcw dsw a0 a2 a7w
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, qsp, qa⟩ := hq
  let I₀ : State → Prop := fun s => verBsPre s ∧ onePub 1 σ₁ s
  refine ⟨I₀, ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩,
    ⟨h₂, q0, q1, q2, q3, q4, q5, q6, q7, qsp, qa⟩, ?_⟩
  refine CT.seq (J := SVB σ₁) ?_ (fun s ⟨hs, hq⟩ => WP.mono (bsPre_ok (verBs_sa hs) (verBs_in hs))
    fun s₀ ⟨t2, a7, ho, k⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.a7]) (.block bsPre) h).isSome = true :=
      ⟨_, by taint_decide⟩
    exact CT.taintEq _ σ₁.gpr σ₁.sp (fun s ⟨_, _, _, _, _, _, _, _, q7, qsp, _⟩ =>
      ⟨qsp.symm, by simp [q7]⟩) hc
  · obtain ⟨hx, hb⟩ := verBs_pre hs ⟨t2, a7, ho, k⟩
    obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, qsp, qa⟩ := hq
    exact ⟨⟨_, hx⟩, hb, by rw [ho _ (by decide) (by decide), q0], by rw [ho _ (by decide) (by decide), q1],
      by rw [ho _ (by decide) (by decide), q2], by rw [ho _ (by decide) (by decide), q3],
      by rw [ho _ (by decide) (by decide), q4], by rw [ho _ (by decide) (by decide), q5],
      by rw [ho _ (by decide) (by decide), q6], by rw [a7, qa 0 (by decide)], by rw [t2, q7], by rw [k.sp, qsp]⟩
  let tl := (σ₁.gpr .a6).toNat
  let VB := VerIB true (σ₁.gpr .a7) (σ₁.gpr .a0) (σ₁.gpr .a2) (stackArg σ₁ 0) σ₁.sp (σ₁.gpr .a1).toNat
    (σ₁.gpr .a3) (σ₁.gpr .a4) (σ₁.gpr .a5) tl
  refine CT.seq (J := VB) ?_ (fun s ⟨⟨_, hx⟩, hb, e0, e1, e2, e3, e4, e5, e6, e7, e8, esp⟩ => by
    have := verB_VIB hx hb
    rw [e0, e1, e2, e3, e4, e5, e6, e7, e8, esp] at this
    exact this) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint
        (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t2]) (.block (verEntryB true)) h).isSome =
        true := ⟨_, by taint_decide⟩
    exact CT.taintEq _ (fun r => if r = .a7 then stackArg σ₁ 0 else if r = .t2 then σ₁.gpr .a7 else σ₁.gpr r) σ₁.sp
      (fun s ⟨_, _, e0, e1, e2, e3, e4, e5, e6, e7, e8, esp⟩ => ⟨esp, by simp [e0, e1, e2, e3, e4, e5, e6, e7, e8]⟩) hc
  -- the tag length
  let ok := Spec.Gcm.tagLenOk tl
  let J : State → Prop := fun s => VB s ∧ s.gpr .s5 = BitVec.ofNat 64 (if ok then 1 else 0)
  refine CT.seq (J := J) ?_ (fun s ⟨V, a, b, d, e, f, g, i, j, he, hT, hTd, hb⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := tagLenOk_taint
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, _, _, _, j₁, h₁, _⟩ ⟨_, _, _, _, _, _, _, _, j₂, h₂, _⟩ =>
      ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_singleton] at hr; subst hr
    rw [h₁.fr _ (by decide), h₂.fr _ (by decide), j₁, j₂]
  · refine WP.mono (tagLenOk_ok (by rw [he.fr _ (by decide), j]) (σ₁.gpr .a6).isLt) fun s' ⟨h25, hg, hk⟩ =>
      ⟨⟨V, a, b, d, e, f, g, i, j, he.keep (fun r hr => hg r (by revert r; decide) (by revert r; decide))
        hk.sp hk.rd hk.wr, by rw [hk.rd, hk.wr]; exact hT, hTd,
        fun hbs => ⟨(hb hbs).1, ((hb hbs).2.of_eq hk.rd hk.wr).memEq hk.mem⟩⟩, h25⟩
  have ev : ∀ s, J s → isa.eval (.zero .s5) s = some (decide ((if ok then 1 else 0) = 0)) :=
    fun s h => eval_zero h.2 (by split <;> decide)
  refine CT.seq (J := fun s => s.gpr .s0 = stackArg σ₁ 0 ∧ s.sp = σ₁.sp) ?_ (fun s hs => ?_) ?_
  · refine CT.ite _ ev (fun hb => ?_) (fun hb => ?_)
    · obtain ⟨_, hc⟩ := li3_taint
      exact CT.taint _ (fun s₁ s₂ ⟨⟨_, _, _, _, _, _, _, _, _, h₁, _⟩, _⟩ ⟨⟨_, _, _, _, _, _, _, _, _, h₂, _⟩, _⟩ =>
        ⟨h₁.sp.trans h₂.sp.symm, fun r hr => by simp at hr⟩) hc
    · have hok : ok = true := by cases e : ok <;> simp_all
      obtain ⟨t1, t16⟩ := tagLenOk_bounds hok
      exact (verOkB_ct L hR t1 t16).mono fun s h => h.1
  · refine WP.ite _ (ev s hs) (fun hb => ?_) (fun hb => ?_)
    · obtain ⟨⟨V, _, _, d, _, _, _, _, _, he, _⟩, _⟩ := hs
      have h₀ : WP isa (.block [.li .a0 0]) s fun s' => (∀ r, r ≠ .a0 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
        crun [Int.reduceNatCast']
        exact ⟨fun r a => by simp [a], ⟨rfl, rfl, rfl, rfl⟩⟩
      exact WP.mono h₀ fun s' ⟨hg, hk⟩ => ⟨by rw [hg _ (by decide), he.s0, d], by rw [hk.sp, he.sp]⟩
    · have hok : ok = true := by cases e : ok <;> simp_all
      obtain ⟨t1, t16⟩ := tagLenOk_bounds hok
      exact verOkB_wp L hR t1 t16 hs.1
  obtain ⟨_, hc⟩ := restore_taint
  exact CT.taintEq _ (fun _ => stackArg σ₁ 0) σ₁.sp (fun s ⟨e31, esp⟩ => ⟨esp, by simp [e31]⟩) hc

end VG.Proof.AesGcm.RISCV64
