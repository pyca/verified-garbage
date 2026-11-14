module

public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.Bytes
public import VerifiedGarbage.Proof.MdStream.RISCV64.Common
public import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.MdStream.RISCV64.Words
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # DSA parameter search on RISC-V: a hash of one block

As on PPC64LE (`Proof/Dsa/PPC64LE/Gen/Hash.lean`). `hash Gh dst`
(`Impl/Dsa/RISCV64/ParameterSearch.lean`) hashes the block at `sMsg`: the
initial hash value into `sState` (`initAt_ok`), the compression function on
it, with 80 octets of scratch at `sCS`, and the hash value's words big-endian
at `dst` (`MdStream.RISCV64.outBE_ok`). `HashOk Gh` is what the proof needs
of the hash function: its compression function verified, as the streaming
proofs see it, and its digest of a message of fewer than 56 bytes as that
compression of its one padded block.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.PSearch
open VG VG.RISCV64 VG.RISCV64.Steps VG.Proof.MdStream VG.Proof.MdStream.RISCV64
open VG.Impl.Dsa.RISCV64.ParameterSearch
open VG.Impl.Words.RISCV64 (li32 storeLE32)
open VG.RISCV64.ByteLoad (li32_ok storeLE32_ok)

/-! ## The initial hash value -/

/-- The first `k` words of `iv` stored at `A`. -/
structure InitJ (iv : List (BitVec 32)) (A : Addr) (s₀ : State) (k : Nat) (s : State) : Prop where
  a0 : s.gpr .a0 = A
  keep : Keep [.t0, .t1] s₀ s
  sp : s.sp = s₀.sp
  frame : Frame [⟨A, 4 * iv.length⟩] s₀.mem s.mem
  words : ∀ j < k, s.mem.readW (A + BitVec.ofNat 64 (4 * j)) 32 = iv[j]!

theorem readW_writeW_word (m : Mem) (p : Addr) (v : BitVec 32) {j k : Nat} (hj : j < 512)
    (hk : k < 512) (h : j ≠ k) :
    (m.writeW (p + BitVec.ofNat 64 (4 * k)) v).readW (p + BitVec.ofNat 64 (4 * j)) 32 =
    m.readW (p + BitVec.ofNat 64 (4 * j)) 32 :=
  Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide)

/-- `initWords iv` at `a0 = A`, with the words writable: they hold `iv`. -/
theorem initAt_ok (iv : List (BitVec 32)) (hl : iv.length ≤ 8) {s₀ : State} {A : Addr}
    (h0 : s₀.gpr .a0 = A) (hw : ∀ k < iv.length, InRegions s₀.wr (A + BitVec.ofNat 64 (4 * k)) 4) :
    WP isa (Impl.MdStream.RISCV64.initWords iv) s₀ (InitJ iv A s₀ iv.length) := by
  refine wp_range_flatMap (M := isa) (InitJ iv A s₀) (fun k s hk h => ?_) iv.length (Nat.le_refl _) s₀
    ⟨h0, Keep.refl _ _, rfl, Frame.refl _ _, fun _ h => absurd h (by omega)⟩
  rw [WP.block_append_iff]
  refine WP.mono (li32_ok _) fun s₁ e₁ => ?_
  subst e₁
  refine WP.mono (storeLE32_ok (by decide) (by decide) (by omega) ?_) fun s₂ e₂ => ?_
  · rw [RegUpd.wr_write, RegUpd.gpr_write_of_ne _ _ (by decide), h.a0, h.keep.2.2]
    exact hw k hk
  subst e₂
  refine ⟨?_, ⟨fun r hr => ?_, h.keep.2.1, h.keep.2.2⟩, h.sp, ?_, fun j hj => ?_⟩
  · simp only [RegUpd.gpr_write, reduceCtorEq, ↓reduceIte, h.a0]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write_of_ne _ _ hr.2, RegUpd.gpr_write_of_ne _ _ hr.1]
    exact h.keep.1 r (by simp [hr.1, hr.2])
  · simp only [RegUpd.mem_write, RegUpd.gpr_write, reduceCtorEq, ↓reduceIte, h.a0]
    exact h.frame.writeW List.mem_cons_self _ (Offset.contains_base _ (by omega) (by omega))
  · simp only [RegUpd.mem_write, RegUpd.gpr_write, reduceCtorEq, ↓reduceIte, h.a0, lo32_sext]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [readW_writeW_word _ _ _ (by omega) (by omega) (by omega)]
      exact h.words j hj
    · exact Mem.readW_writeW_self32 _ _ _

/-! ## What the proof needs of the hash function -/

/-- The block of a message of fewer than 56 bytes. -/
def blk {N : Nat} (md : MdStream.Md 64 N 8) (msg : List Byte) : List Byte :=
  msg ++ [0x80] ++ List.replicate (55 - msg.length) 0 ++ md.lenBytes msg.length

structure HashOk (Gh : Hash) where
  md : MdStream.Md 64 (4 * Gh.k) 8
  hk : Gh.k ≤ 8
  hk0 : 0 < Gh.k
  ivLen : Gh.iv.length = Gh.k
  callee : CalleeOk md Gh.code
  ct : ConstantTime isa (compressK md).pre (compressK md).pub Gh.code
  /-- The initial hash value. -/
  H0 : md.HV
  iv : ∀ (m : Mem) (p : Addr), (∀ j < Gh.iv.length, m.readW (p + BitVec.ofNat 64 (4 * j)) 32 = Gh.iv[j]!) →
    md.stateAt m p = H0
  digest : ∀ (m : Mem) (p : Addr), md.digest (md.stateAt m p) =
    (List.range Gh.k).flatMap fun j => MdStream.bytes32 true (m.readW (p + BitVec.ofNat 64 (4 * j)) 32)
  /-- The hash function. -/
  H : List Byte → List Byte
  hash : ∀ msg, msg.length < 56 → H msg = md.digest (md.compress H0 (md.parse fun t => (blk md msg).getD t 0))
  /-- The taint analysis of the code before and after the call, which
  depends on the hash function only through its initial hash value and its
  words: checked on each instance. -/
  cert1 : ∃ hc, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s6])
    (.seq (.block [scr .a0 sState]) (Impl.MdStream.RISCV64.initWords Gh.iv)) hc).isSome = true
  cert3 : ∀ dst, ∃ hc, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s6])
    (.block ([scr .s1 sState, scr .s3 dst] ++ Impl.MdStream.RISCV64.outBE Gh.k)) hc).isSome = true

/-! ## The pieces -/

/-- The registers the hash changes before the call. -/
abbrev hRegs : List Reg := [.a0, .a1, .a2, .a3, .t0, .t1]

/-- The registers the hash changes. -/
abbrev hashRegs : List Reg := .s1 :: .s3 :: volatile

section
variable {G : GP} {STK : Nat} {Gh : Hash} (HO : HashOk Gh)

/-- After the initial hash value. -/
abbrev H1 (F : State → State → Prop) (σ s : State) : Prop :=
  ∃ s₀, F σ s₀ ∧ Keep hRegs s₀ s ∧ s.sp = s₀.sp ∧ Frame [G.rs sState (4 * Gh.k)] s₀.mem s.mem ∧
    (∀ j < Gh.iv.length, s.mem.readW (G.sa sState + BitVec.ofNat 64 (4 * j)) 32 = Gh.iv[j]!)

theorem H1.pub {F : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, F σ s → SS G STK σ (c σ) s) :
    Pub G (H1 (G := G) (Gh := Gh) F) := fun σ s ⟨s₀, h₀, K, sp, _⟩ =>
  ⟨by rw [K.gpr (by decide)]; exact (hF σ s₀ h₀).gi.s6, by rw [sp]; exact (SS.pub hF σ s₀ h₀).2⟩

include HO in
theorem hash1_vp {F : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, F σ s → SS G STK σ (c σ) s) :
    VP F (.seq (.block [scr .a0 sState]) (Impl.MdStream.RISCV64.initWords Gh.iv))
      (H1 (G := G) (Gh := Gh) F) := by
  refine VP.pub (SS.pub hF) [] HO.cert1 (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s hs => ?_
  have h := hF σ s hs
  have gi := h.gi
  have fit := gi.scrFit
  have hE := gi.hEnd_le
  have big := gi.scrBig
  have ln := gi.lens
  have hk := HO.hk
  have il := HO.ivLen
  refine WP.seq (wp_addi (show sState < 2048 by decide) fun s₁ u₁ => WP.block_nil ?_)
  have a0 : s₁.gpr .a0 = G.sa sState := by rw [u₁.gpr, gi.s6]
  refine WP.mono (initAt_ok Gh.iv (by omega) a0 (fun j hj => by
      rw [u₁.wr, GP.sa_add]; exact gi.inScr (by simp only [hEnd, fSave, sState] at hE ⊢; omega) (by decide)))
      fun t I => ⟨s, hs, ?_, by rw [I.sp, u₁.sp], ?_, I.words⟩
  · refine ⟨fun r hr => ?_, by rw [I.keep.2.1, u₁.rd], by rw [I.keep.2.2, u₁.wr]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [I.keep.1 r (by simp [hr.2.2.2.2.1, hr.2.2.2.2.2]), u₁.other _ hr.1]
  · rw [← u₁.mem, ← il]; exact I.frame

/-- With the compression function's arguments. -/
abbrev H1c (F : State → State → Prop) (σ s : State) : Prop :=
  H1 (G := G) (Gh := Gh) F σ s ∧ s.gpr .a0 = G.sa sState ∧ s.gpr .a1 = G.sa sMsg ∧ s.gpr .a2 = 1 ∧
    s.gpr .a3 = G.sa sCS

theorem hash2a_vp {F : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, F σ s → SS G STK σ (c σ) s) :
    VP (H1 (G := G) (Gh := Gh) F) (.block [scr .a0 sState, scr .a1 sMsg, .li .a2 1, scr .a3 sCS])
      (H1c (G := G) (Gh := Gh) F) := by
  refine VP.pub (H1.pub hF) [] ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6])
    (.block [scr .a0 sState, scr .a1 sMsg, .li .a2 1, scr .a3 sCS]), by kernel_rfl⟩
    (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s hs => ?_
  have h6 := (H1.pub (Gh := Gh) hF σ s hs).1
  obtain ⟨s₀, h₀, K, sp, F₀, W⟩ := hs
  simp only [scr]
  refine wp_addi (show sState < 2048 by decide) fun s₁ u₁ => wp_addi (show sMsg < 2048 by decide) fun s₂ u₂ =>
    wp_li (imm := 1) (by decide) fun s₃ u₃ => wp_addi (show sCS < 2048 by decide) fun t u => WP.block_nil
      ⟨⟨s₀, h₀, ?_, by rw [u.sp, u₃.sp, u₂.sp, u₁.sp, sp], by rw [u.mem, u₃.mem, u₂.mem, u₁.mem]; exact F₀,
        by rw [u.mem, u₃.mem, u₂.mem, u₁.mem]; exact W⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun r hr => ?_, by rw [u.rd, u₃.rd, u₂.rd, u₁.rd, K.2.1], by rw [u.wr, u₃.wr, u₂.wr, u₁.wr, K.2.2]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u.other _ hr.2.2.2.1, u₃.other _ hr.2.2.1, u₂.other _ hr.2.1, u₁.other _ hr.1, K.gpr (by simpa using hr)]
  · rw [u.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h6]
  · rw [u.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h6]
  · rw [u.other _ (by decide), u₃.gpr]; rfl
  · rw [u.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h6]

/-- After the compression. -/
abbrev H2 (F : State → State → Prop) (σ s : State) : Prop :=
  ∃ s₀, F σ s₀ ∧ Keep volatile s₀ s ∧ s.sp = s₀.sp ∧
    Frame [G.rs sState (4 * Gh.k), G.rs sCS 80] s₀.mem s.mem ∧
    HO.md.stateAt s.mem (G.sa sState) = HO.md.compress HO.H0 (HO.md.blockAt s₀.mem (G.sa sMsg))

theorem H2.pub {F : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, F σ s → SS G STK σ (c σ) s) :
    Pub G (H2 HO (G := G) F) := fun σ s ⟨s₀, h₀, K, sp, _⟩ =>
  ⟨by rw [K.gpr (by decide)]; exact (hF σ s₀ h₀).gi.s6, by rw [sp]; exact (SS.pub hF σ s₀ h₀).2⟩

theorem hash2b_vp {F : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, F σ s → SS G STK σ (c σ) s) :
    VP (H1c (G := G) (Gh := Gh) F) (.call Gh.name Gh.code) (H2 HO (G := G) F) := by
  -- The regions the compression function is given.
  let rd : List Region := [⟨G.sa sMsg, 64 * 1⟩]
  let wr : List Region := [⟨G.sa sState, 4 * Gh.k⟩, ⟨G.sa sCS, 80⟩]
  have ec : ∀ {s : State} {r : Reg}, r ∉ linkRegs → (s.callEntry.withRegions rd wr).gpr r = s.gpr r :=
    fun h => by rw [State.withRegions_gpr, State.callEntry_gpr _ h]
  have facts : ∀ σ s, H1c (G := G) (Gh := Gh) F σ s →
      (compressK HO.md).pre (s.callEntry.withRegions rd wr) ∧ Covers (rd ++ wr) (s.rd ++ s.wr) ∧
        Covers wr s.wr := by
    intro σ s ⟨⟨s₀, hs₀, K, _, _, _⟩, e0, e1, e2, e3⟩
    have h := hF σ s₀ hs₀
    have gi := h.gi
    have fit := gi.scrFit
    have hE := gi.hEnd_le
    have big := gi.scrBig
    have ln := gi.lens
    have hk := HO.hk
    have hk0 := HO.hk0
    have n0 : sState = 384 := rfl
    have n1 : sMsg = 320 := rfl
    have n2 : sCS = 416 := rfl
    have hE' : hEnd = 280 := rfl
    have ws : s.wr = s₀.wr := K.2.2
    have hw : Covers wr s.wr := by
      rw [ws]
      refine Covers.pair (Covers.one (gi.inScr ?_ ?_)) (Covers.one (gi.inScr ?_ ?_)) <;> omega
    refine ⟨?_, Covers.append_left (Covers.right (Covers.one (by
      rw [ws]; exact gi.inScr (by omega) (by omega)))) hw.right, hw⟩
    simp only [compressK, State.withRegions_rd, State.withRegions_wr, ec (r := .a0) (by decide),
      ec (r := .a1) (by decide), ec (r := .a2) (by decide), ec (r := .a3) (by decide), e0, e1, e2, e3]
    rw [show (1 : BitVec 64).toNat = 1 from rfl]
    refine ⟨rfl, rfl, gi.sdisj ?_ ?_ ?_, gi.sdisj ?_ ?_ ?_, gi.sdisj ?_ ?_ ?_, gi.al8 (by decide) ?_⟩ <;> omega
  refine VP.of_ct (fun σ₁ σ₂ => RelCT.call HO.callee.verified HO.ct rd wr fun s₁ s₂ ⟨h₁, h₂⟩ => ?_)
    fun σ s hs => ?_
  · obtain ⟨p₁, c₁, w₁⟩ := facts σ₁ s₁ h₁
    obtain ⟨p₂, c₂, w₂⟩ := facts σ₂ s₂ h₂
    obtain ⟨⟨t₁, f₁, K₁, sp₁, -, -⟩, a0, a1, a2, a3⟩ := h₁
    obtain ⟨⟨t₂, f₂, K₂, sp₂, -, -⟩, b0, b1, b2, b3⟩ := h₂
    refine ⟨p₁, p₂, ⟨?_, ?_, ?_, ?_, ?_⟩, c₁, w₁, c₂, w₂⟩
    · rw [ec (by decide), ec (by decide), a0, b0]
    · rw [ec (by decide), ec (by decide), a1, b1]
    · rw [ec (by decide), ec (by decide), a2, b2]
    · rw [ec (by decide), ec (by decide), a3, b3]
    · show s₁.sp = s₂.sp
      rw [sp₁, sp₂, (SS.pub hF _ _ f₁).2, (SS.pub hF _ _ f₂).2]
  · obtain ⟨p, cv, wv⟩ := facts σ s hs
    obtain ⟨⟨s₀, hs₀, K, sp₀, F₀, W⟩, e0, e1, e2, e3⟩ := hs
    have h := hF σ s₀ hs₀
    have gi := h.gi
    have fit := gi.scrFit
    have hE := gi.hEnd_le
    have hk := HO.hk
    have big := gi.scrBig
    have ln := gi.lens
    refine WP.call (k := compressK HO.md) HO.callee.verified p cv wv
      (fun s' hrd hwr hsp hf hg _ hpost => ?_) HO.callee.noFrames
    simp only [compressK, State.withRegions_mem, State.callEntry_mem,
      ec (r := .a0) (by decide), ec (r := .a1) (by decide), ec (r := .a2) (by decide), e0, e1, e2] at hpost
    rw [show (1 : BitVec 64).toNat = 1 from rfl, MdStream.Md.compressBlocks_one, HO.iv s.mem _ W] at hpost
    refine ⟨s₀, hs₀, ?_, by rw [hsp, sp₀], ?_, ?_⟩
    · refine ⟨fun r hr => ?_, by rw [hrd, K.2.1], by rw [hwr, K.2.2]⟩
      have hp : r ∈ preserved := by revert hr; cases r <;> decide
      rw [hg r hp, K.gpr (by revert hr; cases r <;> decide)]
    · refine (F₀.mono (rs' := [G.rs sState (4 * Gh.k), G.rs sCS 80]) fun r hr => by
        simp only [List.mem_singleton] at hr; simp [hr]).trans (hf.sub fun r hr => ?_)
      simp only [wr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨G.rs sState (4 * Gh.k), List.mem_cons_self, fun _ h => h⟩
      · exact ⟨G.rs sCS 80, by simp, fun _ h => h⟩
    · rw [hpost]
      refine congrArg (HO.md.compress HO.H0) ?_
      unfold VG.Proof.MdStream.Md.blockAt
      refine HO.md.parse_congr fun k hk => ?_
      exact F₀.bytes (R := G.rs sMsg 64) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        have n0 : sState = 384 := rfl
        have n1 : sMsg = 320 := rfl
        have hE' : hEnd = 280 := rfl
        exact gi.sdisj (by omega) (by omega) (by omega)) (by show 64 ≤ 2 ^ 64; decide) hk

/-- The block's bytes, as the compression function reads it. -/
theorem blockAt_eq {m : Mem} {p : Addr} {bs : List Byte} (h : Spec.Rsa.bytesAt m p 64 = bs) :
    HO.md.blockAt m p = HO.md.parse fun t => bs.getD t 0 := by
  unfold VG.Proof.MdStream.Md.blockAt
  refine HO.md.parse_congr fun k hk => ?_
  rw [← h]
  simp [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, hk]

theorem hash3_vp {F Q : State → State → Prop} {c : State → Cfg} {dst : Nat} {msg : State → List Byte}
    (hF : ∀ σ s, F σ s → SS G STK σ (c σ) s)
    (hm : ∀ σ s, F σ s → (msg σ).length < 56 ∧ Spec.Rsa.bytesAt s.mem (G.sa sMsg) 64 = blk HO.md (msg σ))
    (hd1 : sCS + 80 ≤ dst) (hd2 : dst + 32 ≤ 2048)
    (k : ∀ σ s t, F σ s → Keep hashRegs s t → t.sp = s.sp →
      Frame (G.rss [(sState, 32), (sCS, 80), (dst, 4 * Gh.k)]) s.mem t.mem →
      Spec.Rsa.bytesAt t.mem (G.sa dst) (4 * Gh.k) = HO.H (msg σ) → Q σ t) :
    VP (H2 HO (G := G) F) (.block ([scr .s1 sState, scr .s3 dst] ++ Impl.MdStream.RISCV64.outBE Gh.k)) Q := by
  refine VP.pub (H2.pub HO hF) [] (HO.cert3 dst) (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s hs => ?_
  obtain ⟨s₀, hs₀, K, sp₀, F₀, St⟩ := hs
  have h := hF σ s₀ hs₀
  have gi := h.gi
  have fit := gi.scrFit
  have hE := gi.hEnd_le
  have big := gi.scrBig
  have ln := gi.lens
  have hk := HO.hk
  have hk0 := HO.hk0
  have h6 : s.gpr .s6 = G.scr := by rw [K.gpr (by decide)]; exact gi.s6
  have n0 : sState = 384 := rfl
  have n2 : sCS = 416 := rfl
  have hE' : hEnd = 280 := rfl
  simp only [scr, List.cons_append, List.nil_append]
  refine wp_addi (show sState < 2048 by decide) fun s₁ u₁ => wp_addi (show dst < 2048 by omega) fun s₂ u₂ => ?_
  have a1 : s₂.gpr .s1 = G.sa sState := by rw [u₂.other _ (by decide), u₁.gpr, h6]
  have a3 : s₂.gpr .s3 = G.sa dst := by rw [u₂.gpr, u₁.other _ (by decide), h6]
  have rd₂ : s₂.rd = s₀.rd := by rw [u₂.rd, u₁.rd, K.2.1]
  have wr₂ : s₂.wr = s₀.wr := by rw [u₂.wr, u₁.wr, K.2.2]
  refine WP.mono (outBE_ok (n := Gh.k) (by omega) s₂
    (by rw [a1, rd₂, wr₂]; exact gi.inRdWr (by omega) (by omega))
    (by rw [a3, wr₂]; exact gi.inScr (by omega) (by omega))
    (by rw [a1, a3]; exact gi.sdisj (by omega) (by omega) (by omega)))
    fun t ⟨g, rd, wr, sp, m⟩ => ?_
  rw [a1, a3, u₂.mem, u₁.mem] at m
  have mt : t.mem = VG.WriteBytes.writeBytes s.mem (G.sa dst) (HO.md.digest (HO.md.stateAt s.mem (G.sa sState))) := by
    rw [m, HO.digest]
  have dl : (HO.md.digest (HO.md.stateAt s.mem (G.sa sState))).length = 4 * Gh.k := by
    rw [HO.digest, flat_length]
  refine k σ s₀ t hs₀ ⟨fun r hr => ?_, by rw [rd, rd₂], by rw [wr, wr₂]⟩
    (by rw [sp, u₂.sp, u₁.sp, sp₀]) ?_ ?_
  · have h1 : r ≠ .s1 := fun e => hr (by rw [e]; decide)
    have h3 : r ≠ .s3 := fun e => hr (by rw [e]; decide)
    have ht1 : r ≠ .t1 := fun e => hr (by rw [e]; decide)
    have ht2 : r ≠ .t2 := fun e => hr (by rw [e]; decide)
    rw [g r ht1 ht2, u₂.other _ h3, u₁.other _ h1, K.gpr (fun e => hr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ e)))]
  · show Frame [G.rs sState 32, G.rs sCS 80, G.rs dst (4 * Gh.k)] _ _
    refine (F₀.sub fun r hr => ?_).trans ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨G.rs sState 32, List.mem_cons_self, Offset.sub _ (Nat.le_refl _) (by omega)⟩
      · exact ⟨G.rs sCS 80, by simp, fun _ h => h⟩
    · rw [mt]
      refine (VG.WriteBytes.writeBytes_frame _ _ _ (R := G.rs dst (4 * Gh.k)) ?_).mono (by simp)
      rw [dl]; exact Region.contains_self _ _
  · obtain ⟨ml, hb⟩ := hm σ s₀ hs₀
    have e := VG.Proof.Sha256.Stream.bytesAt_writeBytes s.mem (G.sa dst) 0
      (HO.md.digest (HO.md.stateAt s.mem (G.sa sState))) (by rw [dl]; omega)
    rw [BitVec.add_zero, Nat.zero_add, dl] at e
    show Spec.Sha256.bytesAt _ _ _ = _
    rw [mt, e, St, blockAt_eq HO hb, ← HO.hash _ ml]; rfl

/-- `hash Gh dst`: the digest of the message whose block is at `sMsg` into `dst`. -/
theorem hash_vp {F Q : State → State → Prop} {c : State → Cfg} {dst : Nat} {msg : State → List Byte}
    (hF : ∀ σ s, F σ s → SS G STK σ (c σ) s)
    (hm : ∀ σ s, F σ s → (msg σ).length < 56 ∧ Spec.Rsa.bytesAt s.mem (G.sa sMsg) 64 = blk HO.md (msg σ))
    (hd1 : sCS + 80 ≤ dst) (hd2 : dst + 32 ≤ 2048)
    (k : ∀ σ s t, F σ s → Keep hashRegs s t → t.sp = s.sp →
      Frame (G.rss [(sState, 32), (sCS, 80), (dst, 4 * Gh.k)]) s.mem t.mem →
      Spec.Rsa.bytesAt t.mem (G.sa dst) (4 * Gh.k) = HO.H (msg σ) → Q σ t) :
    VP F (hash Gh dst) Q :=
  VP.assoc (VP.seq (hash1_vp HO hF)
    (VP.assoc (VP.seq (VP.seq (hash2a_vp hF) (hash2b_vp HO hF)) (hash3_vp HO hF hm hd1 hd2 k))))

end

end VG.Proof.Dsa.RISCV64.PSearch
