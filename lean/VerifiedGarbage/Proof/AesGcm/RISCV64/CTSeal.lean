module

public import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
public import VerifiedGarbage.Proof.AesGcm.RISCV64.CTOne
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Contract
import VerifiedGarbage.Proof.AesGcm.RISCV64.Crypt
import VerifiedGarbage.Proof.AesGcm.RISCV64.InitCT
import VerifiedGarbage.Proof.AesGcm.RISCV64.OneEntry
import VerifiedGarbage.Proof.AesGcm.RISCV64.Seal
import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamCrypt
import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamFinish
public import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTOne
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Contract
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Crypt
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.InitCT
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.OneEntry
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Seal
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamCrypt
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamFinish
meta import VerifiedGarbage.Proof.Gcm.Stream
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.AesGcm.RISCV64.CTFin
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTFin
public import VerifiedGarbage.Impl.AesGcm.RISCV64

/-!
# AES-GCM on RISCV64: `vg_aes_gcm_seal` is constant time

Untrusted: everything here is checked by Lean. The entry loads `W` from the
stack argument at `sp + 8`, a public address, and then saves our caller's
registers through it: its head is checked on its own, and the rest from the
arguments and `W` (`oneHead_ct`). The pieces follow (`CTOne.lean`), with the
tag's address `T` in `s9`, which the environment pins, and, between them,
the additional data absorbed, for `oneTag 0`.
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt zeros padLen)
open VG.Proof.Gcm (Absorbed)

/-- The entry of `seal`, from its precondition. -/
theorem sealEntry_wp {s₀ : State} (h : sealPre s₀) :
    WP isa (.block (oneEntry 8)) s₀ fun s₁ =>
      OneI (s₀.gpr .a0) (stackArg s₀ 1) s₀.sp (s₀.gpr .a1).toNat (s₀.gpr .a2) (s₀.gpr .a3).toNat (s₀.gpr .a4)
        (s₀.gpr .a5) (s₀.gpr .a6) (s₀.gpr .a7) s₁ ∧
      s₁.gpr .s4 = s₀.gpr .a2 ∧ s₁.gpr .s5 = BitVec.ofNat 64 (s₀.gpr .a3).toNat ∧
      s₁.gpr .s9 = stackArg s₀ 0 ∧ Covers [⟨stackArg s₀ 0, 16⟩] s₁.wr := by
  obtain ⟨hrd, hwr, dcd, dcW, dnd, dnW, dad, daW, ddt, ddW, ddA, dtW, dWA, fc, fn, fa, fd, fW, fsp, hR, hstk,
    ca, wa⟩ := h
  have hk₀ : StkOk (s₀.gpr .a0) (stackArg s₀ 1 + BitVec.ofNat 64 16) (stackArg s₀ 1) s₀.sp :=
    one_stk hstk (by simp) (by simp)
  have hC : Covers [⟨s₀.gpr .a0, 256⟩] (s₀.rd ++ s₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  have hW : Covers [⟨stackArg s₀ 1, 2560⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  have hA : Covers [args s₀ 2] (s₀.rd ++ s₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  have hTd : (⟨s₀.sp + BitVec.ofNat 64 0, 8⟩ : Region).Disjoint (oneR (stackArg s₀ 1)) :=
    ((dWA.sub_left (Lay.wSub (d := 128) (n := 120) (by decide))).sub_right
      (Region.sub_prefix (show 8 ≤ 8 * 2 by decide))).symm
  refine WP.mono (one1_wp (off := 8) (W := stackArg s₀ 1) (T := stackArg s₀ 0) (.inl rfl) hW wa hstk.1
    (args_in hA (by decide) (i := 1) (by decide)) rfl (args_in hA (by decide) (i := 0) (by decide)) rfl hTd)
    fun s₁ h1 => ?_
  have hk₁ := h1.keeps
  have toN : ∀ {x : BitVec 64}, x = BitVec.ofNat 64 x.toNat := fun {x} => by simp
  have hDw : Covers [⟨s₀.gpr .a6, (s₀.gpr .a7).toNat⟩] s₁.wr := by
    rw [hk₁.wr, hwr]; exact covers_mem (by simp)
  refine ⟨⟨s₁.gpr, h1.s2, h1.s1, h1.s0, by rw [h1.s3]; exact toN, by rw [h1.s7]; exact toN,
    h1.s10, h1.s11, one_env h1 hC hW hk₀, ?_, ?_, ⟨⟨covers_left hDw, (s₀.gpr .a7).isLt, fd,
      ddW.sub_right (Lay.wSub (by decide)), ddW, by rw [hk₁.sp]; exact hstk.buf (by simp)⟩, hDw, dcd⟩,
    h1.aad, h1.dat⟩, h1.s4, by rw [h1.s5]; exact toN, h1.s9, ?_⟩
  · exact ⟨by rw [hk₁.rd, hk₁.wr]; exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp)),
      (s₀.gpr .a3).isLt, fn, dnW.sub_right (Lay.wSub (by decide)), dnW, by rw [hk₁.sp]; exact hstk.buf (by simp)⟩
  · exact ⟨by rw [hk₁.rd, hk₁.wr]; exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp)),
      (s₀.gpr .a5).isLt, fa, daW.sub_right (Lay.wSub (by decide)), daW, by rw [hk₁.sp]; exact hstk.buf (by simp)⟩
  · rw [hk₁.wr, hwr]; exact covers_mem (by simp)

/-- The head of the entry: `W`, the stack argument at `sp + off`, into `t1`. -/
theorem oneA_ok {s₀ : State} {off : Nat} {W : Addr} (hoff : off = 8 ∨ off = 16) (hsa : s₀.sp.toNat % 16 = 0)
    (hWi : InRegions (s₀.rd ++ s₀.wr) (s₀.sp + BitVec.ofNat 64 off) 8)
    (hWv : s₀.mem.readW (s₀.sp + BitVec.ofNat 64 off) 64 = W) :
    WP isa (.block [.addSp .t1 0, .load .d .t1 .t1 off]) s₀ fun sA =>
      sA.gpr .t1 = W ∧ (∀ r, r ≠ .t1 → sA.gpr r = s₀.gpr r) ∧ Keeps s₀ sA := by
  refine Steps.wp_addSp (imm := 0) (by decide) fun sA uA => ?_
  refine Steps.wp_ld (off := off) (a := s₀.sp + BitVec.ofNat 64 off) (by omega) (by rw [uA.gpr, add_ofNat_zero])
    (Spill.al8 (by omega) (by omega)) (by rw [uA.rd, uA.wr]; exact hWi) fun sB uB => WP.block_nil ?_
  exact ⟨by rw [uB.gpr, uA.mem, hWv], fun r hr => by rw [uB.other r hr, uA.other r hr],
    ⟨by rw [uB.mem, uA.mem], by rw [uB.rd, uA.rd], by rw [uB.wr, uA.wr], by rw [uB.sp, uA.sp]⟩⟩

/-- The rest of the entry, after `W` is in `t1`. -/
abbrev oneRest : List Instr :=
  save .t1 ++ ([mov .s2 .a0, mov .s3 .a1, .addi .s1 .s0 16, mov .s4 .a2, mov .s5 .a3, mov .s7 .a3,
    .store .d .a4 .s0 aadO, mov .s10 .a5, .store .d .a6 .s0 dataO, mov .s11 .a7, .addSp .t1 0,
    .load .d .s9 .t1 0] : List Instr)

theorem oneEntry_eq (off : Nat) : oneEntry off = [.addSp .t1 0, .load .d .t1 .t1 off] ++ oneRest := by
  rw [oneEntry, List.append_assoc]

theorem oneHead_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [])
    (.block [.addSp .t1 0, .load .d .t1 .t1 8]) h).isSome = true := ⟨_, by taint_decide⟩

theorem oneRest_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint
    (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t1]) (.block oneRest) h).isSome = true :=
  ⟨_, by taint_decide⟩

section
variable {c W sp : Addr} {R : Nat} {Np : Addr} {n : Nat} {Ad A D Ln T : BitVec 64}

/-- `OneI`, with the tag's address `T` in `s9`, which the state may write. -/
def OneT (c W sp : Addr) (R : Nat) (Np : Addr) (n : Nat) (Ad A D Ln T : BitVec 64) (s : State) : Prop :=
  OneI c W sp R Np n Ad A D Ln s ∧ s.gpr .s9 = T ∧ Covers [⟨T, 16⟩] s.wr

theorem OneT.frame {s s' : State} (h : OneT c W sp R Np n Ad A D Ln T s) {V : Reg → BitVec 64}
    (hV : ∀ r ∈ frozen, V r = s.gpr r) (he : Env V sp s') (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hs : ∀ {d : Nat}, 232 ≤ d ∧ d + 8 ≤ 248 → ∀ r ∈ rs, (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r) :
    OneT c W sp R Np n Ad A D Ln T s' :=
  ⟨h.1.frame hV he hrd hwr hsp hf hs, (he.fr _ (by decide)).trans ((hV _ (by decide)).trans h.2.1),
    by rw [hwr]; exact h.2.2⟩

/-- Between `oneAad` and `oneTag`: the additional data `a` absorbed and padded. -/
def OneAbs (c W : Addr) (A : BitVec 64) (s : State) : Prop :=
  ∃ H : Block, ∃ a : List Byte, blockAt s.mem (c + BitVec.ofNat 64 240) = H ∧ A.toNat = a.length ∧
    Absorbed s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H
      (a ++ zeros (padLen a.length))

variable (L : Lay c (W + BitVec.ofNat 64 16) W) (hR : R = 10 ∨ R = 12 ∨ R = 14)
  (hTW : (⟨T, 16⟩ : Region).Disjoint ⟨W, 16⟩)
include L hR hTW

/-- `seal` after its entry. -/
theorem sealBody_ct : CT (fun s => OneT c W sp R Np n Ad A D Ln T s ∧ s.gpr .s4 = Np ∧
    s.gpr .s5 = BitVec.ofNat 64 n)
    (.seq oneAad (.seq oneCrypt (.seq (oneTag 0) (.seq (.block tagOut) (.block restore))))) := by
  -- `oneAad`
  refine CT.seq (J := fun s => OneT c W sp R Np n Ad A D Ln T s ∧ OneAbs c W A s)
    ((oneAad_ct L).mono fun s ⟨⟨hO, _⟩, h24, h25⟩ => ⟨hO, h24, h25⟩)
    (fun s ⟨hT, h24, h25⟩ => ?_) ?_
  · obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := hT.1
    refine WP.mono (WP.with_rdwr (oneAad_ok (L.v a b d) (A := Ad) he rfl h24 h25 f (by rw [b, d]; exact hN)
      (by rw [b, d, i]; exact hA) (by rw [d]; exact sa))) fun s' ⟨oa, rd, wr, sp'⟩ =>
        ⟨hT.frame (fun r hr => (he.fr r hr).symm) oa.env rd wr sp' oa.frame
          (fun hd' => by rw [← d]; exact slot_j0 (L.v a b d) he.stk' hd'),
        blockAt s.mem (V .s2 + BitVec.ofNat 64 240), bytesAt s.mem Ad (V .s10).toNat,
        by rw [← a]; exact oa.hH, by rw [i, length_bytesAt], by rw [← b]; exact oa.abs⟩
  -- `oneCrypt`
  refine CT.seq (J := fun s => OneT c W sp R Np n Ad A D Ln T s ∧ OneAbs c W A s)
    ((oneCrypt_ct L hR).mono fun s ⟨hT, _⟩ => hT.1) (fun s ⟨hT, H, x, hH, hl, hab⟩ => ?_) ?_
  · obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := hT.1
    have L' := L.v a b d
    have hd : DataW (V .s2) (V .s1) (V .s0) s D (V .s11).toNat := by rw [a, b, d, k]; exact hD
    refine WP.mono (WP.with_rdwr (oneCrypt_ok L' he e hR hd (by rw [d]; exact sd) rfl)) fun s' ⟨oc, rd, wr, sp'⟩ =>
      ⟨hT.frame (fun r hr => (he.fr r hr).symm) oc.env rd wr sp' oc.frame
        (fun hd' => by rw [← d]; exact slot_crFrame L' hd hd'), H, x, ?_, hl, ?_⟩
    · rw [← a, blockAt_frame oc.frame (fun r hr => (ctx_crFrame L' hd r hr).sub_left (Lay.ctxSub (by decide)))]
      rw [← a] at hH; exact hH
    · have hx := Nat.mod_lt (x ++ zeros (padLen x.length)).length (show 16 > 0 by decide)
      rw [← b] at hab ⊢
      exact hab.congr (blockAt_frame oc.frame (stp_crFrame L' hd (by decide)))
        (bytesAt_frame oc.frame (stp_crFrame L' hd (by omega)) (by omega))
  -- `oneTag 0`
  refine CT.seq (J := fun s => ∃ V : Reg → BitVec 64, V .s0 = W ∧ V .s9 = T ∧ Env V sp s ∧
    Covers [⟨T, 16⟩] s.wr) ((oneTag_ct L (.inl rfl) hR).mono fun s ⟨hT, _⟩ => hT.1)
    (fun s ⟨hT, H, x, hH, hl, hab⟩ => ?_) ?_
  · obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := hT.1
    refine WP.mono (WP.with_rdwr (oneTag_ok (L.v a b d) (o := 0) (.inl rfl) (H := H) (a := x) (D := D) he e hR
      (by rw [a]; exact hH) (by rw [i]; exact hl) (by rw [b]; exact hab) (by rw [b, d, k]; exact hD.ok)
      (by rw [d]; exact sd)))
      fun s' ⟨ot, _, wr, _⟩ => ⟨V, d, (he.fr _ (by decide)).symm.trans hT.2.1, ot.env, by rw [wr]; exact hT.2.2⟩
  -- the tag copied out
  refine CT.seq (J := fun s => s.gpr .s0 = W ∧ s.sp = sp) ?_
    (fun s ⟨V, d, i, he, hT⟩ => WP.mono (tagOut_ok he (by rw [i]; exact hT) (by rw [i, d]; exact hTW))
      fun s' ⟨_, _, hg, hk⟩ => ⟨by rw [hg _ (by decide), he.s0, d], by rw [hk.sp, he.sp]⟩) ?_
  · obtain ⟨_, hc⟩ := tagOut_taint
    refine CT.taint _ (fun s₁ s₂ ⟨_, d₁, i₁, h₁, _⟩ ⟨_, d₂, i₂, h₂, _⟩ =>
      ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), i₁, i₂]
    · rw [h₁.s0, h₂.s0, d₁, d₂]
  obtain ⟨_, hc⟩ := restore_taint
  exact CT.taintEq _ (fun _ => W) sp (fun s ⟨e31, esp⟩ => ⟨esp, by simp [e31]⟩) hc

end

theorem seal_ct : ConstantTime isa sealRISCV64.pre sealRISCV64.pub «seal» := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q3, q4, q5, q6, q7, q8, q9, q10, qsp, qa⟩ := hq
  have h₁' : sealPre σ₁ := h₁
  obtain ⟨_, _, _, dcW, _, _, _, _, _, _, _, dtW, _, fc, _, _, _, fW, _, hR, _, ca, wa⟩ := h₁'
  let I₀ : State → Prop := fun s => sealPre s ∧ s.gpr .a0 = σ₁.gpr .a0 ∧ s.gpr .a1 = σ₁.gpr .a1 ∧
    s.gpr .a2 = σ₁.gpr .a2 ∧ s.gpr .a3 = σ₁.gpr .a3 ∧ s.gpr .a4 = σ₁.gpr .a4 ∧ s.gpr .a5 = σ₁.gpr .a5 ∧
    s.gpr .a6 = σ₁.gpr .a6 ∧ s.gpr .a7 = σ₁.gpr .a7 ∧ s.sp = σ₁.sp ∧ stackArg s 0 = stackArg σ₁ 0 ∧
    stackArg s 1 = stackArg σ₁ 1
  refine ⟨I₀, ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨h₂, q3.symm, q4.symm, q5.symm,
    q6.symm, q7.symm, q8.symm, q9.symm, q10.symm, qsp.symm, (qa 0 (by decide)).symm, (qa 1 (by decide)).symm⟩, ?_⟩
  refine CT.seq (J := fun s => OneT (σ₁.gpr .a0) (stackArg σ₁ 1) σ₁.sp (σ₁.gpr .a1).toNat (σ₁.gpr .a2)
    (σ₁.gpr .a3).toNat (σ₁.gpr .a4) (σ₁.gpr .a5) (σ₁.gpr .a6) (σ₁.gpr .a7) (stackArg σ₁ 0) s ∧
    s.gpr .s4 = σ₁.gpr .a2 ∧ s.gpr .s5 = BitVec.ofNat 64 (σ₁.gpr .a3).toNat) ?_
    (fun s ⟨hs, e3, e4, e5, e6, e7, e8, e9, e10, esp, ea0, ea1⟩ => ?_)
    (sealBody_ct (oneLay fc fW dcW ca wa) hR (dtW.sub_right (Region.sub_prefix (by decide))))
  · -- the entry: its head loads `W` from a public address, the rest saves through it
    let v : Reg → BitVec 64 := fun r => if r = .t1 then stackArg σ₁ 1 else σ₁.gpr r
    rw [oneEntry_eq]
    refine RelCT.block_append (CT.seq (J := fun s => s.sp = σ₁.sp ∧
      ∀ r ∈ [Reg.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t1], s.gpr r = v r) ?_ ?_ ?_)
    · obtain ⟨_, hc⟩ := oneHead_taint
      exact CT.taintEq _ σ₁.gpr σ₁.sp (fun s ⟨_, _, _, _, _, _, _, _, _, esp, _⟩ => ⟨esp, by simp⟩) hc
    · intro s ⟨hs, e3, e4, e5, e6, e7, e8, e9, e10, esp, _, ea1⟩
      have hA : Covers [args s 2] (s.rd ++ s.wr) := covers_mem (List.mem_append_left _ (by rw [hs.1]; simp))
      have hsa : s.sp.toNat % 16 = 0 := by
        obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hk, -⟩ := hs
        exact hk.1
      refine WP.mono (oneA_ok (W := stackArg s 1) (.inl rfl) hsa (args_in hA (by decide) (i := 1) (by decide)) rfl)
        fun sA ⟨a12, gA, kA⟩ => ⟨kA.sp.trans esp, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [v, a12, ea1, e3, e4, e5, e6, e7, e8, e9, e10, gA]
    · obtain ⟨_, hc⟩ := oneRest_taint
      exact CT.taintEq _ v σ₁.sp (fun s h => h) hc
  · have := sealEntry_wp hs
    rw [ea0, ea1, e3, e4, e5, e6, e7, e8, e9, e10, esp] at this
    exact WP.mono this fun s' ⟨hO, h24, h25, h20, hT⟩ => ⟨⟨hO, h20, hT⟩, h24, h25⟩

end VG.Proof.AesGcm.RISCV64
