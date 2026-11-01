module

public import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
public import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.CTOne
public import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.Contract
import VerifiedGarbage.Proof.AesGcm.RISCV64.InitCT
import VerifiedGarbage.Proof.AesGcm.RISCV64.J0
import VerifiedGarbage.Proof.AesGcm.RISCV64.OneShot
import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.OneShot
import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.OneEntry
import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.Seal
import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.StreamCrypt
public import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
meta import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.CTOne
meta import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.Contract
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.InitCT
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.J0
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.OneShot
meta import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.OneShot
meta import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.OneEntry
meta import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.Seal
meta import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.StreamCrypt
meta import VerifiedGarbage.Proof.Gcm.Stream
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.CTFin
meta import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.CTFin
public import VerifiedGarbage.Impl.Sm4Gcm.RISCV64

/-!
# SM4-GCM on RISC-V: `vg_sm4_gcm_seal` is constant time

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/RISCV64/CTSeal.lean`): the entry loads `W` from the stack
argument at `sp`, a public address, and then saves our caller's registers
through it: its head is checked on its own, and the rest from the arguments
and `W` (`oneHead_ct`). The pieces follow (`CTOne.lean`), with the tag's
address `T` in `s9`, which the environment pins, and, between them, the
additional data absorbed, for `oneTag 0`.
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.RISCV64

open VG VG.RISCV64 VG.Impl.Sm4Gcm.RISCV64
open VG.Impl.AesGcm.RISCV64 (mov oneAad tagOut restore save aadO dataO)
open VG.Proof.AesGcm.RISCV64 hiding CrIn CrMid CrOut crFrame ciphOf TailKs ctx_crFrame ciph_frame
  CtrCall CtrPost ctr_call ctr_rel tagFrame TagOut TagMid tagLens_ok
  tagArgs_ok ctrTag_mk tagCall_ok tag_ok slot_crFrame OC oneCrypt_ok otFrame abs_otSub t_otSub tag_otSub OT
  oneTag_ok stp_crFrame saved_crFrame ciph_keep SO1 one1_wp one_env saved_otFrame sealPre sealRISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt zeros padLen)
open VG.Proof.Gcm (Absorbed)

/-- The entry of `seal`, from its precondition. -/
theorem sealEntry_wp {s₀ : State} (h : sealPre s₀) :
    WP isa (.block (oneEntry 0)) s₀ fun s₁ =>
      OneI (s₀.gpr .a0) (stackArg s₀ 0) s₀.sp (s₀.gpr .a1) (s₀.gpr .a2).toNat (s₀.gpr .a3)
        (s₀.gpr .a4) (s₀.gpr .a5) (s₀.gpr .a6) s₁ ∧
      s₁.gpr .s4 = s₀.gpr .a1 ∧ s₁.gpr .s5 = BitVec.ofNat 64 (s₀.gpr .a2).toNat ∧
      s₁.gpr .s9 = s₀.gpr .a7 ∧ Covers [⟨s₀.gpr .a7, 16⟩] s₁.wr := by
  obtain ⟨hrd, hwr, dcd, dcW, dnd, dnW, dad, daW, ddt, ddW, ddA, dtW, dWA, fc, fn, fa, fd, ft, fW, fsp, hstk,
    ca, wa⟩ := h
  have hk₀ : StkOk (s₀.gpr .a0) (stackArg s₀ 0 + BitVec.ofNat 64 16) (stackArg s₀ 0) s₀.sp :=
    one_stk3 hstk (by simp) (by simp)
  have bc₀ : (below s₀.sp 3232).Disjoint ⟨s₀.gpr .a0, 256⟩ := hstk.buf3 (by simp)
  have bw₀ : (below s₀.sp 3232).Disjoint ⟨stackArg s₀ 0, 2560⟩ := hstk.buf3 (by simp)
  have bd₀ : (below s₀.sp 3232).Disjoint ⟨s₀.gpr .a5, (s₀.gpr .a6).toNat⟩ := hstk.buf3 (by simp)
  have hC : Covers [⟨s₀.gpr .a0, 256⟩] (s₀.rd ++ s₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  have hW : Covers [⟨stackArg s₀ 0, 2560⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  have hA : Covers [args s₀ 1] (s₀.rd ++ s₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  refine WP.mono (one1_wp (off := 0) (W := stackArg s₀ 0) (.inl rfl) hW wa hstk.1
    (args_in hA (by decide) (i := 0) (by decide)) rfl) fun s₁ h1 => ?_
  have hk₁ := h1.keeps
  have toN : ∀ {x : BitVec 64}, x = BitVec.ofNat 64 x.toNat := fun {x} => by simp
  have hDw : Covers [⟨s₀.gpr .a5, (s₀.gpr .a6).toNat⟩] s₁.wr := by
    rw [hk₁.wr, hwr]; exact covers_mem (by simp)
  refine ⟨⟨s₁.gpr, h1.s2, h1.s1, h1.s0, ⟨⟨hstk.2.1, by rw [h1.s2]; exact bc₀,
      by rw [h1.s1]; exact bw₀.sub_right (Lay.wSub (by decide)), by rw [h1.s0]; exact bw₀⟩, bd₀⟩,
    by rw [h1.s7]; exact toN, h1.s10, h1.s11, one_env h1 hC hW hk₀, ?_, ?_, ⟨⟨covers_left hDw, (s₀.gpr .a6).isLt, fd,
      ddW.sub_right (Lay.wSub (by decide)), ddW, by rw [hk₁.sp]; exact hstk.buf (by simp)⟩, hDw, dcd⟩,
    h1.aad, h1.dat⟩, h1.s4, by rw [h1.s5]; exact toN, h1.s9, ?_⟩
  · exact ⟨by rw [hk₁.rd, hk₁.wr]; exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp)),
      (s₀.gpr .a2).isLt, fn, dnW.sub_right (Lay.wSub (by decide)), dnW, by rw [hk₁.sp]; exact hstk.buf (by simp)⟩
  · exact ⟨by rw [hk₁.rd, hk₁.wr]; exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp)),
      (s₀.gpr .a4).isLt, fa, daW.sub_right (Lay.wSub (by decide)), daW, by rw [hk₁.sp]; exact hstk.buf (by simp)⟩
  · rw [hk₁.wr, hwr]; exact covers_mem (by simp)

/-- The head of the entry: `W`, the stack argument at `sp + off`, into `t1`. -/
theorem oneA_ok {s₀ : State} {off : Nat} {W : Addr} (hoff : off = 0 ∨ off = 8) (hsa : s₀.sp.toNat % 16 = 0)
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
  save .t1 ++ ([mov .s2 .a0, .addi .s1 .s0 16, mov .s4 .a1, mov .s5 .a2, mov .s7 .a2,
    .store .d .a3 .s0 aadO, mov .s10 .a4, .store .d .a5 .s0 dataO, mov .s11 .a6, mov .s9 .a7] : List Instr)

theorem oneEntry_eq (off : Nat) : oneEntry off = ([.addSp .t1 0, .load .d .t1 .t1 off] : List Instr) ++ oneRest := by
  rw [oneEntry, List.append_assoc]

theorem oneHead_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [])
    (.block [.addSp .t1 0, .load .d .t1 .t1 0]) h).isSome = true := ⟨_, by taint_decide⟩

theorem oneRest_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint
    (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t1]) (.block oneRest) h).isSome = true :=
  ⟨_, by taint_decide⟩

section
variable {c W sp : Addr} {Np : Addr} {n : Nat} {Ad A D Ln T : BitVec 64}

/-- `OneI`, with the tag's address `T` in `s9`, which the state may write. -/
def OneT (c W sp : Addr) (Np : Addr) (n : Nat) (Ad A D Ln T : BitVec 64) (s : State) : Prop :=
  OneI c W sp Np n Ad A D Ln s ∧ s.gpr .s9 = T ∧ Covers [⟨T, 16⟩] s.wr

theorem OneT.frame {s s' : State} (h : OneT c W sp Np n Ad A D Ln T s) {V : Reg → BitVec 64}
    (hV : ∀ r ∈ frozen, V r = s.gpr r) (he : Env V sp s') (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hs : ∀ {d : Nat}, 232 ≤ d ∧ d + 8 ≤ 248 → ∀ r ∈ rs, (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r) :
    OneT c W sp Np n Ad A D Ln T s' :=
  ⟨h.1.frame hV he hrd hwr hsp hf hs, (he.fr _ (by decide)).trans ((hV _ (by decide)).trans h.2.1),
    by rw [hwr]; exact h.2.2⟩

/-- Between `oneAad` and `oneTag`: the additional data `a` absorbed and padded. -/
def OneAbs (c W : Addr) (A : BitVec 64) (s : State) : Prop :=
  ∃ H : Block, ∃ a : List Byte, blockAt s.mem (c + BitVec.ofNat 64 240) = H ∧ A.toNat = a.length ∧
    Absorbed s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H
      (a ++ zeros (padLen a.length))

variable (L : Lay c (W + BitVec.ofNat 64 16) W) (hTW : (⟨T, 16⟩ : Region).Disjoint ⟨W, 16⟩)
include L hTW

/-- `seal` after its entry. -/
theorem sealBody_ct : CT (fun s => OneT c W sp Np n Ad A D Ln T s ∧ s.gpr .s4 = Np ∧
    s.gpr .s5 = BitVec.ofNat 64 n)
    (.seq oneAad (.seq oneCrypt (.seq (oneTag 0) (.seq (.block tagOut) (.block restore))))) := by
  -- `oneAad`
  refine CT.seq (J := fun s => OneT c W sp Np n Ad A D Ln T s ∧ OneAbs c W A s)
    ((oneAad_ct L).mono fun s ⟨⟨hO, _⟩, h24, h25⟩ => ⟨hO, h24, h25⟩)
    (fun s ⟨hT, h24, h25⟩ => ?_) ?_
  · obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := hT.1
    refine WP.mono (Proof.AesGcm.RISCV64.WP.with_rdwr (oneAad_ok (L.v a b d) (A := Ad) he rfl h24 h25 f (by rw [b, d]; exact hN)
      (by rw [b, d, i]; exact hA) (by rw [d]; exact sa))) fun s' ⟨oa, rd, wr, sp'⟩ =>
        ⟨hT.frame (fun r hr => (he.fr r hr).symm) oa.env rd wr sp' oa.frame
          (fun hd' => by rw [← d]; exact slot_j0 (L.v a b d) he.stk' hd'),
        blockAt s.mem (V .s2 + BitVec.ofNat 64 240), bytesAt s.mem Ad (V .s10).toNat,
        by rw [← a]; exact oa.hH, by rw [i, length_bytesAt], by rw [← b]; exact oa.abs⟩
  -- `oneCrypt`
  refine CT.seq (J := fun s => OneT c W sp Np n Ad A D Ln T s ∧ OneAbs c W A s)
    ((oneCrypt_ct L).mono fun s ⟨hT, _⟩ => hT.1) (fun s ⟨hT, H, x, hH, hl, hab⟩ => ?_) ?_
  · obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := hT.1
    have L' := L.v a b d
    have hd : DataW (V .s2) (V .s1) (V .s0) s D (V .s11).toNat := by rw [a, b, d, k]; exact hD
    refine WP.mono (Proof.AesGcm.RISCV64.WP.with_rdwr (oneCrypt_ok L' e.1 he hd (by rw [k]; exact e.2) (by rw [d]; exact sd) rfl)) fun s' ⟨oc, rd, wr, sp'⟩ =>
      ⟨hT.frame (fun r hr => (he.fr r hr).symm) oc.env rd wr sp' oc.frame
        (fun hd' => by rw [← d]; exact slot_crFrame L' e.1 hd hd'), H, x, ?_, hl, ?_⟩
    · rw [← a, blockAt_frame oc.frame (fun r hr => (ctx_crFrame L' e.1 hd r hr).sub_left (Lay.ctxSub (by decide)))]
      rw [← a] at hH; exact hH
    · have hx := Nat.mod_lt (x ++ zeros (padLen x.length)).length (show 16 > 0 by decide)
      rw [← b] at hab ⊢
      exact hab.congr (blockAt_frame oc.frame (stp_crFrame e.1.st hd (by decide)))
        (bytesAt_frame oc.frame (stp_crFrame e.1.st hd (by omega)) (by omega))
  -- `oneTag 0`
  refine CT.seq (J := fun s => ∃ V : Reg → BitVec 64, V .s0 = W ∧ V .s9 = T ∧ Env V sp s ∧
    Covers [⟨T, 16⟩] s.wr) ((oneTag_ct L (.inl rfl)).mono fun s ⟨hT, _⟩ => hT.1)
    (fun s ⟨hT, H, x, hH, hl, hab⟩ => ?_) ?_
  · obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := hT.1
    refine WP.mono (Proof.AesGcm.RISCV64.WP.with_rdwr (oneTag_ok (L.v a b d) e.1 (o := 0) (.inl rfl) (H := H) (a := x) (D := D) he
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
  obtain ⟨_, _, _, dcW, _, _, _, _, _, _, _, dtW, _, fc, _, _, _, _, fW, _, _, ca, wa⟩ := h₁'
  let I₀ : State → Prop := fun s => sealPre s ∧ s.gpr .a0 = σ₁.gpr .a0 ∧ s.gpr .a1 = σ₁.gpr .a1 ∧
    s.gpr .a2 = σ₁.gpr .a2 ∧ s.gpr .a3 = σ₁.gpr .a3 ∧ s.gpr .a4 = σ₁.gpr .a4 ∧ s.gpr .a5 = σ₁.gpr .a5 ∧
    s.gpr .a6 = σ₁.gpr .a6 ∧ s.gpr .a7 = σ₁.gpr .a7 ∧ s.sp = σ₁.sp ∧ stackArg s 0 = stackArg σ₁ 0
  refine ⟨I₀, ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨h₂, q3.symm, q4.symm, q5.symm,
    q6.symm, q7.symm, q8.symm, q9.symm, q10.symm, qsp.symm, (qa 0 (by decide)).symm⟩, ?_⟩
  refine CT.seq (J := fun s => OneT (σ₁.gpr .a0) (stackArg σ₁ 0) σ₁.sp (σ₁.gpr .a1)
    (σ₁.gpr .a2).toNat (σ₁.gpr .a3) (σ₁.gpr .a4) (σ₁.gpr .a5) (σ₁.gpr .a6) (σ₁.gpr .a7) s ∧
    s.gpr .s4 = σ₁.gpr .a1 ∧ s.gpr .s5 = BitVec.ofNat 64 (σ₁.gpr .a2).toNat) ?_
    (fun s ⟨hs, e3, e4, e5, e6, e7, e8, e9, e10, esp, ea0⟩ => ?_)
    (sealBody_ct (oneLay fc fW dcW ca wa) (dtW.sub_right (Region.sub_prefix (by decide))))
  · -- the entry: its head loads `W` from a public address, the rest saves through it
    let v : Reg → BitVec 64 := fun r => if r = .t1 then stackArg σ₁ 0 else σ₁.gpr r
    rw [oneEntry_eq]
    refine RelCT.block_append (CT.seq (J := fun s => s.sp = σ₁.sp ∧
      ∀ r ∈ [Reg.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t1], s.gpr r = v r) ?_ ?_ ?_)
    · obtain ⟨_, hc⟩ := oneHead_taint
      exact CT.taintEq _ σ₁.gpr σ₁.sp (fun s ⟨_, _, _, _, _, _, _, _, _, esp, _⟩ => ⟨esp, by simp⟩) hc
    · intro s ⟨hs, e3, e4, e5, e6, e7, e8, e9, e10, esp, ea1⟩
      have hA : Covers [args s 1] (s.rd ++ s.wr) := covers_mem (List.mem_append_left _ (by rw [hs.1]; simp))
      have hsa : s.sp.toNat % 16 = 0 := by
        obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hk, -⟩ := hs
        exact hk.1
      refine WP.mono (oneA_ok (W := stackArg s 0) (.inl rfl) hsa (args_in hA (by decide) (i := 0) (by decide)) rfl)
        fun sA ⟨a12, gA, kA⟩ => ⟨kA.sp.trans esp, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [v, a12, ea1, e3, e4, e5, e6, e7, e8, e9, e10, gA]
    · obtain ⟨_, hc⟩ := oneRest_taint
      exact CT.taintEq _ v σ₁.sp (fun s h => h) hc
  · have := sealEntry_wp hs
    rw [ea0, e3, e4, e5, e6, e7, e8, e9, e10, esp] at this
    exact WP.mono this fun s' ⟨hO, h24, h25, h20, hT⟩ => ⟨⟨hO, h20, hT⟩, h24, h25⟩

end VG.Proof.Sm4Gcm.RISCV64
