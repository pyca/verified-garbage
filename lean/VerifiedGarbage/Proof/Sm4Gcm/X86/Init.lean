module

public import VerifiedGarbage.Proof.AesGcm.X86.Top
public import VerifiedGarbage.Proof.Sm4Gcm.X86.Contract
public import VerifiedGarbage.Proof.Sm4Gcm.X86.CtrCall
meta import VerifiedGarbage.Proof.AesGcm.X86.Top
import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Impl.Sm4Gcm.X86
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Framework.X86.Call
meta import VerifiedGarbage.TCB.X86.Isa
meta import VerifiedGarbage.TCB.X86.State
meta import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.AesGcm.X86.Loops
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.AesGcm.X86.Absorb
meta import VerifiedGarbage.Proof.AesGcm.X86.Loops
meta import VerifiedGarbage.Proof.Cmac.Block32
meta import VerifiedGarbage.Proof.Cmac.Mem32
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.AesGcm.X86.Flush
meta import VerifiedGarbage.Proof.AesGcm.X86.Flush
meta import VerifiedGarbage.Proof.Gcm.Ctr
import VerifiedGarbage.Proof.Sm4Gcm.X86.Crypt
meta import VerifiedGarbage.Proof.Sm4Gcm.X86.Crypt

import VerifiedGarbage.Proof.Sm4.CtrCipher

/-!
# SM4-GCM on x86: `vg_sm4_gcm_init`

Untrusted: everything here is checked by Lean. The key schedule
(`vg_sm4_expand_key`), then the hash subkey `CIPH_K(0¹²⁸)` (`vg_sm4_ctr32`
on a zero block, with a zero counter block at `T`), as one `Pc`
(`init_pc`): correct (`init_correct`) and constant time (`init_ct`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.X86


open VG VG.X86 VG.X86.RegUpd VG.Impl.Sm4Gcm.X86 VG.WriteBytes VG.Proof.AesGcm.X86
open VG.Impl.AesGcm.X86 hiding ctrCall keyCall ctrArgs cryptWhole cryptTail crypt tag init cryptEntry
  streamEncrypt streamDecrypt finEntry finTag streamFinish streamVerify oneEntry oneTag oneCrypt «seal» «open»
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt)
open VG.Spec.Sm4.Gcm (KeyRepr)

/-- The facts of `init`'s precondition about the public data `p` alone. -/
structure InitPure (p : BitVec 32 × (Nat → BitVec 32)) : Prop where
  kc : (⟨w64 (p.2 0), 16⟩ : Region).Disjoint ⟨w64 (p.2 1), 256⟩
  kw : (⟨w64 (p.2 0), 16⟩ : Region).Disjoint ⟨w64 (p.2 2), 2560⟩
  cw : (⟨w64 (p.2 1), 256⟩ : Region).Disjoint ⟨w64 (p.2 2), 2560⟩
  r_c : (⟨w64 p.1, 4⟩ : Region).Disjoint ⟨w64 (p.2 1), 256⟩
  r_w : (⟨w64 p.1, 4⟩ : Region).Disjoint ⟨w64 (p.2 2), 2560⟩
  k_k : (below p.1 1536).Disjoint ⟨w64 (p.2 0), 16⟩
  k_c : (below p.1 1536).Disjoint ⟨w64 (p.2 1), 256⟩
  k_w : (below p.1 1536).Disjoint ⟨w64 (p.2 2), 2560⟩
  fk : (p.2 0).toNat + 16 ≤ 2 ^ 32
  fc : (p.2 1).toNat + 256 ≤ 2 ^ 32
  fw : (p.2 2).toNat + 2560 ≤ 2 ^ 32
  sp : 1536 ≤ p.1.toNat

theorem initPure_of {p : BitVec 32 × (Nat → BitVec 32)} {s : State} (h : initPre s) (hp : pubOf 3 s = p) :
    InitPure p := by
  simp only [initPre] at h
  sig_split h
  rename_i hdrop0 hdrop1 d_kc d_kw hdrop4 d_cw hdrop6 hdrop7 hdrop8 r_c r_w hdrop11 k_k k_c k_w hdrop15 fk fc
    fw sp
  clear hdrop0 hdrop1 hdrop4 hdrop6 hdrop7 hdrop8 hdrop11 hdrop15 h
  rw [ofNat_lit, below_eq sp] at k_k k_c k_w
  have a0 := pubOf_arg hp (i := 0) (by decide); have a1 := pubOf_arg hp (i := 1) (by decide)
  have a2 := pubOf_arg hp (i := 2) (by decide)
  have e := pubOf_esp hp
  simp only [a0, a1, a2, e] at d_kc d_kw d_cw r_c r_w k_k k_c k_w fk fc fw sp
  exact ⟨d_kc, d_kw, d_cw, r_c, r_w, k_k, k_c, k_w, fk, fc, fw, sp⟩

/-- `ctx` and `W` and the stack apart, at offsets. -/
theorem InitPure.cw' {p : BitVec 32 × (Nat → BitVec 32)} (h : InitPure p) {a n d k : Nat} (ha : a + n ≤ 256)
    (hd : d + k ≤ 2560) :
    (⟨w64 (p.2 1) + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨w64 (p.2 2) + BitVec.ofNat 64 d, k⟩ :=
  (h.cw.sub_left (Lay.ctxSub ha)).sub_right (Lay.wSub hd)

abbrev initTail : List Instr := [.mov .eax (argOp 0), .mov .edx (.reg .esi)]

abbrev initMid : List Instr :=
  ([.mov .eax (imm 0), .store (at_ .esi 240) .eax, .store (at_ .esi 244) .eax,
      .store (at_ .esi 248) .eax, .store (at_ .esi 252) .eax] : List Instr) ++ zero4 tO ++
      ([.mov .eax (.reg .esi), .mov .edx (.reg .ebp), .alu .add .edx (imm tO),
        .mov .ebx (.reg .esi), .alu .add .ebx (imm 240), .mov .edi (imm 1)] : List Instr)

theorem init_eq : init = .seq (entry 2 (([.mov .esi (argOp 1)] : List Instr) ++
    (([] : List (Nat × Nat)).flatMap (fun p => keep p.1 p.2) ++ initTail)))
    (.seq keyCall (.seq (.block initMid) (.seq ctrCall (.block restore)))) := rfl

/-- After the entry: the arguments of `vg_sm4_expand_key`. -/
structure IEnt (p : BitVec 32 × (Nat → BitVec 32)) (s₀ s : State) : Prop where
  pre : initPre s₀
  pub : pubOf 3 s₀ = p
  call : KeyCall s (p.2 0) (p.2 1)
  esi : s.gpr .esi = p.2 1
  ebp : s.gpr .ebp = p.2 2
  esp : s.gpr .esp = p.1
  saved : SavedAt s.mem (p.2 2) s₀
  frame : Frame [⟨w64 (p.2 2) + BitVec.ofNat 64 128, 2432⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem iEntry_pc (p : BitVec 32 × (Nat → BitVec 32)) :
    Pc (fun (s₀ : State) s => initPre s₀ ∧ pubOf 3 s₀ = p ∧ s = s₀)
      (entry 2 (([.mov .esi (argOp 1)] : List Instr) ++ (([] : List (Nat × Nat)).flatMap (fun p => keep p.1 p.2) ++ initTail)))
      (IEnt p) := by
  refine ⟨fun s₀ s ⟨hpre, hpub, hs⟩ => ?_, ?_⟩
  · subst s
    have hc := initPure_of hpre hpub
    have hp := hpre
    simp only [initPre] at hp
    sig_split hp
    rename_i hrd hwr hdrop2 hdrop3 hdrop4 hdrop5 hdrop6 d_wa hdrop8 hdrop9 hdrop10 hdrop11 hdrop12 hdrop13
      hdrop14 hdrop15 hdrop16 hdrop17 hdrop18 hdrop19
    clear hdrop2 hdrop3 hdrop4 hdrop5 hdrop6 hdrop8 hdrop9 hdrop10 hdrop11 hdrop12 hdrop13 hdrop14 hdrop15
      hdrop16 hdrop17 hdrop18 hdrop19
    have fa := hp
    clear hp
    have a : ∀ i, i < 3 → arg s₀ i = p.2 i := fun i hi => pubOf_arg hpub hi
    have esp := pubOf_esp hpub
    have wW : Covers [⟨w64 (arg s₀ 2), 2560⟩] s₀.wr := by rw [hwr]; exact covers_of_mem (by simp)
    have rA : Covers [argsR (s₀.gpr .esp) 3] (s₀.rd ++ s₀.wr) := by
      rw [argsR_eq, hrd, hwr]; exact covers_of_mem (by simp)
    have aw : (argsR (s₀.gpr .esp) 3).Disjoint ⟨w64 (arg s₀ 2), 2560⟩ := by rw [argsR_eq]; exact d_wa.symm
    refine entry_ok [] initTail (by decide) (by decide) (by decide) (by decide) rfl rfl wW rA aw (by omega_arith)
      (by rw [a 2 (by decide)]; exact hc.fw) fun s₂ e => ?_
    have i₀ : InRegions (s₂.rd ++ s₂.wr) (argA (s₀.gpr .esp) 0) 4 := by
      rw [e.rd, e.wr]; exact argIn_of rA (by omega_arith) (by decide)
    have v₀ := e.args 0 (by decide)
    refine ⟨_, by xrun [e.esp, i₀, v₀, e.esi], ?_⟩
    have bsub : Region.Sub (below p.1 1460) (below p.1 1536) := VG.X86.below_sub (by decide) hc.sp
    have hrd' : s₀.rd = [⟨w64 (p.2 0), 16⟩] := by rw [hrd, a 0 (by decide)]
    have hwr' : s₀.wr = [⟨w64 (p.2 1), 256⟩, ⟨w64 (p.2 2), 2560⟩, ⟨argAddr s₀ 0, 12⟩] := by
      rw [hwr, a 1 (by decide), a 2 (by decide)]
    refine ⟨hpre, hpub, ⟨by regs [v₀]; exact a 0 (by decide), by regs [e.esi]; exact a 1 (by decide),
      by regs [e.esp, esp]; have := hc.sp; omega_arith, hc.kc.sub_right (Region.sub_prefix (by decide)),
      by regs [e.esp, esp]; exact hc.k_k.sub_left bsub,
      by regs [e.esp, esp]; exact (hc.k_c.sub_left bsub).sub_right (Region.sub_prefix (by decide)),
      hc.fk, by have := hc.fc; omega_arith,
      by mems [e.rd, e.wr, hrd']; exact covers_of_mem (by simp), ?_⟩, by regs [e.esi]; exact a 1 (by decide),
      by regs [e.ebp]; rw [a 2 (by decide)], by regs [e.esp, esp], by mems []; rw [← a 2 (by decide)]; exact e.saved,
      by mems []; rw [← a 2 (by decide)]; exact e.frame, by mems [e.rd], by mems [e.wr]⟩
    mems [e.wr, hwr']
    have := covers_off (p := w64 (p.2 1)) (k := 256) (d := 0) (n := 128)
      (rs := [⟨w64 (p.2 1), 256⟩, ⟨w64 (p.2 2), 2560⟩, ⟨argAddr s₀ 0, 12⟩]) (covers_of_mem (by simp)) (by decide)
      (by decide)
    simpa using this
  · refine CT.seq (J := fun s => s.gpr .eax = p.2 2 ∧ s.gpr .esp = p.1)
      (CT.taint [.esp] (fun s₁ s₂ ⟨a₁, _, h₁, e₁⟩ ⟨a₂, _, h₂, e₂⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; subst e₁; subst e₂
        rw [pubOf_esp h₁, pubOf_esp h₂]) (by taint_decide)) (fun s ⟨s₀, hpre, hpub, hs⟩ => ?_)
      (CT.taint [.eax, .esp] (fun s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2, h₂.2]) (by taint_decide))
    subst s
    have hp := hpre
    simp only [initPre] at hp
    sig_split hp
    rename_i hrd hwr hdrop2 hdrop3 hdrop4 hdrop5 hdrop6 hdrop7 hdrop8 hdrop9 hdrop10 hdrop11 hdrop12 hdrop13
      hdrop14 hdrop15 hdrop16 hdrop17 hdrop18 hdrop19
    clear hdrop2 hdrop3 hdrop4 hdrop5 hdrop6 hdrop7 hdrop8 hdrop9 hdrop10 hdrop11 hdrop12 hdrop13 hdrop14
      hdrop15 hdrop16 hdrop17 hdrop18 hdrop19
    have fa := hp
    clear hp
    have rA : Covers [argsR (s₀.gpr .esp) 3] (s₀.rd ++ s₀.wr) := by
      rw [argsR_eq, hrd, hwr]; exact covers_of_mem (by simp)
    exact WP.mono (arg0_ok (argIn_of rA (by omega_arith) (by decide))) fun s' ⟨ax, sp⟩ =>
      ⟨by rw [ax]; exact pubOf_arg hpub (by decide), by rw [sp]; exact pubOf_esp hpub⟩

/-- After the key schedule and `initMid`: the arguments of `vg_sm4_ctr32` for `H`. -/
structure IMid (p : BitVec 32 × (Nat → BitVec 32)) (s₀ s : State) : Prop where
  ent : ∃ s₁, IEnt p s₀ s₁ ∧ Frame [⟨w64 (p.2 1), 256⟩, ⟨w64 (p.2 2), 2560⟩, below p.1 1536] s₁.mem s.mem
  call : CtrCall s (p.2 1) (p.2 2 + BitVec.ofNat 32 96) (p.2 1 + BitVec.ofNat 32 240) 1
  esp : s.gpr .esp = p.1
  ebp : s.gpr .ebp = p.2 2
  sched : Spec.Sm4.scheduleAt s.mem (w64 (p.2 1)) = Spec.Sm4.expandKey (Spec.Sm4.blockAt s₀.mem (w64 (p.2 0)))
  zt : blockAt s.mem (w64 (p.2 2) + BitVec.ofNat 64 96) = 0
  zh : blockAt s.mem (w64 (p.2 1) + BitVec.ofNat 64 240) = 0
  saved : SavedAt s.mem (p.2 2) s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem iMid_ok {p : BitVec 32 × (Nat → BitVec 32)} (hc : InitPure p) {s₀ s₁ s : State} (h : IEnt p s₀ s₁)
    (g : KeyPost s₁ (p.2 0) (p.2 1) s) :
    WP isa (.block initMid) s (IMid p s₀) := by
  have eT := w64_add (x := p.2 2) (k := 96) (by have := hc.fw; omega_arith)
  have eH := w64_add (x := p.2 1) (k := 240) (by have := hc.fc; omega_arith)
  have bp : s.gpr .ebp = p.2 2 := by rw [g.saved .ebp (by decide), h.ebp]
  have si : s.gpr .esi = p.2 1 := by rw [g.saved .esi (by decide), h.esi]
  have sp : s.gpr .esp = p.1 := by rw [g.saved .esp (by decide), h.esp]
  have hwr : s.wr = s₀.wr := by rw [g.wr, h.wr]
  have hp := h.pre
  simp only [initPre] at hp
  have hwr₀ : s₀.wr = [⟨w64 (p.2 1), 256⟩, ⟨w64 (p.2 2), 2560⟩, ⟨argAddr s₀ 0, 12⟩] := by
    rw [hp.2.1, pubOf_arg h.pub (i := 1) (by decide), pubOf_arg h.pub (i := 2) (by decide)]
  have wC : Covers [⟨w64 (p.2 1), 256⟩] s.wr := by rw [hwr, hwr₀]; exact covers_of_mem (by simp)
  have wW : Covers [⟨w64 (p.2 2), 2560⟩] s.wr := by rw [hwr, hwr₀]; exact covers_of_mem (by simp)
  have aC : ∀ {o}, o < 256 → w64 (p.2 1 + BitVec.ofNat 32 o) = w64 (p.2 1) + BitVec.ofNat 64 o :=
    fun ho => w64_add (by have := hc.fc; omega_arith)
  have aW : ∀ {o}, o < 2560 → w64 (p.2 2 + BitVec.ofNat 32 o) = w64 (p.2 2) + BitVec.ofNat 64 o :=
    fun ho => w64_add (by have := hc.fw; omega_arith)
  have cIn : ∀ {d}, d + 4 ≤ 256 → InRegions s.wr (w64 (p.2 1) + BitVec.ofNat 64 d) 4 :=
    fun hd => in_off wC hd (by decide)
  have wIn : ∀ {d}, d + 4 ≤ 2560 → InRegions s.wr (w64 (p.2 2) + BitVec.ofNat 64 d) 4 :=
    fun hd => in_off wW hd (by decide)
  have hzC : ∀ m : Mem, Cmac.zero4 m (w64 (p.2 1) + BitVec.ofNat 64 240) =
      (((m.writeW (w64 (p.2 1) + BitVec.ofNat 64 240) (BitVec.ofNat 32 0)).writeW (w64 (p.2 1) + BitVec.ofNat 64 244)
      (BitVec.ofNat 32 0)).writeW (w64 (p.2 1) + BitVec.ofNat 64 248) (BitVec.ofNat 32 0)).writeW
      (w64 (p.2 1) + BitVec.ofNat 64 252) (BitVec.ofNat 32 0) := fun m => by
    simp only [Cmac.zero4, Cmac.store4, add_ofNat_assoc]; rfl
  have hzW : ∀ m : Mem, Cmac.zero4 m (w64 (p.2 2) + BitVec.ofNat 64 96) =
      (((m.writeW (w64 (p.2 2) + BitVec.ofNat 64 96) (BitVec.ofNat 32 0)).writeW (w64 (p.2 2) + BitVec.ofNat 64 100)
      (BitVec.ofNat 32 0)).writeW (w64 (p.2 2) + BitVec.ofNat 64 104) (BitVec.ofNat 32 0)).writeW
      (w64 (p.2 2) + BitVec.ofNat 64 108) (BitVec.ofNat 32 0) := fun m => by
    simp only [Cmac.zero4, Cmac.store4, add_ofNat_assoc]; rfl
  refine WP.of_runBlock ⟨_, by xrun [initMid, bp, si, aC, aW, cIn, wIn, zero4, ← hzC, ← hzW], ?_⟩
  generalize hZ₁ : Cmac.zero4 s.mem (w64 (p.2 1) + BitVec.ofNat 64 240) = Z₁
  generalize hZ₂ : Cmac.zero4 Z₁ (w64 (p.2 2) + BitVec.ofNat 64 96) = Z₂
  have f₁ : Frame [⟨w64 (p.2 1) + BitVec.ofNat 64 240, 16⟩] s.mem Z₁ := by
    rw [← hZ₁]; exact Cmac.frame_store4 _ _ _ _ _
  have f₂ : Frame [⟨w64 (p.2 2) + BitVec.ofNat 64 96, 16⟩] Z₁ Z₂ := by rw [← hZ₂]; exact Cmac.frame_store4 _ _ _ _ _
  have hfit := hc.fc
  have hfw := hc.fw
  have hsp := hc.sp
  have bsub : Region.Sub (below p.1 1460) (below p.1 1536) := VG.X86.below_sub (by decide) hsp
  have gf := g.frame
  rw [h.esp] at gf
  have go := g.out
  have dK : ∀ r ∈ [(⟨w64 (p.2 2) + BitVec.ofNat 64 128, 2432⟩ : Region)],
      (⟨w64 (p.2 0), 16⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hc.kw.sub_right (Lay.wSub (by decide))
  rw [sm4BlockAt_frame h.frame dK] at go
  have dZ : ∀ r ∈ [(⟨w64 (p.2 1) + BitVec.ofNat 64 240, 16⟩ : Region)],
      (⟨w64 (p.2 1), 128⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.base_disjoint _ (by decide) (by omega_arith)
  have dZ₂ : ∀ r ∈ [(⟨w64 (p.2 2) + BitVec.ofNat 64 96, 16⟩ : Region)],
      (⟨w64 (p.2 1), 128⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hc.cw.sub_left (Region.sub_prefix (by omega_arith))).sub_right (Lay.wSub (by decide))
  have hsv : SavedAt Z₂ (p.2 2) s₀ := by
    refine ((h.saved.frame gf fun r hr => ?_).frame f₁ fun r hr => ?_).frame f₂ fun r hr => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ((hc.cw.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide))).symm
      · exact ((hc.k_w.sub_left bsub).sub_right (Lay.wSub (by decide))).symm
    · simp only [List.mem_singleton] at hr; subst hr; exact (hc.cw' (by decide) (by decide)).symm
    · simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  have kc := hc.cw' (a := 0) (n := 128) (d := 96) (k := 16) (by decide) (by decide)
  have cd := hc.cw' (a := 240) (n := 16) (d := 96) (k := 16) (by decide) (by decide)
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at kc
  have rC : Covers [⟨w64 (p.2 1), 128⟩] (s.rd ++ s.wr) := by
    have := covers_off (p := w64 (p.2 1)) (k := 256) (d := 0) (n := 128) (rs := s.wr) wC (by decide) (by decide)
    exact covers_left (by simpa using this)
  refine ⟨⟨s₁, h, ?_⟩, ⟨by regs [si], by regs [bp], by regs [si], by regs [], by regs [sp]; omega_arith,
    by rw [eT]; exact kc, ?_, by rw [eT, eH]; exact cd.symm,
    by regs [sp]; exact hc.k_c.sub_right (Region.sub_prefix (by decide)),
    by regs [sp]; rw [eT]; exact hc.k_w.sub_right (Lay.wSub (by decide)),
    by regs [sp]; rw [eH]; exact hc.k_c.sub_right (Lay.ctxSub (by decide)),
    by omega_arith, by rw [toNat_add32 (by omega_arith)]; omega_arith, by rw [toNat_add32 (by omega_arith)]; omega_arith,
    by mems []; exact rC, ?_⟩, by regs [sp], by regs [bp], ?_, ?_, ?_, ?_, by mems [g.rd, h.rd],
    by mems [g.wr, h.wr]⟩
  · simp only [mem_setMem, mem_setReg, mem_arithFlags]
    refine (gf.sub fun r hr => ?_).trans ((f₁.sub fun r hr => ?_).trans (f₂.sub fun r hr => ?_))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
      · exact ⟨_, by simp, bsub⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., Lay.ctxSub (by decide)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Lay.wSub (by decide)⟩
  · rw [eH]
    have := Offset.disjoint (w64 (p.2 1)) (d := 0) (n := 128) (e := 240) (k := 16 * 1) (.inl (by omega_arith))
      (by omega_arith) (by omega_arith)
    simpa using this
  · mems []
    rw [eT, eH]
    exact covers_cons (covers_off wW (by decide) (by decide)) (covers_cons (covers_off wC (by decide) (by decide))
      covers_nil)
  · simp only [mem_setMem, mem_setReg, mem_arithFlags]
    rw [scheduleAt_frame f₂ dZ₂, scheduleAt_frame f₁ dZ]
    exact go
  · simp only [mem_setMem, mem_setReg, mem_arithFlags]
    rw [← hZ₂, blockAt, zero4_bytes', ofBytes_zeros]
  · simp only [mem_setMem, mem_setReg, mem_arithFlags]
    rw [blockAt_frame f₂ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact cd, ← hZ₁, blockAt, zero4_bytes', ofBytes_zeros]
  · simp only [mem_setMem, mem_setReg, mem_arithFlags]; exact hsv

theorem init_pc (p : BitVec 32 × (Nat → BitVec 32)) :
    Pc (fun (s₀ : State) s => initPre s₀ ∧ pubOf 3 s₀ = p ∧ s = s₀) (init)
      (fun s₀ s' => abiPreserved s₀ s' ∧ initX86.post s₀ s') := by
  by_cases hex : ∃ s₀, initPre s₀ ∧ pubOf 3 s₀ = p
  swap
  · exact Pc.vacuous fun a s ⟨h₁, h₂, _⟩ => hex ⟨a, h₁, h₂⟩
  obtain ⟨z, hz, hzp⟩ := hex
  have hc := initPure_of hz hzp
  rw [init_eq]
  refine Pc.seq (iEntry_pc p) ?_
  refine Pc.seq (Pc.of (I := fun s => KeyCall s (p.2 0) (p.2 1) ∧ s.gpr .esp = p.1) (fun s h => key_call h.1)
    (key_ct fun s h => h) _ fun _ _ h => ⟨h.call, h.esp⟩) ?_
  refine Pc.seq (Q := IMid p) (Pc.taint [.esi, .ebp] (fun s₀ s ⟨s₁, h, g⟩ => iMid_ok hc h g)
    (fun _ _ s₁ s₂ ⟨t₁, h₁, g₁⟩ ⟨t₂, h₂, g₂⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [g₁.saved .esi (by decide), g₂.saved .esi (by decide), h₁.esi, h₂.esi]
      · rw [g₁.saved .ebp (by decide), g₂.saved .ebp (by decide), h₁.ebp, h₂.ebp]) (by taint_decide)) ?_
  refine Pc.seq (Pc.of (I := fun s => CtrCall s (p.2 1) (p.2 2 + BitVec.ofNat 32 96)
    (p.2 1 + BitVec.ofNat 32 240) 1 ∧ s.gpr .esp = p.1) (fun s h => ctr_call h.1)
    (ctr_ct fun s h => h) _ fun _ _ h => ⟨h.call, h.esp⟩) ?_
  refine Pc.taint [.ebp] (fun s₀ s' ⟨s, hm, g⟩ => ?_) (fun _ _ s₁ s₂ ⟨_, h₁, g₁⟩ ⟨_, h₂, g₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [g₁.saved .ebp (by decide), g₂.saved .ebp (by decide), h₁.ebp, h₂.ebp]) (by taint_decide)
  obtain ⟨s₁, h₁, fE⟩ := hm.ent
  have eT := w64_add (x := p.2 2) (k := 96) (by have := hc.fw; omega_arith)
  have eH := w64_add (x := p.2 1) (k := 240) (by have := hc.fc; omega_arith)
  have bp : s'.gpr .ebp = p.2 2 := by rw [g.saved .ebp (by decide), hm.ebp]
  have gf := g.frame
  rw [hm.esp, eT, eH] at gf
  have hsp := hc.sp
  have dC : ∀ r ∈ [(⟨w64 (p.2 2) + BitVec.ofNat 64 96, 16⟩ : Region),
      ⟨w64 (p.2 1) + BitVec.ofNat 64 240, 16 * 1⟩, below p.1 1536],
      (⟨w64 (p.2 1), 128⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hc.cw.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide))
    · exact Offset.base_disjoint _ (by decide) (by omega_arith)
    · exact (hc.k_c.sub_right (Region.sub_prefix (by decide))).symm
  have hsv : SavedAt s'.mem (p.2 2) s₀ := hm.saved.frame gf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact (hc.cw' (by decide) (by decide)).symm
    · exact ((hc.k_w.sub_right (Lay.wSub (by decide)))).symm
  have rG : ∀ r ∈ [(⟨w64 (p.2 2) + BitVec.ofNat 64 96, 16⟩ : Region),
      ⟨w64 (p.2 1) + BitVec.ofNat 64 240, 16 * 1⟩, below p.1 1536],
      (⟨w64 p.1, 4⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hc.r_w.sub_right (Lay.wSub (by decide))
    · exact hc.r_c.sub_right (Lay.ctxSub (by decide))
    · exact ret_below hsp
  have rF : ∀ r ∈ [(⟨w64 (p.2 1), 256⟩ : Region), ⟨w64 (p.2 2), 2560⟩, below p.1 1536],
      (⟨w64 p.1, 4⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hc.r_c
    · exact hc.r_w
    · exact ret_below hsp
  have rE : ∀ r ∈ [(⟨w64 (p.2 2) + BitVec.ofNat 64 128, 2432⟩ : Region)], (⟨w64 p.1, 4⟩ : Region).Disjoint r :=
    fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hc.r_w.sub_right (Lay.wSub (by decide))
  have hret : s'.mem.readW (w64 (s₀.gpr .esp)) 32 = s₀.mem.readW (w64 (s₀.gpr .esp)) 32 := by
    rw [pubOf_esp h₁.pub, ret_kept gf rG, ret_kept fE rF, ret_kept h₁.frame rE]
  have hwr₀ : s'.wr = s₀.wr := by rw [g.wr, hm.wr]
  have hp := h₁.pre
  simp only [initPre] at hp
  have wW : Covers [⟨w64 (p.2 2), 2560⟩] s'.wr := by
    rw [hwr₀, hp.2.1, pubOf_arg h₁.pub (i := 2) (by decide)]; exact covers_of_mem (by simp)
  refine WP.mono (exit_ok (W := p.2 2) bp (by rw [g.saved .esp (by decide), hm.esp, pubOf_esp h₁.pub])
    (covers_left wW) hc.fw hsv hret)
    fun s'' ⟨abi, m'', _, _, _⟩ => ⟨abi, ?_⟩
  have hA : ∀ i, i < 3 → arg s₀ i = p.2 i := fun i hi => pubOf_arg h₁.pub hi
  show KeyRepr s''.mem _ _
  rw [hA 0 (by decide), hA 1 (by decide), m'']
  have hkey : (Vector.ofFn fun i : Fin 16 => (bytesAt s₀.mem (w64 (p.2 0)) 16).getD i.val 0) =
      Spec.Sm4.blockAt s₀.mem (w64 (p.2 0)) := by
    rw [Proof.Sm4.bytesAt_eq_blockAt]; exact Proof.Sm4.ofFn_toList _
  have hs : Spec.Sm4.scheduleAt s'.mem (w64 (p.2 1)) =
      Spec.Sm4.expandKey (Spec.Sm4.blockAt s₀.mem (w64 (p.2 0))) := by
    rw [scheduleAt_frame gf dC]; exact hm.sched
  refine ⟨by rw [hkey]; exact hs, ?_⟩
  have go := g.out
  rw [eH, eT, blocksAt_one, blocksAt_one, hm.zh, hm.zt, hm.sched] at go
  have hb := congrArg (fun l => List.getD l 0 0) go
  simp only [List.getD_cons_zero] at hb
  rw [Proof.Gcm.ctr32_getD _ _ _ (by simp)] at hb
  simp only [List.getD_cons_zero, Nat.repeat, BitVec.zero_xor] at hb
  rw [ctxH_eq, hb]
  simp only [Spec.Sm4.gcmCipherOfKey, hkey]
  exact BitVec.zero_xor

theorem init_correct (s : State) (hs : initX86.pre s) :
    ∃ t s', Exec isa (init) s t s' ∧ abiPreserved s s' ∧ initX86.post s s' :=
  (init_pc (pubOf 3 s)).wp s s ⟨hs, rfl, rfl⟩

theorem init_ct : ConstantTime isa initX86.pre initX86.pub (init) :=
  Pc.constantTime (pubOf 3) (fun _ _ _ _ h => pubOf_eq h) init_pc fun _ hs => ⟨hs, rfl, rfl⟩

end VG.Proof.Sm4Gcm.X86
