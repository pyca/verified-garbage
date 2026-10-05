import VerifiedGarbage.Proof.AesOcb.X86.Calls

/-!
# AES-OCB on x86: `vg_aes_ocb_init`

Untrusted: everything here is checked by Lean. The entry (our caller's
registers saved in `scratch`, the arguments into its slots), the key
schedule (`vg_aes_expand_key`), then `L_* = ENCIPHER(K, zeros(128))`
(`vg_aes_encrypt_blocks` on a zero block at byte 240 of the key context),
as one `Pc` (`init_pc`): correct (`init_correct`) and constant time
(`init_ct`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (blockAtMem KeyRepr)
open VG.Proof.AesOcb.X86 (zero4_fold)
open VG.Proof.Aes.X86 (BlocksImpl)
open VG.Impl.AesGcm.X86 (at_ imm slot argOp keep entry saveAt restore)
open VG.Proof.AesGcm.X86 (w64 w64_add slotv slotv_eq argA argsR argsR_eq argA_contains argA_sub SavedAt save_ok
  KeepEnv keeps_ok keepR runBlock_app_of in_off below_eq covers_left covers_off covers_cons covers_nil Pc pubOf
  pubOf_arg pubOf_esp pubOf_eq argIn_of arg0_ok ret_kept ret_below ofNat_lit ofNat_toNat32 toNat_add32
  toNat_ofNat32 exit_ok KeyCall KeyPost add_ofNat_assoc32 CT length_bytesAt)

/-- The facts of `init`'s precondition about the public data `p` alone. -/
structure InitPure (p : BitVec 32 × (Nat → BitVec 32)) : Prop where
  kc : (⟨w64 (p.2 0), (p.2 1).toNat⟩ : Region).Disjoint ⟨w64 (p.2 2), 256⟩
  kw : (⟨w64 (p.2 0), (p.2 1).toNat⟩ : Region).Disjoint ⟨w64 (p.2 3), 2560⟩
  cw : (⟨w64 (p.2 2), 256⟩ : Region).Disjoint ⟨w64 (p.2 3), 2560⟩
  r_c : (⟨w64 p.1, 4⟩ : Region).Disjoint ⟨w64 (p.2 2), 256⟩
  r_w : (⟨w64 p.1, 4⟩ : Region).Disjoint ⟨w64 (p.2 3), 2560⟩
  k_k : (below p.1 24).Disjoint ⟨w64 (p.2 0), (p.2 1).toNat⟩
  k_c : (below p.1 24).Disjoint ⟨w64 (p.2 2), 256⟩
  k_w : (below p.1 24).Disjoint ⟨w64 (p.2 3), 2560⟩
  fk : (p.2 0).toNat + (p.2 1).toNat ≤ 2 ^ 32
  fc : (p.2 2).toNat + 256 ≤ 2 ^ 32
  fw : (p.2 3).toNat + 2560 ≤ 2 ^ 32
  sp : 24 ≤ p.1.toNat
  len : (p.2 1).toNat = 16 ∨ (p.2 1).toNat = 24 ∨ (p.2 1).toNat = 32

theorem initPure_of {p : BitVec 32 × (Nat → BitVec 32)} {s : State} (h : initPre s) (hp : pubOf 4 s = p) :
    InitPure p := by
  simp only [initPre] at h
  obtain ⟨-, -, d_kc, d_kw, -, d_cw, -, -, -, r_c, r_w, -, k_k, k_c, k_w, -, fk, fc, fw, sp, -, hl⟩ := h
  simp only [keyR, ictxR, scrR, retR, stackR] at d_kc d_kw d_cw r_c r_w k_k k_c k_w
  rw [show (24 : Addr) = BitVec.ofNat 64 24 from rfl, below_eq sp] at k_k k_c k_w
  have a0 := pubOf_arg hp (i := 0) (by decide); have a1 := pubOf_arg hp (i := 1) (by decide)
  have a2 := pubOf_arg hp (i := 2) (by decide); have a3 := pubOf_arg hp (i := 3) (by decide)
  have e := pubOf_esp hp
  simp only [a0, a1, a2, a3, e] at d_kc d_kw d_cw r_c r_w k_k k_c k_w fk fc fw sp hl
  exact ⟨d_kc, d_kw, d_cw, r_c, r_w, k_k, k_c, k_w, fk, fc, fw, sp, hl⟩

/-- The arguments the entry copies, and where. -/
abbrev initPs : List (Nat × Nat) := [(0, nO), (1, nlO), (2, ctxO)]

theorem initEntry_eq : (entry 3 (keep 0 nO ++ keep 1 nlO ++ keep 2 ctxO) : Prog isa) =
    entry 3 (initPs.flatMap (fun p => keep p.1 p.2)) := rfl

/-- After the entry. -/
structure IEnt (p : BitVec 32 × (Nat → BitVec 32)) (s₀ s : State) : Prop where
  pre : initPre s₀
  pub : pubOf 4 s₀ = p
  ebp : s.gpr .ebp = p.2 3
  esp : s.gpr .esp = p.1
  sK : slotv s.mem (p.2 3) nO = p.2 0
  sL : slotv s.mem (p.2 3) nlO = p.2 1
  sC : slotv s.mem (p.2 3) ctxO = p.2 2
  saved : SavedAt s.mem (p.2 3) s₀
  frame : Frame [⟨w64 (p.2 3) + BitVec.ofNat 64 128, 64⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem iEntry_pc (p : BitVec 32 × (Nat → BitVec 32)) :
    Pc (fun (s₀ : State) s => initPre s₀ ∧ pubOf 4 s₀ = p ∧ s = s₀)
      (entry 3 (keep 0 nO ++ keep 1 nlO ++ keep 2 ctxO)) (IEnt p) := by
  rw [initEntry_eq]
  refine ⟨fun s₀ s ⟨hpre, hpub, hs⟩ => ?_, ?_⟩
  · subst s
    have hc := initPure_of hpre hpub
    have hp := hpre
    simp only [initPre] at hp
    obtain ⟨hrd, hwr, -, -, -, -, -, d_wa, -, -, -, -, -, -, -, -, -, -, -, -, fa, -⟩ := hp
    have a : ∀ i, i < 4 → arg s₀ i = p.2 i := fun i hi => pubOf_arg hpub hi
    have wW : Covers [⟨w64 (arg s₀ 3), 2560⟩] s₀.wr := by rw [hwr]; exact covers_of_mem (by simp)
    have rA : Covers [argsR (s₀.gpr .esp) 4] (s₀.rd ++ s₀.wr) := by
      rw [argsR_eq, hrd, hwr]; exact covers_of_mem (by simp)
    have aw : (argsR (s₀.gpr .esp) 4).Disjoint ⟨w64 (arg s₀ 3), 2560⟩ := by rw [argsR_eq]; exact d_wa.symm
    have fw : (arg s₀ 3).toNat + 2560 ≤ 2 ^ 32 := by rw [a 3 (by decide)]; exact hc.fw
    have fa' : (s₀.gpr .esp).toNat + 4 + 4 * 4 ≤ 2 ^ 32 := by omega
    generalize hSP : s₀.gpr .esp = SP at rA aw fa'
    have i₀ : InRegions (s₀.rd ++ s₀.wr) (argA SP 3) 4 :=
      rA _ _ ⟨_, List.mem_singleton_self _, argA_contains (by decide) fa'⟩
    refine WP.seq (WP.of_runBlock ⟨_, by grun [hSP, i₀], ?_⟩)
    have hax : (s₀.setReg .eax (s₀.mem.readW (argA SP 3) 32)).gpr .eax = arg s₀ 3 := by
      rw [gpr_setReg_self, ← hSP]; rfl
    set t₀ := s₀.setReg .eax (s₀.mem.readW (argA SP 3) 32) with ht₀
    obtain ⟨s₁, run₁, bp₁, g₁, rd₁, wr₁, sv₁, f₁⟩ := save_ok t₀ hax (by rw [ht₀]; exact wW) fw
    have sp₁ : s₁.gpr .esp = SP := by rw [g₁ _ (by decide), ht₀, gpr_setReg_of_ne _ _ (by decide), hSP]
    have hA₁ : ∀ i < 4, s₁.mem.readW (argA SP i) 32 = arg s₀ i := fun i hi => by
      rw [f₁.readW (r := ⟨argA SP i, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (aw.sub_left (argA_sub hi fa')).sub_right (Lay.wSub (by decide))) (by decide)]
      rw [arg, argAddr, hSP]
      exact rfl
    have ke : KeepEnv (arg s₀ 3) SP 4 s₁ := ⟨bp₁, sp₁, by rw [wr₁]; exact wW, by rw [rd₁, wr₁]; exact rA, aw, fa', fw⟩
    obtain ⟨s₃, run₃, sl₃, f₃, g₃, rd₃, wr₃⟩ := keeps_ok initPs (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> decide) (by decide) ke
    refine WP.of_runBlock ⟨_, runBlock_app_of run₁ run₃, ?_⟩
    have f₃' : Frame [⟨w64 (arg s₀ 3) + BitVec.ofNat 64 128, 64⟩] s₀.mem s₃.mem := by
      refine (f₁.sub fun r hr => ?_).trans (f₃.sub fun r hr => ?_)
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
      · simp only [List.mem_map] at hr
        obtain ⟨q, hq, rfl⟩ := hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl <;> exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
    have hsv : SavedAt s₃.mem (arg s₀ 3) s₀ := by
      have := sv₁.frame f₃ fun r hr => by
        simp only [List.mem_map] at hr
        obtain ⟨q, hq, rfl⟩ := hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl <;> exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      obtain ⟨a, b, c, d⟩ := this
      refine ⟨a.trans ?_, b.trans ?_, c.trans ?_, d.trans ?_⟩ <;>
        simp only [ht₀, gpr_setReg_of_ne _ _ (by decide : Reg.ebx ≠ .eax),
          gpr_setReg_of_ne _ _ (by decide : Reg.esi ≠ .eax), gpr_setReg_of_ne _ _ (by decide : Reg.edi ≠ .eax),
          gpr_setReg_of_ne _ _ (by decide : Reg.ebp ≠ .eax)]
    have sl : ∀ q ∈ initPs, slotv s₃.mem (arg s₀ 3) q.2 = p.2 q.1 := fun q hq => by
      have e := sl₃ q hq
      have hq1 : q.1 < 4 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl <;> decide
      rw [hA₁ q.1 hq1, a q.1 hq1] at e
      exact e
    rw [a 3 (by decide)] at f₃' hsv sl
    exact ⟨hpre, hpub, by rw [g₃ _ (by decide), bp₁, a 3 (by decide)],
      by rw [g₃ _ (by decide), sp₁, ← hSP]; exact pubOf_esp hpub, sl (0, nO) (by simp), sl (1, nlO) (by simp),
      sl (2, ctxO) (by simp), hsv, f₃', by rw [rd₃, rd₁]; rfl, by rw [wr₃, wr₁]; rfl⟩
  · refine CT.seq (J := fun s => s.gpr .eax = p.2 3 ∧ s.gpr .esp = p.1)
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
    obtain ⟨hrd, hwr, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, fa, -⟩ := hp
    have rA : Covers [argsR (s₀.gpr .esp) 4] (s₀.rd ++ s₀.wr) := by
      rw [argsR_eq, hrd, hwr]; exact covers_of_mem (by simp)
    exact WP.mono (arg0_ok (argIn_of rA (by omega) (by decide))) fun s' ⟨ax, sp⟩ =>
      ⟨by rw [ax]; exact pubOf_arg hpub (by decide), by rw [sp]; exact pubOf_esp hpub⟩

theorem shr2_32 {n : Nat} (hn : n < 2 ^ 32) : BitVec.ofNat 32 n >>> 2 = BitVec.ofNat 32 (n / 4) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]

/-- `W` and the key context apart, at offsets. -/
theorem InitPure.cw' {p : BitVec 32 × (Nat → BitVec 32)} (h : InitPure p) {a n d k : Nat} (ha : a + n ≤ 256)
    (hd : d + k ≤ 2560) :
    (⟨w64 (p.2 2) + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨w64 (p.2 3) + BitVec.ofNat 64 d, k⟩ :=
  (h.cw.sub_left (Offset.sub_base _ ha)).sub_right (Lay.wSub hd)

/-- The arguments of `vg_aes_expand_key`. -/
abbrev iArgs : List Instr :=
  [.mov .eax (slot nO), .mov .ecx (slot nlO), .mov .edx (slot ctxO), .alu .add .ebp (imm scrO)]

/-- After `iArgs`: the call of `vg_aes_expand_key`. -/
structure IArg (p : BitVec 32 × (Nat → BitVec 32)) (s₀ s : State) : Prop where
  pre : initPre s₀
  pub : pubOf 4 s₀ = p
  call : KeyCall s (p.2 0) (p.2 2) (p.2 3 + BitVec.ofNat 32 512) (p.2 1).toNat
  esp : s.gpr .esp = p.1
  sL : slotv s.mem (p.2 3) nlO = p.2 1
  sC : slotv s.mem (p.2 3) ctxO = p.2 2
  saved : SavedAt s.mem (p.2 3) s₀
  frame : Frame [⟨w64 (p.2 3) + BitVec.ofNat 64 128, 64⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- What the precondition lets `init` read and write. -/
theorem init_perm {p : BitVec 32 × (Nat → BitVec 32)} {s₀ : State} (hpre : initPre s₀) (hpub : pubOf 4 s₀ = p) :
    s₀.rd = [⟨w64 (p.2 0), (p.2 1).toNat⟩] ∧
      s₀.wr = [⟨w64 (p.2 2), 256⟩, ⟨w64 (p.2 3), 2560⟩, ⟨argAddr s₀ 0, 16⟩] := by
  have hp := hpre
  simp only [initPre] at hp
  rw [hp.1, hp.2.1]
  simp only [keyR, ictxR, scrR, iargsR, pubOf_arg hpub (i := 0) (by decide), pubOf_arg hpub (i := 1) (by decide),
    pubOf_arg hpub (i := 2) (by decide), pubOf_arg hpub (i := 3) (by decide), and_self]

theorem iArgs_pc (p : BitVec 32 × (Nat → BitVec 32)) : Pc (IEnt p) (.block iArgs) (IArg p) := by
  refine Pc.taint [.ebp] (fun s₀ s h => ?_) (fun _ _ s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.ebp, h₂.ebp]) (by taint_decide)
  have hc := initPure_of h.pre h.pub
  obtain ⟨hrd, hwr⟩ := init_perm h.pre h.pub
  have wW : Covers [⟨w64 (p.2 3), 2560⟩] s.wr := by rw [h.wr, hwr]; exact covers_of_mem (by simp)
  have wC : Covers [⟨w64 (p.2 2), 256⟩] s.wr := by rw [h.wr, hwr]; exact covers_of_mem (by simp)
  have aW : ∀ {o}, o < 2560 → w64 (p.2 3 + BitVec.ofNat 32 o) = w64 (p.2 3) + BitVec.ofNat 64 o :=
    fun ho => w64_add (by have := hc.fw; omega)
  have rIn : ∀ {o}, o + 4 ≤ 2560 → InRegions (s.rd ++ s.wr) (w64 (p.2 3) + BitVec.ofNat 64 o) 4 :=
    fun ho => Proof.AesGcm.X86.in_left (in_off wW ho (by decide))
  have sK := h.sK
  have sL := h.sL
  have sC := h.sC
  simp only [slotv_eq] at sK sL sC
  have eS := w64_add (x := p.2 3) (k := 512) (by have := hc.fw; omega)
  have bsub : Region.Sub (below p.1 20) (below p.1 24) := VG.X86.below_sub (by decide) hc.sp
  refine WP.of_runBlock ⟨_, by grun [h.ebp, aW, rIn, sK, sL, sC], ?_⟩
  refine ⟨h.pre, h.pub, ⟨by gregs [sK], by gregs [sL]; exact (ofNat_toNat32 _).symm, by gregs [sC],
    by gregs [h.ebp], hc.len, by gregs [h.esp]; have := hc.sp; omega,
    hc.kc.sub_right (Region.sub_prefix (by decide)), by rw [eS]; exact hc.kw.sub_right (Lay.wSub (by decide)),
    by rw [eS]; exact (hc.cw.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide)),
    by gregs [h.esp]; exact hc.k_k.sub_left bsub,
    by gregs [h.esp]; exact (hc.k_c.sub_left bsub).sub_right (Region.sub_prefix (by decide)),
    by gregs [h.esp]; rw [eS]; exact (hc.k_w.sub_left bsub).sub_right (Lay.wSub (by decide)),
    hc.fk, by have := hc.fc; omega, by rw [toNat_add32 (by have := hc.fw; omega)]; have := hc.fw; omega,
    by gmems [h.rd, h.wr, hrd]; exact covers_of_mem (by simp), ?_⟩, by gregs [h.esp], by gmems []; exact h.sL,
    by gmems []; exact h.sC, by gmems []; exact h.saved, by gmems []; exact h.frame, by gmems [h.rd],
    by gmems [h.wr]⟩
  rw [eS]
  gmems [h.wr, hwr]
  have c₁ : Covers [⟨w64 (p.2 2), 240⟩] [⟨w64 (p.2 2), 256⟩, ⟨w64 (p.2 3), 2560⟩, ⟨argAddr s₀ 0, 16⟩] := by
    have := covers_off (p := w64 (p.2 2)) (k := 256) (d := 0) (n := 240)
      (rs := [⟨w64 (p.2 2), 256⟩, ⟨w64 (p.2 3), 2560⟩, ⟨argAddr s₀ 0, 16⟩]) (covers_of_mem (by simp)) (by decide)
      (by decide)
    simpa using this
  exact covers_cons c₁ (covers_cons (covers_off (p := w64 (p.2 3)) (k := 2560) (d := 512) (n := 512)
    (covers_of_mem (by simp)) (by decide) (by decide)) covers_nil)

/-- After the key schedule: `0` into bytes 240–255 of the key context. -/
abbrev mid1 : List Instr :=
  [.alu .sub .ebp (imm scrO), .mov .edx (slot ctxO), .mov .eax (imm 0), .store (at_ .edx 240) .eax,
    .store (at_ .edx 244) .eax, .store (at_ .edx 248) .eax, .store (at_ .edx 252) .eax]

/-- The arguments of `vg_aes_encrypt_blocks` for `L_*`. -/
abbrev mid2 : List Instr :=
  [.mov .eax (.reg .edx), .mov .ecx (slot nlO), .shift .shr .ecx 2, .alu .add .ecx (imm 6),
    .alu .add .edx (imm 240), .mov .ebx (imm 1), .alu .add .ebp (imm scrO)]

/-- After `mid1 ++ mid2`: the call of `vg_aes_encrypt_blocks` on the block at byte 240. -/
structure IMid (p : BitVec 32 × (Nat → BitVec 32)) (s₀ s : State) : Prop where
  pre : initPre s₀
  pub : pubOf 4 s₀ = p
  call : BCall s (p.2 2) (p.2 2 + BitVec.ofNat 32 240) (p.2 3 + BitVec.ofNat 32 512) ((p.2 1).toNat / 4 + 6) 1
  esp : s.gpr .esp = p.1
  sched : bytesAt s.mem (w64 (p.2 2)) (16 * ((p.2 1).toNat / 4 + 6 + 1)) =
    Spec.Aes.expandKey (bytesAt s₀.mem (w64 (p.2 0)) (p.2 1).toNat)
  zero : blockAtMem s.mem (w64 (p.2 2) + BitVec.ofNat 64 240) = 0
  saved : SavedAt s.mem (p.2 3) s₀
  frame : Frame [⟨w64 (p.2 2), 256⟩, ⟨w64 (p.2 3), 2560⟩, below p.1 24] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem rounds_of_len {L : Nat} (h : L = 16 ∨ L = 24 ∨ L = 32) : L / 4 + 6 = 10 ∨ L / 4 + 6 = 12 ∨ L / 4 + 6 = 14 := by
  rcases h with rfl | rfl | rfl <;> decide

theorem iMid_ok {p : BitVec 32 × (Nat → BitVec 32)} {s₀ s₁ s : State} (h : IArg p s₀ s₁)
    (g : KeyPost s₁ (p.2 0) (p.2 2) (p.2 3 + BitVec.ofNat 32 512) (p.2 1).toNat s) :
    WP isa (.block (mid1 ++ mid2)) s (IMid p s₀) := by
  have hc := initPure_of h.pre h.pub
  obtain ⟨hrd, hwr⟩ := init_perm h.pre h.pub
  have hfw := hc.fw
  have hfc := hc.fc
  have hsp := hc.sp
  have eS := w64_add (x := p.2 3) (k := 512) (by omega)
  have eH := w64_add (x := p.2 2) (k := 240) (by omega)
  have bp : s.gpr .ebp = p.2 3 + BitVec.ofNat 32 512 := by rw [g.saved .ebp (by decide), h.call.ebp]
  have sp : s.gpr .esp = p.1 := by rw [g.saved .esp (by decide), h.esp]
  have hb0 : p.2 3 + BitVec.ofNat 32 512 - BitVec.ofNat 32 512 = p.2 3 := BitVec.add_sub_cancel _ _
  have bsub : Region.Sub (below p.1 20) (below p.1 24) := VG.X86.below_sub (by decide) hsp
  have gf := g.frame
  rw [h.esp, eS] at gf
  -- What the key call keeps: the slots, the saved registers.
  have dG : ∀ {d k : Nat}, (128 ≤ d ∧ d + k ≤ 512) → ∀ r ∈ [(⟨w64 (p.2 2), 240⟩ : Region),
      ⟨w64 (p.2 3) + BitVec.ofNat 64 512, 512⟩, below p.1 20],
      (⟨w64 (p.2 3) + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun {d k} hd r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hc.cw.sub_left (Region.sub_prefix (by decide))).symm.sub_left (Lay.wSub (d := d) (n := k) (by omega))
    · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
    · exact ((hc.k_w.sub_left bsub).sub_right (Lay.wSub (by omega))).symm
  have sC := h.sC
  have sL := h.sL
  rw [slotv_eq, ← gf.readW (Region.contains_self _ _) (dG ⟨by decide, by decide⟩) (by decide)] at sC sL
  have wW : Covers [⟨w64 (p.2 3), 2560⟩] s.wr := by rw [g.wr, h.wr, hwr]; exact covers_of_mem (by simp)
  have wC : Covers [⟨w64 (p.2 2), 256⟩] s.wr := by rw [g.wr, h.wr, hwr]; exact covers_of_mem (by simp)
  have aW : ∀ {o}, o < 2560 → w64 (p.2 3 + BitVec.ofNat 32 o) = w64 (p.2 3) + BitVec.ofNat 64 o :=
    fun ho => w64_add (by omega)
  have aC : ∀ {o}, o < 256 → w64 (p.2 2 + BitVec.ofNat 32 o) = w64 (p.2 2) + BitVec.ofNat 64 o :=
    fun ho => w64_add (by omega)
  have rIn : ∀ {o}, o + 4 ≤ 2560 → InRegions (s.rd ++ s.wr) (w64 (p.2 3) + BitVec.ofNat 64 o) 4 :=
    fun ho => Proof.AesGcm.X86.in_left (in_off wW ho (by decide))
  have cIn : ∀ {o}, o + 4 ≤ 256 → InRegions s.wr (w64 (p.2 2) + BitVec.ofNat 64 o) 4 :=
    fun ho => in_off wC ho (by decide)
  -- `mid1`.
  obtain ⟨t, run₁, m₁, bp₁, dx₁, g₁, rd₁, wr₁⟩ : ∃ t, runBlock isa mid1 s = some t ∧
      t.mem = Proof.Cmac.zero4 s.mem (w64 (p.2 2) + BitVec.ofNat 64 240) ∧ t.gpr .ebp = p.2 3 ∧
      t.gpr .edx = p.2 2 ∧ (∀ r, r ≠ .eax → r ≠ .edx → r ≠ .ebp → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr :=
    ⟨_, by grun [bp, hb0, aW, rIn, sC, aC, cIn], by gmems []; exact zero4_fold _ _ _, by gregs [bp, hb0],
      by gregs [sC], fun r h₁ h₂ h₃ => by gregs [h₁, h₂, h₃], by gmems [], by gmems []⟩
  have f₁ : Frame [⟨w64 (p.2 2) + BitVec.ofNat 64 240, 16⟩] s.mem t.mem := by
    rw [m₁]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  have sL₁ : t.mem.readW (w64 (p.2 3) + BitVec.ofNat 64 nlO) 32 = p.2 1 := by
    rw [f₁.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hc.cw' (by decide) (by decide)).symm) (by decide)]
    exact sL
  have hL : (p.2 1).toNat < 2 ^ 32 := (p.2 1).isLt
  have hsh : p.2 1 >>> 2 + BitVec.ofNat 32 6 = BitVec.ofNat 32 ((p.2 1).toNat / 4 + 6) := by
    rw [← ofNat_toNat32 (p.2 1), shr2_32 hL, Proof.AesGcm.X86.ofNat_add_ofNat32, toNat_ofNat32 hL]
  have rIn₁ : ∀ {o}, o + 4 ≤ 2560 → InRegions (t.rd ++ t.wr) (w64 (p.2 3) + BitVec.ofNat 64 o) 4 := fun ho => by
    rw [rd₁, wr₁]; exact rIn ho
  -- `mid2`.
  obtain ⟨u, run₂, m₂, ax₂, cx₂, dx₂, bx₂, bp₂, g₂, rd₂, wr₂⟩ : ∃ u, runBlock isa mid2 t = some u ∧
      u.mem = t.mem ∧ u.gpr .eax = p.2 2 ∧ u.gpr .ecx = BitVec.ofNat 32 ((p.2 1).toNat / 4 + 6) ∧
      u.gpr .edx = p.2 2 + BitVec.ofNat 32 240 ∧ u.gpr .ebx = BitVec.ofNat 32 1 ∧
      u.gpr .ebp = p.2 3 + BitVec.ofNat 32 512 ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .ebx → r ≠ .ebp → u.gpr r = t.gpr r) ∧ u.rd = t.rd ∧
      u.wr = t.wr :=
    ⟨_, by grun [bp₁, aW, rIn₁, sL₁, dx₁], by gmems [], by gregs [dx₁], by gregs [sL₁, hsh], by gregs [dx₁],
      by gregs [], by gregs [bp₁], fun r h₁ h₂ h₃ h₄ h₅ => by gregs [h₁, h₂, h₃, h₄, h₅], by gmems [], by gmems []⟩
  refine WP.of_runBlock ⟨u, runBlock_app_of run₁ run₂, ?_⟩
  have spU : u.gpr .esp = p.1 := by
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide), g₁ _ (by decide) (by decide) (by decide), sp]
  have hR := rounds_of_len hc.len
  have hRb : 16 * ((p.2 1).toNat / 4 + 6 + 1) ≤ 240 := by rcases hR with h' | h' | h' <;> omega
  have go := g.out
  rw [Proof.AesGcm.X86.bytesAt_frame h.frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hc.kw.sub_right (Lay.wSub (by decide)))
    (by have := hc.fk; omega)] at go
  have hrw : u.wr = s₀.wr := by rw [wr₂, wr₁, g.wr, h.wr]
  have hrd' : u.rd = s₀.rd := by rw [rd₂, rd₁, g.rd, h.rd]
  have kd : (⟨w64 (p.2 2), 240⟩ : Region).Disjoint ⟨w64 (p.2 2 + BitVec.ofNat 32 240), 16 * 1⟩ := by
    rw [eH]
    have := Offset.disjoint (w64 (p.2 2)) (d := 0) (n := 240) (e := 240) (k := 16 * 1) (.inl (by omega)) (by omega)
      (by omega)
    simpa using this
  have uW : Covers [⟨w64 (p.2 3), 2560⟩] u.wr := by rw [hrw, hwr]; exact covers_of_mem (by simp)
  have uC : Covers [⟨w64 (p.2 2), 256⟩] u.wr := by rw [hrw, hwr]; exact covers_of_mem (by simp)
  have rC : Covers [⟨w64 (p.2 2), 240⟩] (u.rd ++ u.wr) := by
    have := covers_off (p := w64 (p.2 2)) (k := 256) (d := 0) (n := 240) (rs := u.wr) uC (by decide) (by decide)
    exact covers_left (by simpa using this)
  have wB : Covers [⟨w64 (p.2 2 + BitVec.ofNat 32 240), 16 * 1⟩, ⟨w64 (p.2 3 + BitVec.ofNat 32 512), 2048⟩] u.wr := by
    rw [eH, eS]
    exact covers_cons (covers_off uC (by decide) (by decide)) (covers_cons (covers_off uW (by decide) (by decide))
      covers_nil)
  refine ⟨h.pre, h.pub, ⟨ax₂, cx₂, dx₂, bx₂, bp₂, hR, by rw [spU]; exact hsp, kd,
    by rw [eS]; exact (hc.cw.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide)),
    by rw [eH, eS]; exact hc.cw' (by decide) (by decide),
    by rw [spU]; exact hc.k_c.sub_right (Region.sub_prefix (by decide)),
    by rw [spU, eH]; exact hc.k_c.sub_right (Offset.sub_base _ (by decide)),
    by rw [spU, eS]; exact hc.k_w.sub_right (Lay.wSub (by decide)),
    by omega, by rw [Proof.AesGcm.X86.toNat_add32 (by omega)]; omega,
    by rw [Proof.AesGcm.X86.toNat_add32 (by omega)]; omega, rC, wB⟩, spU, ?_, ?_, ?_, ?_, hrd', hrw⟩
  · have dZ : ∀ r ∈ [(⟨w64 (p.2 2) + BitVec.ofNat 64 240, 16⟩ : Region)],
        (⟨w64 (p.2 2), 16 * ((p.2 1).toNat / 4 + 6 + 1)⟩ : Region).Disjoint r := fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      have := Offset.disjoint (w64 (p.2 2)) (d := 0) (n := 16 * ((p.2 1).toNat / 4 + 6 + 1)) (e := 240) (k := 16)
        (.inl (by omega)) (by omega) (by omega)
      simpa using this
    rw [m₂, Proof.AesGcm.X86.bytesAt_frame f₁ dZ (by omega)]
    exact go
  · rw [m₂, m₁]; exact blockAtMem_zero4 _ _
  · rw [m₂]
    exact (h.saved.frame gf (dG ⟨by decide, by decide⟩)).frame f₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hc.cw' (by decide) (by decide)).symm
  · rw [m₂]
    refine ((h.frame.sub fun r hr => ?_).trans (gf.sub fun r hr => ?_)).trans (f₁.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Lay.wSub (by decide)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Lay.wSub (by decide)⟩
      · exact ⟨_, by simp, bsub⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., Offset.sub_base _ (by decide)⟩

end VG.Proof.AesOcb.X86
