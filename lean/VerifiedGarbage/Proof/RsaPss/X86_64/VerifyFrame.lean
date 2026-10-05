import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyCtx
import VerifiedGarbage.Proof.RsaPss.X86_64.SignPro

/-!
# RSASSA-PSS verification on x86-64: the precondition by name, the frame
and the prologue

`VPre` names the facts of `verifyK.pre`; the frame is the `frameBytes` bytes
below `rsp` (`fb`), within the stack the function uses (`vstkR`). From the
entry state, after the frame's push, `verifyPrologue` saves `rbx`, `rbp` and
`r12` and the arguments to their slots (`verifyPro_ok`).
-/

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)

variable (G : Spec.Mgf1.Hash)

/-- `verifyK.pre`, by name. -/
structure VPre (s : State) : Prop where
  sp1 : verifyStack ≤ (s.gpr .rsp).toNat
  sp2 : (s.gpr .rsp).toNat + 48 ≤ 2 ^ 64
  hrd : s.rd = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨s.gpr .r8, G.len⟩,
    ⟨s.gpr .r9, (stackArg s 0).toNat⟩, ⟨stackArgAddr s 0, 40⟩]
  hwr : s.wr = [⟨stackArg s 3, (stackArg s 4).toNat * 8⟩]
  dns : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  des : (⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  ddgs : (⟨s.gpr .r8, G.len⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  dsgs : (⟨s.gpr .r9, (stackArg s 0).toNat⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  dsa : (⟨stackArg s 3, (stackArg s 4).toNat * 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 40⟩
  dRn : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  dRe : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  dRdg : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .r8, G.len⟩
  dRsg : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .r9, (stackArg s 0).toNat⟩
  dRs : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  dRa : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 40⟩
  dKn : (⟨s.gpr .rsp - BitVec.ofNat 64 verifyStack, verifyStack⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  dKe : (⟨s.gpr .rsp - BitVec.ofNat 64 verifyStack, verifyStack⟩ : Region).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  dKdg : (⟨s.gpr .rsp - BitVec.ofNat 64 verifyStack, verifyStack⟩ : Region).Disjoint ⟨s.gpr .r8, G.len⟩
  dKsg : (⟨s.gpr .rsp - BitVec.ofNat 64 verifyStack, verifyStack⟩ : Region).Disjoint ⟨s.gpr .r9, (stackArg s 0).toNat⟩
  dKs : (⟨s.gpr .rsp - BitVec.ofNat 64 verifyStack, verifyStack⟩ : Region).Disjoint
    ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  dKa : (⟨s.gpr .rsp - BitVec.ofNat 64 verifyStack, verifyStack⟩ : Region).Disjoint ⟨stackArgAddr s 0, 40⟩
  wN : (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64
  wE : (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64
  wDg : (s.gpr .r8).toNat + G.len ≤ 2 ^ 64
  wSg : (s.gpr .r9).toNat + (stackArg s 0).toNat ≤ 2 ^ 64
  wS : (stackArg s 3).toNat + (stackArg s 4).toNat * 8 ≤ 2 ^ 64
  k1 : 64 ≤ (s.gpr .rsi).toNat
  k2 : (s.gpr .rsi).toNat ≤ 1024
  L1 : 1 ≤ (s.gpr .rcx).toNat
  L2 : (s.gpr .rcx).toNat ≤ (s.gpr .rsi).toNat
  hsg : (stackArg s 0).toNat = (s.gpr .rsi).toNat
  hsl : 16 * (s.gpr .rsi).toNat + 1024 ≤ (stackArg s 4).toNat

theorem VPre.of {s : State} (h : (verifyK G).pre s) : VPre G s := by
  simp only [verifyK] at h
  obtain ⟨sp1, sp2, hrd, hwr, dns, des, ddgs, dsgs, dsa, dRn, dRe, dRdg, dRsg, dRs, dRa, dKn, dKe, dKdg, dKsg, dKs,
    dKa, wN, wE, wDg, wSg, wS, ⟨k1, k2⟩, L1, L2, hsg, hsl⟩ := h
  exact ⟨sp1, sp2, hrd, hwr, dns, des, ddgs, dsgs, dsa, dRn, dRe, dRdg, dRsg, dRs, dRa, dKn, dKe, dKdg, dKsg, dKs,
    dKa, wN, wE, wDg, wSg, wS, k1, k2, L1, L2, hsg,
    by unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at hsl; omega⟩

/-! ## The frame -/

/-- The stack the function uses, below `rsp`. -/
def vstkR (s : State) : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 verifyStack, verifyStack⟩

theorem vframe_sub (s : State) : Region.Sub ⟨fb s, frameBytes⟩ (vstkR s) :=
  Offset.sub_below _ (by decide) (by decide)

theorem vret_sub (s : State) : Region.Sub (below (fb s) 8) (vstkR s) := by
  simp only [below, fb, sub_sub']
  exact Offset.sub_below _ (by decide) (by decide)

/-- The region the function writes: its stack and `scratch`. -/
def vscrR (s : State) : Region := ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩

abbrev vwrR (s : State) : List Region := [vstkR s, vscrR s]

/-- An input, apart from them. -/
theorem vin_apart {s : State} {R : Region} (hK : (vstkR s).Disjoint R) (hS : R.Disjoint (vscrR s)) :
    ∀ r ∈ vwrR s, R.Disjoint r := by
  intro r hr
  simp only [vwrR, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hK.symm
  · exact hS

/-- An address of an input: in no writable region of the frame's state, nor
below the frame. -/
theorem VPre.outside {s : State} (hp : VPre G s) {R : Region}
    (hS : R.Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩) (hK : (vstkR s).Disjoint R) {a : Addr}
    (ha : R.Contains a 1) : Outside (⟨fb s, frameBytes⟩ :: s.wr) (fb s) a := by
  refine ⟨fun r hr hc => ?_, fun hc => hK a (vret_sub s a hc) ha⟩
  rw [List.mem_cons, hp.hwr] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hK a (vframe_sub s a hc) ha
  · exact hS a ha hc

variable {G}

theorem vfb_toNat {s : State} (hp : VPre G s) : (fb s).toNat + frameBytes = (s.gpr .rsp).toNat := by
  have := hp.sp1; unfold verifyStack at this
  simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold frameBytes at *; omega

theorem VPre.geo {s : State} (hp : VPre G s) : Geo (fb s) (stackArg s 3) := by
  have hF := vfb_toNat hp
  have := hp.sp2
  have hsl := hp.hsl
  have hk := hp.k1
  have wS := hp.wS
  have sS : Region.Sub ⟨stackArg s 3, oRsa⟩ ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩ :=
    Region.sub_prefix (by unfold oRsa; omega)
  refine ⟨by omega, by unfold oRsa; omega, ((hp.dKs.sub_left (vframe_sub s)).sub_right sS),
    ((hp.dKs.sub_left (vret_sub s)).sub_right sS)⟩

/-- Stack argument `j`, read from memory changed only in the frame. -/
theorem varg_read {s : State} (hp : VPre G s) {m : Mem} (hf : Frame [frR s] s.mem m) {j : Nat} (hj : j < 5) :
    m.readW (off (fb s) (frameBytes + 8 + 8 * j)) 64 = stackArg s j := by
  rw [argAddr]
  refine hf.readW (r := ⟨stackArgAddr s 0, 40⟩) ?_ (fun r' hr' => ?_) (by decide)
  · rw [show stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) by
      simp only [stackArgAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega]
    have := hp.sp2
    exact Offset.contains_base _ (by omega) (by omega)
  · simp only [List.mem_singleton] at hr'; subst hr'
    exact (hp.dKa.sub_left (vframe_sub s)).symm

/-- The address of stack argument `j` is readable. -/
theorem varg_in {s : State} (hp : VPre G s) {u : State} (hrd : u.rd = s.rd) {j : Nat} (hj : j < 5)
    (n : Nat := 8) (hn : n ≤ 8 := by decide) :
    InRegions (u.rd ++ u.wr) (off (fb s) (frameBytes + 8 + 8 * j)) n := by
  have := hp.sp2
  refine ⟨⟨stackArgAddr s 0, 40⟩, List.mem_append_left _ (by rw [hrd, hp.hrd]; simp), ?_⟩
  rw [argAddr, show stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) by
    simp only [stackArgAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega]
  exact Offset.contains_base _ (by omega) (by omega)

theorem vframe_w {s : State} (hp : VPre G s) {m m' : Mem} (hf : Frame [frR s] m m') {d : Nat}
    (hd : d + 8 ≤ frameBytes) (v : BitVec 64) : Frame [frR s] m (m'.writeW (off (fb s) d) v) := by
  have hF := vfb_toNat hp
  have := hp.sp2
  exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))

/-- One stack argument copied to a slot. -/
theorem vcopy1_ok {s : State} (hp : VPre G s) {u : State} (hsp : u.gpr .rsp = fb s) (hfr : frR s ∈ u.wr)
    (hrd : u.rd = s.rd) (hf : Frame [frR s] s.mem u.mem) {j d : Nat} (hj : j < 5) (hd : d + 8 ≤ frameBytes) :
    WP isa (.block [.mov .rax (.mem (arg j)), .store (sp d) .rax]) u fun u' => Keep [.rax] u u' ∧
      u'.mem = u.mem.writeW (off (fb s) d) (stackArg s j) ∧ Frame [frR s] s.mem u'.mem := by
  have hF := vfb_toNat hp
  have := hp.sp2
  have hsc : Scr u (fb s) frameBytes := Scr.of_mem hfr (by omega)
  refine WP.mono (WP.keep [.rax] (Q := fun u' => u'.mem = u.mem.writeW (off (fb s) d) (stackArg s j)) ?_ rfl)
    fun u' ⟨hm, k⟩ => ⟨k, hm, hm ▸ vframe_w hp hf hd _⟩
  xrun [arg, ea_sp, hsp, varg_in hp hrd hj, varg_read hp hf hj, hsc.st (d := d) hd]

/-- The slots `verifyPrologue` stores to, and what. -/
def vproW (s : State) : Nat → BitVec 64 :=
  upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (fun k => word s.mem (fb s) (8 * k))
    41 (s.gpr .rbx)) 42 (s.gpr .rbp)) 43 (s.gpr .r12)) 18 (s.gpr .rdi)) 17 (s.gpr .rsi)) 19 (s.gpr .rdx))
    20 (s.gpr .rcx)) 37 (s.gpr .r8)) 38 (s.gpr .r9)) 21 (stackArg s 3)) 22 (stackArg s 4)

theorem verifyPrologue_eq : verifyPrologue =
    ([.store (sp sRbx) .rbx, .store (sp sRbp) .rbp, .store (sp sR12) .r12, .store (sp sN) .rdi,
      .store (sp sK) .rsi, .store (sp sE) .rdx, .store (sp sEl) .rcx, .store (sp sDig) .r8,
      .store (sp sSig) .r9] : List Instr) ++
    ([.mov .rax (.mem (arg 3)), .store (sp sScr) .rax] : List Instr) ++
    ([.mov .rax (.mem (arg 4)), .store (sp sScrLen) .rax] : List Instr) := rfl

/-- The prologue: the slots as `vproW` says, the working space untouched. -/
theorem verifyPro_ok {s : State} (hp : VPre G s) :
    WP isa (.block verifyPrologue) (allocState frameBytes s) fun t => Keep [.rax] (allocState frameBytes s) t ∧
      Lay t (fb s) (stackArg s 3) ∧ Rep t.mem (fb s) (stackArg s 3) (fun o => s.mem (off (stackArg s 3) o)) (vproW s) ∧
      Frame [frR s] s.mem t.mem := by
  have hF := vfb_toNat hp
  have := hp.sp2
  have G' := hp.geo
  set A := allocState frameBytes s with hA
  have hsp : A.gpr .rsp = fb s := rfl
  have hfr : frR s ∈ A.wr := List.mem_cons_self ..
  have hsc : Scr A (fb s) frameBytes := Scr.of_mem hfr (by omega)
  have R0 : Rep s.mem (fb s) (stackArg s 3) (fun o => s.mem (off (stackArg s 3) o))
      (fun k => word s.mem (fb s) (8 * k)) := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  rw [verifyPrologue_eq, WP.block_append_iff, WP.block_append_iff]
  have R1 := (((((((((R0.wf G' (k := 41) (by decide) (s.gpr .rbx)).wf G' (k := 42) (by decide) (s.gpr .rbp)).wf G'
    (k := 43) (by decide) (s.gpr .r12)).wf G' (k := 18) (by decide) (s.gpr .rdi)).wf G' (k := 17) (by decide)
    (s.gpr .rsi)).wf G' (k := 19) (by decide) (s.gpr .rdx)).wf G' (k := 20) (by decide) (s.gpr .rcx)).wf G'
    (k := 37) (by decide) (s.gpr .r8)).wf G' (k := 38) (by decide) (s.gpr .r9))
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = ((((((((s.mem.writeW (off (fb s) (8 * 41)) (s.gpr .rbx)).writeW
      (off (fb s) (8 * 42)) (s.gpr .rbp)).writeW (off (fb s) (8 * 43)) (s.gpr .r12)).writeW (off (fb s) (8 * 18))
      (s.gpr .rdi)).writeW (off (fb s) (8 * 17)) (s.gpr .rsi)).writeW (off (fb s) (8 * 19)) (s.gpr .rdx)).writeW
      (off (fb s) (8 * 20)) (s.gpr .rcx)).writeW (off (fb s) (8 * 37)) (s.gpr .r8)).writeW (off (fb s) (8 * 38))
      (s.gpr .r9)) ?_ rfl) fun t1 ⟨hm1, k1⟩ => ?_
  · xrun [ea_sp, hsp, hsc.st (d := sRbx) (by decide), hsc.st (d := sRbp) (by decide), hsc.st (d := sR12) (by decide),
      hsc.st (d := sN) (by decide), hsc.st (d := sK) (by decide), hsc.st (d := sE) (by decide),
      hsc.st (d := sEl) (by decide), hsc.st (d := sDig) (by decide), hsc.st (d := sSig) (by decide), allocState_gpr']
    rfl
  have f1 : Frame [frR s] s.mem t1.mem := by
    rw [hm1]
    exact vframe_w hp (vframe_w hp (vframe_w hp (vframe_w hp (vframe_w hp (vframe_w hp (vframe_w hp (vframe_w hp
      (vframe_w hp (Frame.refl _ _) (by decide) _) (by decide) _) (by decide) _) (by decide) _) (by decide) _)
      (by decide) _) (by decide) _) (by decide) _) (by decide) _
  have sp1 : t1.gpr .rsp = fb s := k1.gpr (by decide)
  refine WP.mono (vcopy1_ok hp sp1 (k1.2.2 ▸ hfr) k1.2.1 f1 (j := 3) (d := sScr) (by decide) (by decide))
    fun t2 ⟨k2, hm2, f2⟩ => ?_
  refine WP.mono (vcopy1_ok hp ((k2.gpr (by decide)).trans sp1) (k2.2.2 ▸ k1.2.2 ▸ hfr) (k2.2.1.trans k1.2.1) f2
    (j := 4) (d := sScrLen) (by decide) (by decide)) fun t3 ⟨k3, hm3, f3⟩ => ?_
  have k13 : Keep [.rax] A t3 := (k1.trans (k2.trans k3)).mono (by decide)
  have R3 : Rep t3.mem (fb s) (stackArg s 3) (fun o => s.mem (off (stackArg s 3) o)) (vproW s) := by
    rw [hm3, hm2, hm1]
    exact (R1.wf G' (k := 21) (by decide) (stackArg s 3)).wf G' (k := 22) (by decide) (stackArg s 4)
  have := hp.sp1
  have h392 : frameBytes = 392 := rfl
  have hvs : verifyStack = 400 := rfl
  refine ⟨k13, ⟨(k13.gpr (by decide)).trans hsp, k13.2.2 ▸ hfr, by omega, by omega, ?_, ?_, G'.dFS, G'.dRS⟩, R3, f3⟩
  · have hsl := hp.hsl
    have hk := hp.k1
    refine ⟨⟨stackArg s 3, 0, (stackArg s 4).toNat * 8, by rw [k13.2.2, hA]; simp [allocState, hp.hwr],
      (BitVec.add_zero _).symm, by unfold oRsa; omega, hp.wS.trans' (by omega)⟩, G'.Sw⟩
  · rw [show sScr = 8 * 21 from rfl]
    exact (R3.fr 21 (by decide)).trans (by simp [vproW, upd])

/-! ## The salt length's arguments -/

theorem readW32_low (m : Mem) (a : Addr) : m.readW a 32 = (m.readW a 64).setWidth 32 := by
  have e := Mem.read_eq_of_bytes (n := 4) (v := (m.readW a 64).setWidth 32) (a := a) (m := m) fun i hi => by
    rw [BitVec.extractLsb'_setWidth_of_le (by omega)]
    show _ = ((m.read a 8).setWidth 64).extractLsb' (8 * i) 8
    rw [BitVec.extractLsb'_setWidth_of_le (by omega), Mem.extractLsb'_read m a (by omega : i < 8)]
  show (m.read a 4).setWidth 32 = _
  rw [e]; exact BitVec.setWidth_eq _

/-- Stack argument `j`, read from memory the function changed only where it
may write. -/
theorem varg_read' {s : State} (hp : VPre G s) {m : Mem} (hf : Frame (vwrR s) s.mem m) {j : Nat} (hj : j < 5) :
    m.readW (off (fb s) (frameBytes + 8 + 8 * j)) 64 = stackArg s j := by
  rw [argAddr]
  refine hf.readW (r := ⟨stackArgAddr s 0, 40⟩) ?_ (vin_apart hp.dKa hp.dsa.symm) (by decide)
  rw [show stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) by
    simp only [stackArgAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega]
  have := hp.sp2
  exact Offset.contains_base _ (by omega) (by omega)

theorem zext32_beq_zero (x : BitVec 32) : (BitVec.setWidth 64 x == 0) = decide (x = 0) := by
  by_cases h : x = 0
  · subst h; rfl
  · have : BitVec.setWidth 64 x ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by
      have := congrArg BitVec.toNat e
      simp only [BitVec.toNat_setWidth] at this
      rw [Nat.mod_eq_of_lt (by omega)] at this
      exact this))
    rw [beq_eq_false_iff_ne.mpr this, decide_eq_false h]

/-- `sSlen := salt_len`, `sAny := any_salt_len ≠ 0`, and `rdx` the salt
length the encoding must fit, 0 for any. -/
theorem anyArgs_ok {s : State} (hp : VPre G s) {u : State} {S : Addr} (L : Lay u (fb s) S) (hrd : u.rd = s.rd)
    (hf : Frame (vwrR s) s.mem u.mem) {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep u.mem (fb s) S V W) :
    WP isa anyArgs u fun u' => Lay u' (fb s) S ∧ Keep [.rax, .rdx] u u' ∧
      Rep u'.mem (fb s) S V (upd (upd W 36 (stackArg s 1)) 35
        (if (stackArg s 2).setWidth 32 = 0 then 0 else 1)) ∧
      u'.gpr .rdx = if (stackArg s 2).setWidth 32 = 0 then stackArg s 1 else 0 := by
  have G' := L.geo
  have R1 := R.wf G' (k := 36) (by decide) (stackArg s 1)
  rw [show off (fb s) (8 * 36) = off (fb s) sSlen from rfl] at R1
  have hF := vfb_toNat hp
  have := hp.sp2
  have a1 := varg_read' hp hf (j := 1) (by decide)
  have a2 : (u.mem.writeW (off (fb s) sSlen) (stackArg s 1)).readW (off (fb s) (frameBytes + 8 + 8 * 2)) 32 =
      (stackArg s 2).setWidth 32 := by
    rw [readW32_low, Mem.readW_writeW_sep (Offset.sep _ (.inr (by unfold sSlen frameBytes; omega))
      (by unfold frameBytes; omega) (by unfold sSlen; omega)) (by decide), varg_read' hp hf (j := 2) (by decide)]
  refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun v => v.mem = u.mem.writeW (off (fb s) sSlen) (stackArg s 1) ∧
      v.zf = some (decide ((stackArg s 2).setWidth 32 = 0))) ?_ rfl) fun v ⟨⟨hm, hz⟩, hk⟩ => ?_)
  · xrun [anyArgs, arg, ea_sp, L.rsp, varg_in hp hrd (j := 1) (by decide), varg_in hp hrd (j := 2) (by decide) 4, a1, a2,
      L.st (d := sSlen) (by decide)]
    rw [BitVec.and_self, zext32_beq_zero]
  have R1' : Rep v.mem (fb s) S V (upd W 36 (stackArg s 1)) := hm ▸ R1
  have Lv : Lay v (fb s) S := L.of_rep' R R1' (by simp [upd]) (hk.gpr (by decide)) hk.2.2
  have R2 := R1'.wf G' (k := 35) (by decide) (if (stackArg s 2).setWidth 32 = 0 then 0 else 1)
  rw [show off (fb s) (8 * 35) = off (fb s) sAny from rfl] at R2
  refine WP.ite (M := isa) _ (show isa.eval .e v = _ from hz) (fun hb => ?_) (fun hb => ?_)
  · rw [decide_eq_true_eq] at hb
    rw [ifp hb] at R2 ⊢
    rw [ifp hb]
    have e36 : (v.mem.writeW (off (fb s) sAny) (0 : BitVec 64)).readW (off (fb s) sSlen) 64 = stackArg s 1 := by
      rw [R2.rd (d := sSlen) 36 rfl (by decide)]; simp [upd]
    refine WP.mono (WP.keep [.rax, .rdx] (Q := fun w => w.mem = v.mem.writeW (off (fb s) sAny) (0 : BitVec 64) ∧
        w.gpr .rdx = stackArg s 1) ?_ rfl)
      fun w ⟨⟨hm', hdx⟩, k'⟩ => ⟨Lv.of_rep' R1' (hm' ▸ R2) (by simp [upd]) (k'.gpr (by decide)) k'.2.2,
        (hk.trans k').mono (by decide), hm' ▸ R2, hdx⟩
    xrun [ea_sp, Lv.rsp, Lv.st (d := sAny) (by decide), Lv.ld (d := sSlen) (by decide),
      show BitVec.setWidth 64 (0 : BitVec 32) = (0 : BitVec 64) from rfl, e36]
  · rw [decide_eq_false_iff_not] at hb
    rw [ifn hb] at R2 ⊢
    rw [ifn hb]
    refine WP.mono (WP.keep [.rax, .rdx] (Q := fun w => w.mem = v.mem.writeW (off (fb s) sAny) (1 : BitVec 64) ∧
        w.gpr .rdx = 0) ?_ rfl)
      fun w ⟨⟨hm', hdx⟩, k'⟩ => ⟨Lv.of_rep' R1' (hm' ▸ R2) (by simp [upd]) (k'.gpr (by decide)) k'.2.2,
        (hk.trans k').mono (by decide), hm' ▸ R2, hdx⟩
    xrun [ea_sp, Lv.rsp, Lv.st (d := sAny) (by decide),
      show BitVec.setWidth 64 (1 : BitVec 32) = (1 : BitVec 64) from rfl,
      show BitVec.setWidth 64 (0 : BitVec 32) = (0 : BitVec 64) from rfl]

end VG.Proof.RsaPss.X86_64
