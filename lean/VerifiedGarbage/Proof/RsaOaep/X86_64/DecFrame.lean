import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.RsaOaep.X86_64.DecCtx
import VerifiedGarbage.Proof.RsaOaep.X86_64.EncCorrect

/-!
# RSAES-OAEP decryption on x86-64: the frame and the prologue

The frame of `frameBytes` bytes at `fb s`, below it the stack the function
uses (`stkD`), the caller's regions it writes (`out`, `*msg_len`, the
working space), and the prologue (`decPro_ok`): the argument slots, as
`decW` says.
-/

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp)
open VG.Proof.MlKem.X86_64 (Keep WP.keep ifp ifn)
open VG.Proof.RsaPkcs1Enc.X86_64 (privStack)

/-! ## The regions -/

/-- The stack the function uses, below `rsp`. -/
def stkD (s : State) : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 decStack, decStack⟩

/-- `*msg_len`. -/
def mlR (s : State) : Region := ⟨s.gpr .rdx, 8⟩

/-- The working space. -/
def scrD (s : State) : Region := ⟨stackArg s 15, (stackArg s 16).toNat * 8⟩

theorem frame_subD (s : State) : Region.Sub (frR s) (stkD s) :=
  Offset.sub_below _ (by decide) (by decide)

theorem below_subD (s : State) {n : Nat} (hn : n ≤ 8 + privStack) : Region.Sub (below (fb s) n) (stkD s) := by
  simp only [below, fb, sub_sub']
  exact Offset.sub_below _ (by unfold decStack frameBytes privStack at *; omega) (by unfold decStack frameBytes privStack at *; omega)

theorem ret_subD (s : State) : Region.Sub (below (fb s) 16) (stkD s) := below_subD s (by decide)

theorem fb_toNatD {s : State} (hp : DPre s) : (fb s).toNat + frameBytes = (s.gpr .rsp).toNat := by
  have := hp.sp1; unfold decStack privStack at this
  simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold frameBytes at *; omega

theorem DPre.hsl {s : State} (hp : DPre s) : 16 * (s.gpr .r8).toNat + 1024 ≤ (stackArg s 16).toNat := by
  have := hp.hsw; unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at this; omega

theorem DPre.geo {s : State} (hp : DPre s) : Geo (fb s) (stackArg s 15) := by
  have hF := fb_toNatD hp
  have := hp.sp2
  have hsl := hp.hsl
  have wS := hp.wS
  have sS : Region.Sub ⟨stackArg s 15, oRsa⟩ (scrD s) := Region.sub_prefix (by unfold oRsa; omega)
  refine ⟨by unfold frameBytes at *; omega, by unfold oRsa; omega,
    ((hp.dKs.sub_left (frame_subD s)).sub_right sS), ((hp.dKs.sub_left (ret_subD s)).sub_right sS)⟩

/-- Memory changed only in the stack the function uses, `out`, `*msg_len`
and the working space. -/
def FrD (s : State) (m : Mem) : Prop := Frame [stkD s, outR s, mlR s, scrD s] s.mem m

theorem FrD.bytes {s : State} {m : Mem} (h : FrD s m) {p : Addr} {len : Nat} (hk : (stkD s).Disjoint ⟨p, len⟩)
    (ho : (outR s).Disjoint ⟨p, len⟩) (hm : (mlR s).Disjoint ⟨p, len⟩) (hs : (scrD s).Disjoint ⟨p, len⟩)
    (hl : len ≤ 2 ^ 64) : Spec.Rsa.bytesAt m p len = Spec.Rsa.bytesAt s.mem p len := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => Frame.bytes h (R := ⟨p, len⟩) (fun r hr => ?_) hl (List.mem_range.mp hi)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hk.symm
  · exact ho.symm
  · exact hm.symm
  · exact hs.symm

theorem FrD.step {s : State} {m m' : Mem} (h : FrD s m) {ws : List Region}
    (hws : ws = [frR s, outR s, mlR s, scrD s]) (h' : Frame (ws ++ [below (fb s) 16]) m m') : FrD s m' :=
  h.trans (h'.sub fun r hr => by
    rw [hws] at hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., frame_subD s⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, List.mem_cons_self .., ret_subD s⟩)

theorem DPre.wr {s : State} (hp : DPre s) : (allocState frameBytes s).wr = [frR s, outR s, mlR s, scrD s] := by
  simp [allocState, hp.hwr, outR, mlR, scrD]

/-- In the frame, from the entry state `s`. -/
structure EnvD (s t : State) : Prop where
  rsp : t.gpr .rsp = fb s
  rd : t.rd = s.rd
  wr : t.wr = [frR s, outR s, mlR s, scrD s]
  cs : ∀ r ∈ calleeSaved, r ≠ .rsp → t.gpr r = s.gpr r
  mx : t.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10
  fr : FrD s t.mem

theorem EnvD.step {s t t' : State} (he : EnvD s t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hsp : t'.gpr .rsp = t.gpr .rsp) (hcs : ∀ r ∈ calleeSaved, r ≠ .rsp → t'.gpr r = t.gpr r)
    (hmx : t'.mxcsr = t.mxcsr) (hf : Frame (t.wr ++ [below (t.gpr .rsp) 16]) t.mem t'.mem) : EnvD s t' :=
  ⟨hsp.trans he.rsp, hrd.trans he.rd, hwr.trans he.wr, fun r hr h => (hcs r hr h).trans (he.cs r hr h),
    by rw [hmx]; exact he.mx, FrD.step he.fr (ws := t.wr) he.wr (by rw [he.rsp] at hf; exact hf)⟩

/-! ## The stack arguments -/

/-- Stack argument `j`, read from memory changed only in the frame. -/
theorem arg_readD {s : State} (hp : DPre s) {m : Mem} (hf : Frame [frR s] s.mem m) {j : Nat} (hj : j < 17) :
    m.readW (off (fb s) (frameBytes + 8 + 8 * j)) 64 = stackArg s j := by
  rw [argAddr]
  refine hf.readW (r := ⟨stackArgAddr s 0, 136⟩) ?_ (fun r' hr' => ?_) (by decide)
  · rw [stackArgAddr_j s j]
    exact Offset.contains_base _ (by omega) (by omega)
  · simp only [List.mem_singleton] at hr'; subst hr'
    exact (hp.dKa.sub_left (frame_subD s)).symm

/-- One stack argument copied to a slot. -/
theorem copy1D_ok {s : State} (hp : DPre s) {u : State} (hsp : u.gpr .rsp = fb s) (hfr : frR s ∈ u.wr)
    (hrd : u.rd = s.rd) (hf : Frame [frR s] s.mem u.mem) {j d : Nat} (hj : j < 17) (hd : d + 8 ≤ frameBytes) :
    WP isa (.block (argSlot j d)) u fun u' => Keep [.rax] u u' ∧
      u'.mem = u.mem.writeW (off (fb s) d) (stackArg s j) ∧ Frame [frR s] s.mem u'.mem := by
  have hF := fb_toNatD hp
  have := hp.sp2
  have hsc : Scr u (fb s) frameBytes := Scr.of_mem hfr (by unfold frameBytes at *; omega)
  have hin : InRegions (u.rd ++ u.wr) (off (fb s) (frameBytes + 8 + 8 * j)) 8 := by
    refine ⟨⟨stackArgAddr s 0, 136⟩, List.mem_append_left _ (by rw [hrd, hp.hrd]; simp), ?_⟩
    rw [argAddr, stackArgAddr_j s j]
    exact Offset.contains_base _ (by omega) (by omega)
  refine WP.mono (WP.keep [.rax] (Q := fun u' => u'.mem = u.mem.writeW (off (fb s) d) (stackArg s j)) ?_ rfl)
    fun u' ⟨hm, k⟩ => ⟨k, hm, hm ▸ hf.writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega) (by unfold frameBytes at *; omega))⟩
  xrun [argSlot, arg, ea_sp, hsp, hin, arg_readD hp hf hj, hsc.st (d := d) hd]

theorem frame_wD {s : State} (hp : DPre s) {m m' : Mem} (hf : Frame [frR s] m m') {d : Nat}
    (hd : d + 8 ≤ frameBytes) (v : BitVec 64) : Frame [frR s] m (m'.writeW (off (fb s) d) v) := by
  have hF := fb_toNatD hp
  have := hp.sp2
  exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by unfold frameBytes at *; omega))

/-! ## The prologue -/

/-- The slots `decPrologue` stores to, and what. -/
def decW (s : State) : Nat → BitVec 64 :=
  upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (fun k => word s.mem (fb s) (8 * k))
    21 (s.gpr .rdi)) 29 (s.gpr .rdx)) 22 (s.gpr .rcx)) 23 (s.gpr .r8)) 24 (s.gpr .r9))
    25 (stackArg s 0)) 27 (stackArg s 11)) 28 (stackArg s 12)) 14 (stackArg s 15)) 26 (stackArg s 16)

theorem decPrologue_eq : decPrologue =
    ([.store (sp sOut) .rdi, .store (sp sMl) .rdx, .store (sp sN) .rcx, .store (sp sK) .r8,
      .store (sp sE) .r9] : List Instr) ++ argSlot 0 sEl ++ argSlot 11 sLab ++ argSlot 12 sLabLen ++
    argSlot 15 sScr ++ argSlot 16 sScrLen := rfl

/-- The prologue: the slots as `decW` says, the working space untouched. -/
theorem decPro_ok {s : State} (hp : DPre s) :
    WP isa (.block decPrologue) (allocState frameBytes s) fun t => Keep [.rax] (allocState frameBytes s) t ∧
      Lay t (fb s) (stackArg s 15) ∧
      Rep t.mem (fb s) (stackArg s 15) (fun o => s.mem (off (stackArg s 15) o)) (decW s) ∧
      Frame [frR s] s.mem t.mem := by
  have hF := fb_toNatD hp
  have := hp.sp2
  have G' := hp.geo
  have hsp : (allocState frameBytes s).gpr .rsp = fb s := rfl
  have hfr : frR s ∈ (allocState frameBytes s).wr := List.mem_cons_self ..
  have hsc : Scr (allocState frameBytes s) (fb s) frameBytes := Scr.of_mem hfr (by unfold frameBytes at *; omega)
  have R0 : Rep s.mem (fb s) (stackArg s 15) (fun o => s.mem (off (stackArg s 15) o))
      (fun k => word s.mem (fb s) (8 * k)) := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  rw [decPrologue_eq, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff,
    WP.block_append_iff]
  have R1 := ((((R0.wf G' (k := 21) (by decide) (s.gpr .rdi)).wf G' (k := 29) (by decide) (s.gpr .rdx)).wf G'
    (k := 22) (by decide) (s.gpr .rcx)).wf G' (k := 23) (by decide) (s.gpr .r8)).wf G' (k := 24) (by decide)
    (s.gpr .r9)
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = ((((s.mem.writeW (off (fb s) (8 * 21)) (s.gpr .rdi)).writeW
      (off (fb s) (8 * 29)) (s.gpr .rdx)).writeW (off (fb s) (8 * 22)) (s.gpr .rcx)).writeW (off (fb s) (8 * 23))
      (s.gpr .r8)).writeW (off (fb s) (8 * 24)) (s.gpr .r9)) ?_ rfl) fun t1 ⟨hm1, k1⟩ => ?_
  · xrun [ea_sp, hsp, hsc.st (d := sOut) (by decide), hsc.st (d := sMl) (by decide), hsc.st (d := sN) (by decide),
      hsc.st (d := sK) (by decide), hsc.st (d := sE) (by decide), allocState_gpr']
    rfl
  have f1 : Frame [frR s] s.mem t1.mem := by
    rw [hm1]
    exact frame_wD hp (frame_wD hp (frame_wD hp (frame_wD hp (frame_wD hp (Frame.refl _ _) (by decide) _)
      (by decide) _) (by decide) _) (by decide) _) (by decide) _
  have sp1 : t1.gpr .rsp = fb s := k1.gpr (by decide)
  have hfr1 : frR s ∈ t1.wr := k1.2.2 ▸ hfr
  refine WP.mono (copy1D_ok hp sp1 hfr1 k1.2.1 f1 (j := 0) (d := sEl) (by decide) (by decide))
    fun t2 ⟨k2, hm2, f2⟩ => ?_
  refine WP.mono (copy1D_ok hp ((k2.gpr (by decide)).trans sp1) (k2.2.2 ▸ hfr1) (k2.2.1.trans k1.2.1) f2
    (j := 11) (d := sLab) (by decide) (by decide)) fun t3 ⟨k3, hm3, f3⟩ => ?_
  have k23 := k2.trans k3
  refine WP.mono (copy1D_ok hp ((k23.gpr (by decide)).trans sp1) (k23.2.2 ▸ hfr1) (k23.2.1.trans k1.2.1) f3
    (j := 12) (d := sLabLen) (by decide) (by decide)) fun t4 ⟨k4, hm4, f4⟩ => ?_
  have k24 := k23.trans k4
  refine WP.mono (copy1D_ok hp ((k24.gpr (by decide)).trans sp1) (k24.2.2 ▸ hfr1) (k24.2.1.trans k1.2.1) f4
    (j := 15) (d := sScr) (by decide) (by decide)) fun t5 ⟨k5, hm5, f5⟩ => ?_
  have k25 := k24.trans k5
  refine WP.mono (copy1D_ok hp ((k25.gpr (by decide)).trans sp1) (k25.2.2 ▸ hfr1) (k25.2.1.trans k1.2.1) f5
    (j := 16) (d := sScrLen) (by decide) (by decide)) fun t6 ⟨k6, hm6, f6⟩ => ?_
  have k16 : Keep [.rax] (allocState frameBytes s) t6 := (k1.trans (k25.trans k6)).mono (by decide)
  have R6 : Rep t6.mem (fb s) (stackArg s 15) (fun o => s.mem (off (stackArg s 15) o)) (decW s) := by
    rw [hm6, hm5, hm4, hm3, hm2, hm1]
    exact ((((R1.wf G' (k := 25) (by decide) (stackArg s 0)).wf G' (k := 27) (by decide) (stackArg s 11)).wf G'
      (k := 28) (by decide) (stackArg s 12)).wf G' (k := 14) (by decide) (stackArg s 15)).wf G' (k := 26)
      (by decide) (stackArg s 16)
  have := hp.sp1
  refine ⟨k16, ⟨(k16.gpr (by decide)).trans hsp, k16.2.2 ▸ hfr, ?_, ?_, ?_, ?_, G'.dFS, G'.dRS⟩, R6, f6⟩
  · unfold decStack privStack at this; unfold frameBytes at *; omega
  · unfold frameBytes at *; omega
  · have hsl := hp.hsl
    have hk := hp.lv.1
    refine ⟨⟨stackArg s 15, 0, (stackArg s 16).toNat * 8, by rw [k16.2.2]; simp [allocState, hp.hwr],
      (BitVec.add_zero _).symm, by unfold oRsa; omega, hp.wS.trans' (by omega)⟩, G'.Sw⟩
  · rw [show sScr = 8 * 14 from rfl]
    exact (R6.fr 14 (by decide)).trans (by simp [decW, upd])

/-! ## The private-key operation's arguments -/

/-- The frame's words after `privArgs`: the private-key operation's stack
arguments in words 0 to 13. -/
def privW (s : State) : Nat → BitVec 64 :=
  upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (decW s)
    0 (stackArg s 13)) 1 (s.gpr .r8)) 2 (stackArg s 1)) 3 (stackArg s 2)) 4 (stackArg s 3)) 5 (stackArg s 4))
    6 (stackArg s 5)) 7 (stackArg s 6)) 8 (stackArg s 7)) 9 (stackArg s 8)) 10 (stackArg s 9))
    11 (stackArg s 10)) 12 (off (stackArg s 15) oRsa)) 13 (stackArg s 16 - 1024)

theorem privArgs_eq : privArgs =
    argSlot 13 0 ++ ([.mov .rax (.mem (sp sK)), .store (sp 8) .rax] : List Instr) ++ argSlot 1 16 ++
    argSlot 2 24 ++ argSlot 3 32 ++ argSlot 4 40 ++ argSlot 5 48 ++ argSlot 6 56 ++ argSlot 7 64 ++
    argSlot 8 72 ++ argSlot 9 80 ++ argSlot 10 88 ++
    (scr .rax oRsa ++ ([.store (sp 96) .rax] : List Instr)) ++
    ([.mov .rax (.mem (sp sScrLen)), .alu .sub .rax (.imm 1024), .store (sp 104) .rax] : List Instr) ++
    (scr .rdi oEm ++ ([.mov .rsi (.mem (sp sK)), .mov .rdx (.mem (sp sN)),
      .mov .rcx (.mem (sp sK)), .mov .r8 (.mem (sp sE)), .mov .r9 (.mem (sp sEl))] : List Instr)) := by kernel_rfl

/-- A copy of a stack argument to the frame's word `k`, with `Rep`. -/
theorem copyRep_ok {s : State} (hp : DPre s) {u : State} (L : Lay u (fb s) (stackArg s 15)) {V : Nat → Byte}
    {W : Nat → BitVec 64} (R : Rep u.mem (fb s) (stackArg s 15) V W) (hrd : u.rd = s.rd)
    (hf : Frame [frR s] s.mem u.mem) (hfr : frR s ∈ u.wr) {j k : Nat} (hj : j < 17) (hk : k < 14) :
    WP isa (.block (argSlot j (8 * k))) u fun u' => Keep [.rax] u u' ∧ Lay u' (fb s) (stackArg s 15) ∧
      Rep u'.mem (fb s) (stackArg s 15) V (upd W k (stackArg s j)) ∧ Frame [frR s] s.mem u'.mem ∧
      u'.rd = s.rd ∧ frR s ∈ u'.wr :=
  WP.mono (copy1D_ok hp L.rsp hfr hrd hf hj (d := 8 * k) (by unfold frameBytes; omega))
    fun u' ⟨k', hm, f'⟩ =>
      have R' : Rep u'.mem (fb s) (stackArg s 15) V (upd W k (stackArg s j)) := hm ▸ R.wf L.geo (by
        unfold nW frameBytes; omega) _
      ⟨k', L.of_rep' R R' (by simp only [upd]; rw [ifn (by omega)]) (k'.gpr (by decide)) k'.2.2, R', f',
        k'.2.1.trans hrd, k'.2.2 ▸ hfr⟩

/-- After the prologue and the private-key operation's arguments. -/
structure DSet (s t : State) : Prop where
  he : EnvD s t
  L : Lay t (fb s) (stackArg s 15)
  R : Rep t.mem (fb s) (stackArg s 15) (fun o => s.mem (off (stackArg s 15) o)) (privW s)
  rdi : t.gpr .rdi = off (stackArg s 15) oEm
  rsi : t.gpr .rsi = s.gpr .r8
  rdx : t.gpr .rdx = s.gpr .rcx
  rcx : t.gpr .rcx = s.gpr .r8
  r8 : t.gpr .r8 = s.gpr .r9
  r9 : t.gpr .r9 = stackArg s 0

theorem privArgs_ok {s u : State} (hp : DPre s) (L : Lay u (fb s) (stackArg s 15)) {V : Nat → Byte}
    (R : Rep u.mem (fb s) (stackArg s 15) V (decW s)) (hrd : u.rd = s.rd) (hf : Frame [frR s] s.mem u.mem)
    (hfr : frR s ∈ u.wr) :
    WP isa (.block privArgs) u fun u' => Keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] u u' ∧
      Lay u' (fb s) (stackArg s 15) ∧ Rep u'.mem (fb s) (stackArg s 15) V (privW s) ∧
      Frame [frR s] s.mem u'.mem ∧ u'.gpr .rdi = off (stackArg s 15) oEm ∧ u'.gpr .rsi = s.gpr .r8 ∧
      u'.gpr .rdx = s.gpr .rcx ∧ u'.gpr .rcx = s.gpr .r8 ∧ u'.gpr .r8 = s.gpr .r9 ∧
      u'.gpr .r9 = stackArg s 0 := by
  have G' := hp.geo
  rw [privArgs_eq]
  repeat rw [WP.block_append_iff]
  refine WP.mono (copyRep_ok hp L R hrd hf hfr (j := 13) (k := 0) (by decide) (by decide))
    fun t1 ⟨k1, L1, R1, f1, rd1, fr1⟩ => ?_
  -- `k` to word 1.
  have hs1 := R1.slot (d := sK) (k := 23) rfl (by decide) (v := s.gpr .r8) (by simp [upd, decW])
  refine WP.mono (WP.keep [.rax] (Q := fun u => u.mem = t1.mem.writeW (off (fb s) (8 * 1)) (s.gpr .r8)) ?_ rfl)
    fun t2 ⟨hm2, k2⟩ => ?_
  · xrun [ea_sp, L1.rsp, L1.ld (d := sK) (by decide), hs1, L1.st (d := 8) (by decide)]
  have R2 : Rep t2.mem (fb s) (stackArg s 15) _ _ := hm2 ▸ R1.wf G' (k := 1) (by decide) (s.gpr .r8)
  have L2 := L1.of_rep' R1 R2 (by simp [upd]) (k2.gpr (by decide)) k2.2.2
  have f2 : Frame [frR s] s.mem t2.mem := hm2 ▸ frame_wD hp f1 (d := 8) (by decide) _
  have rd2 : t2.rd = s.rd := k2.2.1.trans rd1
  have fr2 : frR s ∈ t2.wr := k2.2.2 ▸ fr1
  refine WP.mono (copyRep_ok hp L2 R2 rd2 f2 fr2 (j := 1) (k := 2) (by decide) (by decide))
    fun t3 ⟨k3, L3, R3, f3, rd3, fr3⟩ => ?_
  refine WP.mono (copyRep_ok hp L3 R3 rd3 f3 fr3 (j := 2) (k := 3) (by decide) (by decide))
    fun t4 ⟨k4, L4, R4, f4, rd4, fr4⟩ => ?_
  refine WP.mono (copyRep_ok hp L4 R4 rd4 f4 fr4 (j := 3) (k := 4) (by decide) (by decide))
    fun t5 ⟨k5, L5, R5, f5, rd5, fr5⟩ => ?_
  refine WP.mono (copyRep_ok hp L5 R5 rd5 f5 fr5 (j := 4) (k := 5) (by decide) (by decide))
    fun t6 ⟨k6, L6, R6, f6, rd6, fr6⟩ => ?_
  refine WP.mono (copyRep_ok hp L6 R6 rd6 f6 fr6 (j := 5) (k := 6) (by decide) (by decide))
    fun t7 ⟨k7, L7, R7, f7, rd7, fr7⟩ => ?_
  refine WP.mono (copyRep_ok hp L7 R7 rd7 f7 fr7 (j := 6) (k := 7) (by decide) (by decide))
    fun t8 ⟨k8, L8, R8, f8, rd8, fr8⟩ => ?_
  refine WP.mono (copyRep_ok hp L8 R8 rd8 f8 fr8 (j := 7) (k := 8) (by decide) (by decide))
    fun t9 ⟨k9, L9, R9, f9, rd9, fr9⟩ => ?_
  refine WP.mono (copyRep_ok hp L9 R9 rd9 f9 fr9 (j := 8) (k := 9) (by decide) (by decide))
    fun t10 ⟨k10, L10, R10, f10, rd10, fr10⟩ => ?_
  refine WP.mono (copyRep_ok hp L10 R10 rd10 f10 fr10 (j := 9) (k := 10) (by decide) (by decide))
    fun t11 ⟨k11, L11, R11, f11, rd11, fr11⟩ => ?_
  refine WP.mono (copyRep_ok hp L11 R11 rd11 f11 fr11 (j := 10) (k := 11) (by decide) (by decide))
    fun t12 ⟨k12, L12, R12, f12, rd12, fr12⟩ => ?_
  -- The working space's address and length, and the registers.
  have hs := L12.slot
  simp only [Bignum.X86_64.word] at hs
  have kk := (((((((((((k1.trans k2).trans k3).trans k4).trans k5).trans k6).trans k7).trans k8).trans k9).trans
    k10).trans k11).trans k12)
  refine WP.mono (WP.keep [.rax] (Q := fun u' => u'.mem =
      t12.mem.writeW (off (fb s) (8 * 12)) (off (stackArg s 15) oRsa)) ?_ rfl) fun t13 ⟨hm13, k13⟩ => ?_
  · xrun [scr, Impl.Mgf1.X86_64.scr, lay, List.cons_append, List.nil_append, ea_sp, L12.rsp,
      L12.ld (d := sScr) (by decide), hs, L12.st (d := 96) (by decide),
      VG.Proof.MlKem.X86_64.sx_ofNat (show oRsa < 2 ^ 31 by decide)]
  have R13 : Rep t13.mem (fb s) (stackArg s 15) V _ := hm13 ▸ R12.wf G' (k := 12) (by decide) (off (stackArg s 15) oRsa)
  have L13 := L12.of_rep' R12 R13 (by simp [upd]) (k13.gpr (by decide)) k13.2.2
  refine WP.mono (WP.keep [.rax] (Q := fun u' => u'.mem =
      t13.mem.writeW (off (fb s) (8 * 13)) (stackArg s 16 - 1024)) ?_ rfl) fun t14 ⟨hm14, k14⟩ => ?_
  · xrun [ea_sp, L13.rsp, L13.ld (d := sScrLen) (by decide), L13.st (d := 104) (by decide),
      R13.slot (d := sScrLen) (k := 26) rfl (by decide) (v := stackArg s 16) (by simp [upd, decW]),
      show BitVec.signExtend 64 (1024 : BitVec 32) = 1024 from by decide]
  have R14 : Rep t14.mem (fb s) (stackArg s 15) V (privW s) := hm14 ▸ R13.wf G' (k := 13) (by decide) _
  have L14 := L13.of_rep' R13 R14 (by simp [upd, privW]) (k14.gpr (by decide)) k14.2.2
  have hs' := L14.slot
  simp only [Bignum.X86_64.word] at hs'
  refine WP.mono (WP.keep [.rdi, .rsi, .rdx, .rcx, .r8, .r9] (Q := fun u' => u'.mem = t14.mem ∧
      u'.gpr .rdi = off (stackArg s 15) oEm ∧ u'.gpr .rsi = s.gpr .r8 ∧ u'.gpr .rdx = s.gpr .rcx ∧
      u'.gpr .rcx = s.gpr .r8 ∧ u'.gpr .r8 = s.gpr .r9 ∧ u'.gpr .r9 = stackArg s 0) ?_ rfl)
    fun u' ⟨⟨hm, h1, h2, h3, h4, h5, h6⟩, k'⟩ => ?_
  · xrun [scr, Impl.Mgf1.X86_64.scr, lay, List.cons_append, List.nil_append, ea_sp, L14.rsp,
      L14.ld (d := sScr) (by decide), L14.ld (d := sK) (by decide), L14.ld (d := sN) (by decide),
      L14.ld (d := sE) (by decide), L14.ld (d := sEl) (by decide), hs',
      R14.slot (d := sK) (k := 23) rfl (by decide) (v := s.gpr .r8) (by simp [upd, privW, decW]),
      R14.slot (d := sN) (k := 22) rfl (by decide) (v := s.gpr .rcx) (by simp [upd, privW, decW]),
      R14.slot (d := sE) (k := 24) rfl (by decide) (v := s.gpr .r9) (by simp [upd, privW, decW]),
      R14.slot (d := sEl) (k := 25) rfl (by decide) (v := stackArg s 0) (by simp [upd, privW, decW]),
      VG.Proof.MlKem.X86_64.sx_ofNat (show oEm < 2 ^ 31 by decide)]
  have Ru : Rep u'.mem (fb s) (stackArg s 15) V (privW s) := by rw [hm]; exact R14
  exact ⟨(kk.trans (k13.trans (k14.trans k'))).mono (by decide),
    L14.of_rep' R14 Ru rfl (k'.gpr (by decide)) k'.2.2, Ru,
    by rw [hm, hm14, hm13]; exact frame_wD hp (frame_wD hp f12 (d := 96) (by decide) _) (d := 104) (by decide) _,
    h1, h2, h3, h4, h5, h6⟩

theorem decHead_ok {s : State} (hp : DPre s) :
    WP isa (.block (decPrologue ++ privArgs)) (allocState frameBytes s) (DSet s) := by
  rw [WP.block_append_iff]
  refine WP.mono (wp_good (block_good _ rfl) (decPro_ok hp)) fun t0 ⟨⟨k0, L0, R0, f0⟩, sp0, mx0, _⟩ => ?_
  have hfr0 : frR s ∈ t0.wr := by rw [k0.2.2]; exact List.mem_cons_self ..
  refine WP.mono (wp_good (block_good _ rfl) (privArgs_ok hp L0 R0 k0.2.1 f0 hfr0)) fun t ⟨⟨k, L, R, f, h1, h2, h3, h4, h5, h6⟩, sp, mx, _⟩ => ?_
  refine ⟨⟨L.rsp, k.2.1.trans k0.2.1, k.2.2.trans (k0.2.2.trans hp.wr), fun r hr h => ?_, by rw [mx, mx0]; rfl,
    f.sub fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., frame_subD s⟩⟩,
    L, R, h1, h2, h3, h4, h5, h6⟩
  rw [k.gpr (cs_disj _ (by decide) r hr), k0.gpr (cs_disj [.rax] (by decide) r hr)]
  show (if r = .rsp then _ else s.gpr r) = s.gpr r
  simp only [h, ↓reduceIte]

end VG.Proof.RsaOaep.X86_64
