module

public import VerifiedGarbage.Proof.RsaOaep.X86_64.DecSpec
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Out
public import VerifiedGarbage.Proof.RsaOaep.Scan
import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Core
public import VerifiedGarbage.Proof.RsaOaep.Decode
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Stack
import VerifiedGarbage.Proof.RsaOaep.X86_64.EncMain
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.RsaOaep.X86_64.Good
import VerifiedGarbage.Proof.RsaOaep.X86_64.EncEm
import VerifiedGarbage.Proof.RsaOaep.X86_64.Hash
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
public import VerifiedGarbage.Proof.RsaOaep.X86_64.MgfT
import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.RsaOaep.X86_64.DecCtx
public import VerifiedGarbage.Proof.RsaOaep.X86_64.EncCall
import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Bignum.X86_64.Mont

/-! ### `RsaOaep.X86_64.DecFrame`, which this module and modules that import it used -/

section

/-!
# RSAES-OAEP decryption on x86-64: the frame and the prologue

The frame of `frameBytes` bytes at `fb s`, below it the stack the function
uses (`stkD`), the caller's regions it writes (`out`, `*msg_len`, the
working space), and the prologue (`decPro_ok`): the argument slots, as
`decW` says.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaOaep.X86_64
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
  exact Offset.sub_below _ (by unfold decStack frameBytes privStack at *; omega_using [hn]) (by unfold decStack frameBytes privStack at *; omega_using [hn])

theorem ret_subD (s : State) : Region.Sub (below (fb s) 16) (stkD s) := below_subD s (by decide)

theorem fb_toNatD {s : State} (hp : DPre s) : (fb s).toNat + frameBytes = (s.gpr .rsp).toNat := by
  have := hp.sp1; unfold decStack privStack at this
  simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold frameBytes at *; omega_using [this]

theorem DPre.hsl {s : State} (hp : DPre s) : 16 * (s.gpr .r8).toNat + 32 + 1024 ≤ (stackArg s 16).toNat := by
  have := hp.hsw; unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at this; omega_using [this]

theorem DPre.geo {s : State} (hp : DPre s) : Geo (fb s) (stackArg s 15) := by
  obtain hF := fb_toNatD hp
  have := hp.sp2
  have hsl := hp.hsl
  have wS := hp.wS
  obtain sS : Region.Sub ⟨stackArg s 15, oRsa⟩ (scrD s) := Region.sub_prefix (by unfold oRsa; omega_using [hsl])
  refine ⟨by unfold frameBytes at *; omega_using [hF, this], by unfold oRsa; omega_using [hsl, wS],
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
theorem arg_readD {s : State} (hp : DPre s) {m : Mem} (hf : Frame [frR s] s.mem m) {j : Nat} (hj : j < 19) :
    m.readW (off (fb s) (frameBytes + 8 + 8 * j)) 64 = stackArg s j := by
  rw [argAddr]
  refine hf.readW (r := ⟨stackArgAddr s 0, 152⟩) ?_ (fun r' hr' => ?_) (by decide)
  · rw [stackArgAddr_j s j]
    exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])
  · simp only [List.mem_singleton] at hr'; subst hr'
    exact (hp.dKa.sub_left (frame_subD s)).symm

/-- A stack argument is in a region the caller reads. -/
theorem DPre.argIn {s u : State} (hp : DPre s) (hrd : u.rd = s.rd) {j : Nat} (hj : j < 19) :
    InRegions (u.rd ++ u.wr) (stackArgAddr s j) 8 := by
  obtain ⟨A, hA, hm⟩ := hp.hra
  refine ⟨_, List.mem_append_left _ (by rw [hrd]; exact hm), ?_⟩
  show (stackArgAddr s j - stackArgAddr s 0).toNat + 8 ≤ A
  rw [stackArgAddr_j s j, BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat]; omega_using [hj, hA]

/-- One stack argument copied to a slot. -/
theorem copy1D_ok {s : State} (hp : DPre s) {u : State} (hsp : u.gpr .rsp = fb s) (hfr : frR s ∈ u.wr)
    (hrd : u.rd = s.rd) (hf : Frame [frR s] s.mem u.mem) {j d : Nat} (hj : j < 19) (hd : d + 8 ≤ frameBytes) :
    WP isa (.block (argSlot j d)) u fun u' => Keep [.rax] u u' ∧
      u'.mem = u.mem.writeW (off (fb s) d) (stackArg s j) ∧ Frame [frR s] s.mem u'.mem := by
  obtain hF := fb_toNatD hp
  have := hp.sp2
  obtain hsc : Scr u (fb s) frameBytes := Scr.of_mem hfr (by unfold frameBytes at *; omega_using [hF])
  obtain hin : InRegions (u.rd ++ u.wr) (off (fb s) (frameBytes + 8 + 8 * j)) 8 := by
    rw [argAddr]; exact hp.argIn hrd hj
  refine WP.mono (WP.keep [.rax] (Q := fun u' => u'.mem = u.mem.writeW (off (fb s) d) (stackArg s j)) ?_ rfl)
    fun u' ⟨hm, k⟩ => ⟨k, hm, hm ▸ hf.writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega_using [hd]) (by unfold frameBytes at *; omega_using [hd]))⟩
  xrun [argSlot, arg, ea_sp, hsp, hin, arg_readD hp hf hj, hsc.st (d := d) hd]

theorem frame_wD {s : State} (hp : DPre s) {m m' : Mem} (hf : Frame [frR s] m m') {d : Nat}
    (hd : d + 8 ≤ frameBytes) (v : BitVec 64) : Frame [frR s] m (m'.writeW (off (fb s) d) v) := by
  obtain hF := fb_toNatD hp
  have := hp.sp2
  exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_using [hd]) (by unfold frameBytes at *; omega_using [hd]))

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
  obtain hF := fb_toNatD hp
  have := hp.sp2
  have G' := hp.geo
  have hsp : (allocState frameBytes s).gpr .rsp = fb s := rfl
  obtain hfr : frR s ∈ (allocState frameBytes s).wr := List.mem_cons_self ..
  obtain hsc : Scr (allocState frameBytes s) (fb s) frameBytes := Scr.of_mem hfr (by unfold frameBytes at *; omega_using [hF])
  obtain R0 : Rep s.mem (fb s) (stackArg s 15) (fun o => s.mem (off (stackArg s 15) o))
      (fun k => word s.mem (fb s) (8 * k)) := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  rw [decPrologue_eq, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff,
    WP.block_append_iff]
  obtain R1 := ((((R0.wf G' (k := 21) (by decide) (s.gpr .rdi)).wf G' (k := 29) (by decide) (s.gpr .rdx)).wf G'
    (k := 22) (by decide) (s.gpr .rcx)).wf G' (k := 23) (by decide) (s.gpr .r8)).wf G' (k := 24) (by decide)
    (s.gpr .r9)
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = ((((s.mem.writeW (off (fb s) (8 * 21)) (s.gpr .rdi)).writeW
      (off (fb s) (8 * 29)) (s.gpr .rdx)).writeW (off (fb s) (8 * 22)) (s.gpr .rcx)).writeW (off (fb s) (8 * 23))
      (s.gpr .r8)).writeW (off (fb s) (8 * 24)) (s.gpr .r9)) ?_ rfl) fun t1 ⟨hm1, k1⟩ => ?_
  · xrun [ea_sp, hsp, hsc.st (d := sOut) (by decide), hsc.st (d := sMl) (by decide), hsc.st (d := sN) (by decide),
      hsc.st (d := sK) (by decide), hsc.st (d := sE) (by decide), allocState_gpr']
    rfl
  obtain f1 : Frame [frR s] s.mem t1.mem := by
    rw [hm1]
    exact frame_wD hp (frame_wD hp (frame_wD hp (frame_wD hp (frame_wD hp (Frame.refl _ _) (by decide) _)
      (by decide) _) (by decide) _) (by decide) _) (by decide) _
  obtain sp1 : t1.gpr .rsp = fb s := k1.gpr (by decide)
  obtain hfr1 : frR s ∈ t1.wr := k1.2.2 ▸ hfr
  refine WP.mono (copy1D_ok hp sp1 hfr1 k1.2.1 f1 (j := 0) (d := sEl) (by decide) (by decide))
    fun t2 ⟨k2, hm2, f2⟩ => ?_
  refine WP.mono (copy1D_ok hp ((k2.gpr (by decide)).trans sp1) (k2.2.2 ▸ hfr1) (k2.2.1.trans k1.2.1) f2
    (j := 11) (d := sLab) (by decide) (by decide)) fun t3 ⟨k3, hm3, f3⟩ => ?_
  obtain k23 := k2.trans k3
  refine WP.mono (copy1D_ok hp ((k23.gpr (by decide)).trans sp1) (k23.2.2 ▸ hfr1) (k23.2.1.trans k1.2.1) f3
    (j := 12) (d := sLabLen) (by decide) (by decide)) fun t4 ⟨k4, hm4, f4⟩ => ?_
  obtain k24 := k23.trans k4
  refine WP.mono (copy1D_ok hp ((k24.gpr (by decide)).trans sp1) (k24.2.2 ▸ hfr1) (k24.2.1.trans k1.2.1) f4
    (j := 15) (d := sScr) (by decide) (by decide)) fun t5 ⟨k5, hm5, f5⟩ => ?_
  obtain k25 := k24.trans k5
  refine WP.mono (copy1D_ok hp ((k25.gpr (by decide)).trans sp1) (k25.2.2 ▸ hfr1) (k25.2.1.trans k1.2.1) f5
    (j := 16) (d := sScrLen) (by decide) (by decide)) fun t6 ⟨k6, hm6, f6⟩ => ?_
  obtain k16 : Keep [.rax] (allocState frameBytes s) t6 := (k1.trans (k25.trans k6)).mono (by decide)
  obtain R6 : Rep t6.mem (fb s) (stackArg s 15) (fun o => s.mem (off (stackArg s 15) o)) (decW s) := by
    rw [hm6, hm5, hm4, hm3, hm2, hm1]
    exact ((((R1.wf G' (k := 25) (by decide) (stackArg s 0)).wf G' (k := 27) (by decide) (stackArg s 11)).wf G'
      (k := 28) (by decide) (stackArg s 12)).wf G' (k := 14) (by decide) (stackArg s 15)).wf G' (k := 26)
      (by decide) (stackArg s 16)
  have := hp.sp1
  refine ⟨k16, ⟨(k16.gpr (by decide)).trans hsp, k16.2.2 ▸ hfr, ?_, ?_, ?_, ?_, G'.dFS, G'.dRS⟩, R6, f6⟩
  · unfold decStack privStack at this; unfold frameBytes at *; omega_using [hF, this]
  · unfold frameBytes at *; omega_arith
  · have hsl := hp.hsl
    have hk := hp.lv.1
    refine ⟨⟨stackArg s 15, 0, (stackArg s 16).toNat * 8, by rw [k16.2.2]; simp [allocState, hp.hwr],
      (BitVec.add_zero _).symm, by unfold oRsa; omega_using [hsl], hp.wS.trans' (by omega_using [])⟩, G'.Sw⟩
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
    (hf : Frame [frR s] s.mem u.mem) (hfr : frR s ∈ u.wr) {j k : Nat} (hj : j < 19) (hk : k < 14) :
    WP isa (.block (argSlot j (8 * k))) u fun u' => Keep [.rax] u u' ∧ Lay u' (fb s) (stackArg s 15) ∧
      Rep u'.mem (fb s) (stackArg s 15) V (upd W k (stackArg s j)) ∧ Frame [frR s] s.mem u'.mem ∧
      u'.rd = s.rd ∧ frR s ∈ u'.wr :=
  WP.mono (copy1D_ok hp L.rsp hfr hrd hf hj (d := 8 * k) (by unfold frameBytes; omega_using [hk]))
    fun u' ⟨k', hm, f'⟩ =>
      have R' : Rep u'.mem (fb s) (stackArg s 15) V (upd W k (stackArg s j)) := hm ▸ R.wf L.geo (by
        unfold nW frameBytes; omega_using [hk]) _
      ⟨k', L.of_rep' R R' (by simp only [upd]; rw [ifn (by omega_using [hk])]) (k'.gpr (by decide)) k'.2.2, R', f',
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

/-- At the private-key operation's call, with the frame's words `W`, whose
first 14 are its stack arguments. -/
structure DCall (s : State) (W : Nat → BitVec 64) (t : State) : Prop where
  he : EnvD s t
  R : Rep t.mem (fb s) (stackArg s 15) (fun o => s.mem (off (stackArg s 15) o)) W
  hW : ∀ i < 14, W i = privW s i
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
  obtain hs1 := R1.slot (d := sK) (k := 23) rfl (by decide) (v := s.gpr .r8) (by simp [upd, decW])
  refine WP.mono (WP.keep [.rax] (Q := fun u => u.mem = t1.mem.writeW (off (fb s) (8 * 1)) (s.gpr .r8)) ?_ rfl)
    fun t2 ⟨hm2, k2⟩ => ?_
  · xrun [ea_sp, L1.rsp, L1.ld (d := sK) (by decide), hs1, L1.st (d := 8) (by decide)]
  obtain R2 : Rep t2.mem (fb s) (stackArg s 15) _ _ := hm2 ▸ R1.wf G' (k := 1) (by decide) (s.gpr .r8)
  obtain L2 := L1.of_rep' R1 R2 (by simp [upd]) (k2.gpr (by decide)) k2.2.2
  obtain f2 : Frame [frR s] s.mem t2.mem := hm2 ▸ frame_wD hp f1 (d := 8) (by decide) _
  obtain rd2 : t2.rd = s.rd := k2.2.1.trans rd1
  obtain fr2 : frR s ∈ t2.wr := k2.2.2 ▸ fr1
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
  simp only [Bignum.word] at hs
  obtain kk := (((((((((((k1.trans k2).trans k3).trans k4).trans k5).trans k6).trans k7).trans k8).trans k9).trans
    k10).trans k11).trans k12)
  refine WP.mono (WP.keep [.rax] (Q := fun u' => u'.mem =
      t12.mem.writeW (off (fb s) (8 * 12)) (off (stackArg s 15) oRsa)) ?_ rfl) fun t13 ⟨hm13, k13⟩ => ?_
  · xrun [scr, Impl.Mgf1.X86_64.scr, lay, List.cons_append, List.nil_append, ea_sp, L12.rsp,
      L12.ld (d := sScr) (by decide), hs, L12.st (d := 96) (by decide),
      VG.Proof.MlKem.X86_64.sx_ofNat (show oRsa < 2 ^ 31 by decide)]
  obtain R13 : Rep t13.mem (fb s) (stackArg s 15) V _ := hm13 ▸ R12.wf G' (k := 12) (by decide) (off (stackArg s 15) oRsa)
  obtain L13 := L12.of_rep' R12 R13 (by simp [upd]) (k13.gpr (by decide)) k13.2.2
  refine WP.mono (WP.keep [.rax] (Q := fun u' => u'.mem =
      t13.mem.writeW (off (fb s) (8 * 13)) (stackArg s 16 - 1024)) ?_ rfl) fun t14 ⟨hm14, k14⟩ => ?_
  · xrun [ea_sp, L13.rsp, L13.ld (d := sScrLen) (by decide), L13.st (d := 104) (by decide),
      R13.slot (d := sScrLen) (k := 26) rfl (by decide) (v := stackArg s 16) (by simp [upd, decW]),
      show BitVec.signExtend 64 (1024 : BitVec 32) = 1024 from by decide]
  obtain R14 : Rep t14.mem (fb s) (stackArg s 15) V (privW s) := hm14 ▸ R13.wf G' (k := 13) (by decide) _
  obtain L14 := L13.of_rep' R13 R14 (by simp [upd, privW]) (k14.gpr (by decide)) k14.2.2
  have hs' := L14.slot
  simp only [Bignum.word] at hs'
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
  obtain Ru : Rep u'.mem (fb s) (stackArg s 15) V (privW s) := by rw [hm]; exact R14
  exact ⟨(kk.trans (k13.trans (k14.trans k'))).mono (by decide),
    L14.of_rep' R14 Ru rfl (k'.gpr (by decide)) k'.2.2, Ru,
    by rw [hm, hm14, hm13]; exact frame_wD hp (frame_wD hp f12 (d := 96) (by decide) _) (d := 104) (by decide) _,
    h1, h2, h3, h4, h5, h6⟩

theorem decHead_ok {s : State} (hp : DPre s) :
    WP isa (.block (decPrologue ++ privArgs)) (allocState frameBytes s) (DSet s) := by
  rw [WP.block_append_iff]
  refine WP.mono (wp_good (block_good _ rfl) (decPro_ok hp)) fun t0 ⟨⟨k0, L0, R0, f0⟩, sp0, mx0, _⟩ => ?_
  obtain hfr0 : frR s ∈ t0.wr := by rw [k0.2.2]; exact List.mem_cons_self ..
  refine WP.mono (wp_good (block_good _ rfl) (privArgs_ok hp L0 R0 k0.2.1 f0 hfr0)) fun t ⟨⟨k, L, R, f, h1, h2, h3, h4, h5, h6⟩, sp, mx, _⟩ => ?_
  refine ⟨⟨L.rsp, k.2.1.trans k0.2.1, k.2.2.trans (k0.2.2.trans hp.wr), fun r hr h => ?_, by rw [mx, mx0]; rfl,
    f.sub fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., frame_subD s⟩⟩,
    L, R, h1, h2, h3, h4, h5, h6⟩
  rw [k.gpr (cs_disj _ (by decide) r hr), k0.gpr (cs_disj [.rax] (by decide) r hr)]
  show (if r = .rsp then _ else s.gpr r) = s.gpr r
  simp only [h, ↓reduceIte]

end VG.Proof.RsaOaep.X86_64

end

end

/-! ### `RsaOaep.X86_64.DecTab`, which this module and modules that import it used -/

section

/-!
# RSAES-OAEP decryption on x86-64: MGF1's table

From a state in the frame (`EnvD`) naming the entry state's addresses of
statics, the tables that the stack arguments 17 (the label's hash
function's) and 18 (MGF1's) point to as the code that calls their functions
needs them (`Table.Tab`): readable, and with their words and those arguments
in every memory the code may leave, since the tables and the stack arguments
are apart from everything it writes (`dtabL`, `dtab`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64.Table (Fns)
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)
open VG.Proof.RsaOaep.X86_64.Table (Tab TabOK TabMem)

/-- A word of a region apart from what the code writes, in memory it may
leave. -/
theorem FrD.readW' {s : State} {m : Mem} (h : FrD s m) {r : Region} {a : Addr}
    (hc : r.Contains a 8) (hk : (stkD s).Disjoint r) (ho : (outR s).Disjoint r) (hm : (mlR s).Disjoint r)
    (hs : (scrD s).Disjoint r) : m.readW a 64 = s.mem.readW a 64 :=
  Frame.readW h hc (fun r' hr' => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl
    · exact hk.symm
    · exact ho.symm
    · exact hm.symm
    · exact hs.symm) (by decide)

/-- The table at the stack argument `j`, from the entry state's. -/
theorem dtabJ {s t : State} (hp : DPre s) (he : EnvD s t) (hsy : t.syms = s.syms) {G : Stream} {f : Fns}
    {j : Nat} (hj : j < 19) (hT : (⟨stackArg s j, 88⟩ : Region) ∈ s.rd) (wT : (stackArg s j).toNat + 88 ≤ 2 ^ 64)
    (dK : (stkD s).Disjoint ⟨stackArg s j, 88⟩) (dO : (outR s).Disjoint ⟨stackArg s j, 88⟩)
    (dM : (mlR s).Disjoint ⟨stackArg s j, 88⟩) (dS : (scrD s).Disjoint ⟨stackArg s j, 88⟩)
    (ok : TabOK G f s.syms) (hm : TabMem G s.syms (stackArg s j) s.mem)
    (hD : s.mem.readW (off (stackArg s j) 48) 64 = BitVec.ofNat 64 G.D) :
    Tab G f (fb s) (stackArg s j) (frameBytes + 8 + 8 * j) t := by
  have hsp := hp.sp2
  have hT' : (⟨stackArg s j, 88⟩ : Region) ∈ t.rd := by rw [he.rd]; exact hT
  have cT : ∀ d, d + 8 ≤ 88 → (⟨stackArg s j, 88⟩ : Region).Contains (off (stackArg s j) d) 8 := fun d hd =>
    Offset.contains_base _ hd (by have := wT; omega_using [hd])
  have cA : (⟨stackArgAddr s 0, 152⟩ : Region).Contains (off (fb s) (frameBytes + 8 + 8 * j)) 8 := by
    rw [argAddr, stackArgAddr_j s j]
    exact Offset.contains_base _ (by omega_using [hj]) (by have := hp.sp2; omega_using [hj])
  refine ⟨by rw [hsy]; exact ok, fun i hi => ⟨_, List.mem_append_left _ hT', cT _ (by omega_using [hi])⟩,
    ⟨_, List.mem_append_left _ hT', cT 48 (by omega_using [])⟩, by rw [argAddr]; exact hp.argIn he.rd hj, fun m hf => ?_⟩
  have hF : FrD s m := FrD.step he.fr he.wr hf
  have rt : ∀ d, d + 8 ≤ 88 → m.readW (off (stackArg s j) d) 64 = s.mem.readW (off (stackArg s j) d) 64 :=
    fun d hd => hF.readW' (cT d hd) dK dO dM dS
  rw [hsy]
  refine ⟨⟨(rt _ (by omega_using [])).trans hm.1, (rt _ (by omega_using [])).trans hm.2.1, (rt _ (by omega_using [])).trans hm.2.2⟩,
    (rt 48 (by omega_using [])).trans hD, ?_⟩
  rw [hF.readW' cA hp.dKa hp.dOa hp.dMa hp.dsa, argAddr]
  rfl

/-- MGF1's table, from the entry state's. -/
theorem dtab {s t : State} (hp : DPre s) (he : EnvD s t) (hsy : t.syms = s.syms) {G : Stream} {f : Fns}
    (ok : TabOK G f s.syms) (hm : TabMem G s.syms (stackArg s 18) s.mem)
    (hD : s.mem.readW (off (stackArg s 18) 48) 64 = BitVec.ofNat 64 G.D) :
    Tab G f (fb s) (stackArg s 18) (frameBytes + 8 + 8 * 18) t :=
  dtabJ hp he hsy (by decide) (hp.hrd _ (by simp [tabR])) hp.wT hp.dKt hp.dOt hp.dMt hp.dst ok hm hD

/-- The table of the label's hash function, from the entry state's. -/
theorem dtabL {s t : State} (hp : DPre s) (he : EnvD s t) (hsy : t.syms = s.syms) {G : Stream} {f : Fns}
    (ok : TabOK G f s.syms) (hm : TabMem G s.syms (stackArg s 17) s.mem)
    (hD : s.mem.readW (off (stackArg s 17) 48) 64 = BitVec.ofNat 64 G.D) :
    Tab G f (fb s) (stackArg s 17) (frameBytes + 8 + 8 * 17) t :=
  dtabJ hp he hsy (by decide) (hp.hrd _ (by simp [tabL])) hp.wTL hp.dKtL hp.dOtL hp.dMtL hp.dstL ok hm hD

end VG.Proof.RsaOaep.X86_64

end

end

/-! ### `RsaOaep.X86_64.DecOut`, which only this module used -/

section

/-!
# RSAES-OAEP decryption on x86-64: the outputs

The mask `ok` (`okMask_ok`), the buffer ANDed with it to `out`
(`outLoop_ok`), the length and the result (`decRet_ok`), and the failure
before decoding (`decFail_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp ix at_ step byteLoop)
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Bignum (off word off_off)
open VG.Proof.Bignum.X86_64 (Scr)
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)

/-- `ok`: all ones iff the private-key operation's result `r` (word 30) is 1
and the accumulator (word 31) is zero. -/
def okW (W : Nat → BitVec 64) : BitVec 64 := zM (W 30 ^^^ 1) &&& zM (W 31)

theorem okMask_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) :
    WP isa (.block okMask) u fun u' => Lay u' F S ∧ Keep [.rax, .r11] u u' ∧ u'.gpr .r11 = okW W ∧
      Rep u'.mem F S V (upd W 33 (okW W)) := by
  have G' := L.geo
  refine WP.mono (WP.keep [.rax, .r11] (Q := fun u' => u'.gpr .r11 = okW W ∧
    u'.mem = u.mem.writeW (off F (8 * 33)) (okW W)) ?_ rfl) fun u' ⟨⟨h11, hm⟩, k⟩ => ?_
  · xrun [okMask, ea_sp, L.rsp, L.ld (d := sR) (by decide), L.ld (d := sAcc) (by decide), L.st (d := sOk) (by decide),
      R.slot (d := sR) (k := 30) rfl (by decide) rfl, R.slot (d := sAcc) (k := 31) rfl (by decide) rfl,
      sbb_zM, sbb0_zM, okW]
    exact ⟨BitVec.and_comm _ _, by rw [BitVec.and_comm]; rfl⟩
  obtain R' : Rep u'.mem F S V (upd W 33 (okW W)) := hm ▸ R.wf G' (k := 33) (by decide) _
  exact ⟨L.of_rep' R R' (by simp [upd]) (k.gpr (by decide)) k.2.2, k, h11, R'⟩

/-! ## `out` -/

/-- A byte of the buffer ANDed with the mask `m`. -/
def andB (b : Byte) (m : BitVec 64) : Byte := BitVec.setWidth 8 (BitVec.setWidth 64 b &&& m)

structure OutI (u₀ : State) (F S : Addr) (V : Nat → Byte) (W : Nat → BitVec 64) (o : Addr) (k : Nat)
    (m : BitVec 64) (j : Nat) (v : State) : Prop where
  L : Lay v F S
  keep : Keep [.rax, .r8] u₀ v
  r8 : v.gpr .r8 = BitVec.ofNat 64 j
  R : Rep v.mem F S V W
  fr : Frame [⟨o, k⟩] u₀.mem v.mem
  out : ∀ i < j, v.mem (o + BitVec.ofNat 64 i) = andB (V (oBuf + i)) m

/-- The buffer's first `k` bytes, ANDed with `ok` (word 33), to `out` (word
21), a region apart from the frame, our working space and the stack below
the frame. -/
theorem outLoop_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {o : Addr} {k : Nat} (ho : W 21 = o) (hk : W 23 = BitVec.ofNat 64 k) (hk0 : 0 < k)
    (hk1 : k ≤ 1024) (hw : (⟨o, k⟩ : Region) ∈ u.wr) (hnw : o.toNat + k ≤ 2 ^ 64) (ha : Apart F S ⟨o, k⟩) :
    WP isa outLoop u fun u' => Lay u' F S ∧ Keep [.rdi, .rcx, .r10, .r11, .r8, .rax] u u' ∧ Rep u'.mem F S V W ∧
      (∀ i < k, u'.mem (o + BitVec.ofNat 64 i) = andB (V (oBuf + i)) (W 33)) ∧ Frame [⟨o, k⟩] u.mem u'.mem := by
  have hs := L.slot
  simp only [Bignum.word] at hs
  have c3 : oBuf = 1024 := rfl
  unfold outLoop
  refine WP.seq (WP.mono (WP.keep [.rdi, .rcx, .r10, .r11, .r8] (Q := fun v => v.gpr .rdi = o ∧
      v.gpr .rcx = off S oBuf ∧ v.gpr .r10 = BitVec.ofNat 64 k ∧ v.gpr .r11 = W 33 ∧
      v.gpr .r8 = BitVec.ofNat 64 0 ∧ v.mem = u.mem) ?_ rfl) fun v ⟨⟨h₁, h₂, h₃, h₄, h₅, hm⟩, hk'⟩ => ?_)
  · xrun [scr, Impl.Mgf1.X86_64.scr, lay, List.cons_append, List.nil_append, ea_sp, L.rsp,
      L.ld (d := sOut) (by decide), L.ld (d := sScr) (by decide), L.ld (d := sK) (by decide),
      L.ld (d := sOk) (by decide), hs, R.slot (d := sOut) (k := 21) rfl (by decide) ho,
      R.slot (d := sK) (k := 23) rfl (by decide) hk, R.slot (d := sOk) (k := 33) rfl (by decide) rfl,
      VG.Proof.MlKem.X86_64.sx_ofNat (show oBuf < 2 ^ 31 by decide)]
  obtain Lv : Lay v F S := L.congr (hk'.gpr (by decide)) hk'.2.2 (by rw [hm])
  obtain hsc : Scr v o k := Scr.of_mem (by rw [hk'.2.2]; exact hw) hnw
  refine WP.mono (byteLoop_ok hk0 (stepR_ok (by omega_using [hk1]) v (show Reg.r10 ∉ [Reg.rax, .r8] by decide) (by decide) h₃)
    (OutI v F S V W o k (W 33)) ?_ ⟨Lv, Keep.refl _ _, h₅, hm ▸ R, Frame.refl _ _,
      fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun w I => ?_
  · intro j hj w I
    obtain hdw : w.gpr .rdi = o := (I.keep.gpr (by decide)).trans h₁
    obtain hcw : w.gpr .rcx = off S oBuf := (I.keep.gpr (by decide)).trans h₂
    obtain h11w : w.gpr .r11 = W 33 := (I.keep.gpr (by decide)).trans h₄
    obtain hst : InRegions w.wr (o + BitVec.ofNat 64 j) 1 := by
      have := hsc.st8 (d := j) (by omega_using [hj]); rw [I.keep.2.2]; exact this
    obtain vb : w.mem (off S (oBuf + j)) = V (oBuf + j) := I.R.scr _ (by unfold oRsa; omega_using [hk1, c3, hj])
    refine WP.mono (WP.keep [.rax] (Q := fun w' => w'.gpr .r8 = BitVec.ofNat 64 j ∧
        w'.mem = w.mem.writeW (o + BitVec.ofNat 64 j) (andB (V (oBuf + j)) (W 33))) ?_ rfl)
      fun w' ⟨⟨h8', hm'⟩, k'⟩ => ⟨(I.keep.trans k').mono (by decide), h8', fun w'' k'' hm'' h8'' => ?_⟩
    · xrun [ea_ix0, ea_ix, hdw, hcw, h11w, I.r8, off_plus, I.L.sld8 (d := oBuf + j) (by unfold oRsa; omega_using [hk1, c3, hj]), vb,
        show o + BitVec.ofNat 64 j + BitVec.ofNat 64 0 = o + BitVec.ofNat 64 j from BitVec.add_zero _, hst, andB]
    · have fw : Frame [⟨o, k⟩] w.mem w''.mem := by
        rw [hm'', hm']
        exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_using [hj]) (by omega_using [hk1, hj]))
      refine ⟨I.L.of_rep I.R (Rep.apart I.R ha fw) (by rw [k''.gpr (by decide), k'.gpr (by decide)])
          (k''.2.2.trans k'.2.2), (I.keep.trans (k'.trans k'')).mono (by decide), h8'', Rep.apart I.R ha fw,
        I.fr.trans fw, fun i hi => ?_⟩
      rw [hm'', hm', VG.WriteBytes.writeW8_apply]
      by_cases h : i = j
      · subst h; simp
      · rw [ifn (Offset.add_ofNat_ne o (by omega_using [hk1, hj, hi]) (by omega_using [hk1, hj]) h), I.out i (by omega_using [hi, h])]
  · have fr : Frame [⟨o, k⟩] u.mem w.mem := by rw [← hm]; exact I.fr
    exact ⟨I.L, (hk'.trans I.keep).mono (by decide), I.R, I.out, fr⟩

/-! ## The length and the result -/

/-- `(r = 2) ? 2 : 0`, from word 30. -/
def faultW (W : Nat → BitVec 64) : BitVec 64 := zM (W 30 ^^^ 2) &&& 2

theorem faultBit_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) :
    WP isa (.block faultBit) u fun u' => Keep [.rax] u u' ∧ u'.mem = u.mem ∧ u'.gpr .rax = faultW W := by
  refine WP.mono (WP.keep [.rax] (Q := fun u' => u'.mem = u.mem ∧ u'.gpr .rax = faultW W) ?_ rfl)
    fun u' ⟨⟨hm, h⟩, k⟩ => ⟨k, hm, h⟩
  xrun [faultBit, ea_sp, L.rsp, L.ld (d := sR) (by decide), R.slot (d := sR) (k := 30) rfl (by decide) rfl,
    sbb_zM, sbb0_zM, faultW]

/-- The length to `*msg_len`, a region apart from the frame, our working
space and the stack below it. -/
theorem decRet_ok {Hm : Stream} {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {pm : Addr} {k : Nat} (hpm : W 29 = pm) (hk : W 23 = BitVec.ofNat 64 k)
    (hkD : 2 * Hm.D + 2 ≤ k) (hD64 : Hm.D ≤ 64) (hw : (⟨pm, 8⟩ : Region) ∈ u.wr)
    (hnw : pm.toNat + 8 ≤ 2 ^ 64) (ha : Apart F S ⟨pm, 8⟩) :
    WP isa (.block (decRet Hm)) u fun u' => Keep [.r11, .rax, .rdi] u u' ∧
      u'.mem = u.mem.writeW pm ((BitVec.ofNat 64 (k - (2 * Hm.D + 2)) - W 32) &&& W 33) ∧
      u'.gpr .rax = faultW W ||| (W 33 &&& 1) := by
  obtain hst : InRegions u.wr pm 8 := by
    have := (Scr.of_mem hw hnw).st (d := 0) (by decide)
    rwa [show off pm 0 = pm from BitVec.add_zero _] at this
  rw [show decRet Hm = [.mov .r11 (.mem (sp sOk)), .mov .rax (.mem (sp sK)), .alu .sub .rax (im (2 * Hm.D + 2)),
      .alu .sub .rax (.mem (sp sIdx)), .alu .and .rax (.reg .r11), .mov .rdi (.mem (sp sMl)),
      .store (at_ .rdi) .rax] ++ (([.alu .and .r11 (.imm 1)] : List Instr) ++ faultBit ++
      ([.alu .or .rax (.reg .r11)] : List Instr)) from rfl, WP.block_append_iff]
  refine WP.mono (WP.keep [.r11, .rax, .rdi] (Q := fun v => v.gpr .r11 = W 33 ∧
      v.mem = u.mem.writeW pm ((BitVec.ofNat 64 (k - (2 * Hm.D + 2)) - W 32) &&& W 33)) ?_ rfl)
    fun v ⟨⟨h11, hm⟩, kv⟩ => ?_
  · xrun [im, ea_sp, ea_at0, L.rsp, L.ld (d := sOk) (by decide), L.ld (d := sK) (by decide),
      L.ld (d := sIdx) (by decide), L.ld (d := sMl) (by decide), hst,
      R.slot (d := sOk) (k := 33) rfl (by decide) rfl, R.slot (d := sK) (k := 23) rfl (by decide) hk,
      R.slot (d := sIdx) (k := 32) rfl (by decide) rfl, R.slot (d := sMl) (k := 29) rfl (by decide) hpm,
      VG.Proof.MlKem.X86_64.sx_ofNat (show 2 * Hm.D + 2 < 2 ^ 31 by omega_using [hD64]),
      VG.Offset.ofNat_sub_ofNat (show 2 * Hm.D + 2 ≤ k by omega_using [hkD])]
  obtain fv : Frame [⟨pm, 8⟩] u.mem v.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain Rv := Rep.apart R ha fv
  obtain Lv : Lay v F S := L.of_rep R Rv (kv.gpr (by decide)) kv.2.2
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.r11] (Q := fun x => x.gpr .r11 = W 33 &&& 1 ∧ x.mem = v.mem) ?_ rfl)
    fun x ⟨⟨h11x, hmx⟩, kx⟩ => ?_
  · xrun [h11]
  obtain Lx : Lay x F S := Lv.congr (kx.gpr (by decide)) kx.2.2 (by rw [hmx])
  refine WP.mono (faultBit_ok Lx (hmx ▸ Rv)) fun y ⟨ky, hmy, hay⟩ => ?_
  refine WP.mono (WP.keep [.rax] (Q := fun z => z.gpr .rax = faultW W ||| (W 33 &&& 1) ∧ z.mem = y.mem) ?_ rfl)
    fun z ⟨⟨haz, hmz⟩, kz⟩ => ⟨(((kv.trans kx).trans ky).trans kz).mono (by decide), by rw [hmz, hmy, hmx, hm], haz⟩
  xrun [hay, ky.gpr (show Reg.r11 ∉ [Reg.rax] by decide), h11x]

/-- The failure before decoding: zeros to `out` and `*msg_len`, and
`(r = 2) ? 2 : 0`. -/
theorem decFail_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {o pm : Addr} {k : Nat} (ho : W 21 = o) (hpm : W 29 = pm)
    (hk : W 23 = BitVec.ofNat 64 k) (hk0 : 0 < k) (hk1 : k ≤ 1024) (hw : (⟨o, k⟩ : Region) ∈ u.wr)
    (hnw : o.toNat + k ≤ 2 ^ 64) (ha : Apart F S ⟨o, k⟩) (hwm : (⟨pm, 8⟩ : Region) ∈ u.wr)
    (hnm : pm.toNat + 8 ≤ 2 ^ 64) (ham : Apart F S ⟨pm, 8⟩) (hom : Region.Disjoint ⟨o, k⟩ ⟨pm, 8⟩) :
    WP isa decFail u fun u' => Lay u' F S ∧ Keep [.rdi, .r10, .rax, .r8] u u' ∧ Rep u'.mem F S V W ∧
      Spec.Rsa.bytesAt u'.mem o k = List.replicate k 0 ∧ u'.mem.readW pm 64 = 0 ∧
      Frame [⟨o, k⟩, ⟨pm, 8⟩] u.mem u'.mem ∧ u'.gpr .rax = faultW W := by
  unfold decFail
  refine WP.seq (WP.mono (zeroOut_ok L R ho hk hk0 hk1 hw hnw ha) fun t1 ⟨L1, k1, R1, hax1, hz1, f1⟩ => ?_)
  obtain hst : InRegions t1.wr pm 8 := by
    have := (Scr.of_mem (by rw [k1.2.2]; exact hwm) hnm).st (d := 0) (by decide)
    rwa [show off pm 0 = pm from BitVec.add_zero _] at this
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rdi] (Q := fun v => v.mem = t1.mem.writeW pm (0#64)) ?_ rfl) fun v ⟨hm, kv⟩ => ?_
  · xrun [ea_sp, ea_at0, L1.rsp, L1.ld (d := sMl) (by decide), hst, hax1,
      R1.slot (d := sMl) (k := 29) rfl (by decide) hpm]
    rfl
  obtain fv : Frame [⟨pm, 8⟩] t1.mem v.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain Rv := Rep.apart R1 ham fv
  obtain Lv : Lay v F S := L1.of_rep R1 Rv (kv.gpr (by decide)) kv.2.2
  refine WP.mono (faultBit_ok Lv Rv) fun y ⟨ky, hmy, hay⟩ => ?_
  obtain hmy' : y.mem = t1.mem.writeW pm (0#64) := hmy.trans hm
  refine ⟨Lv.congr (ky.gpr (by decide)) ky.2.2 (by rw [hmy]), ((k1.trans kv).trans ky).mono (by decide),
    hmy ▸ Rv, ?_, by rw [hmy']; exact Mem.readW_writeW_self64 _ _ _, ?_, hay⟩
  · rw [← hz1]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    rw [hmy]
    exact fv.bytes (R := ⟨o, k⟩) (fun r hr => by rw [List.mem_singleton.mp hr]; exact hom) (show k ≤ 2 ^ 64 by omega_using [hk1])
      (List.mem_range.mp hi)
  · rw [hmy]
    exact (f1.sub fun r hr => ⟨r, by simp [List.mem_singleton.mp hr], fun _ h => h⟩).trans
      (fv.sub fun r hr => ⟨r, by simp [List.mem_singleton.mp hr], fun _ h => h⟩)

end VG.Proof.RsaOaep.X86_64

end

end


/-!
# RSAES-OAEP decryption on x86-64: the decoding

`decMain` (`decMain_ok`): from `EM` in our working space and the private-key
operation's result in its slot, the label's hash, the seed and `DB`
unmasked, `lHash'` compared, `T` scanned, copied and shifted, and the
message under the mask `ok` to `out`, its length to `*msg_len`: what
`Spec.RsaOaep.decrypt` writes for the operation's outcome.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp ix at_ step byteLoop seqs mgfXor)
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink)
open VG.Impl.Mgf1.X86_64.Table (Fns)

/-! ## The pieces that keep `rsp`, MXCSR and the stack -/

theorem accLh_good (H : Impl.Pbkdf2.Md.X86_64.Stream) : Good (accLh H) :=
  ⟨rfl, by simp [accLh, Code.depth, Impl.Mgf1.X86_64.byteLoop]⟩
theorem scan_good (H : Impl.Pbkdf2.Md.X86_64.Stream) : Good (scan H) :=
  ⟨rfl, by simp [scan, Code.depth, Impl.Mgf1.X86_64.byteLoop]⟩
theorem clearBuf_good (H : Impl.Pbkdf2.Md.X86_64.Stream) : Good (clearBuf H) := ⟨rfl, by simp [clearBuf, Code.depth]⟩
theorem copyT_good : Good copyT := ⟨rfl, by simp [copyT, Code.depth, Impl.Mgf1.X86_64.byteLoop]⟩
theorem shift_good : Good shift := ⟨rfl, by simp [shift, shiftPass, Code.depth, Impl.Mgf1.X86_64.byteLoop]⟩
theorem outLoop_good : Good outLoop := ⟨rfl, by simp [outLoop, Code.depth, Impl.Mgf1.X86_64.byteLoop]⟩
theorem decFail_good : Good decFail :=
  ⟨rfl, by simp [decFail, zeroOut, Code.depth, Impl.Mgf1.X86_64.byteLoop]⟩

/-! ## The argument slots -/

/-- The slots `decPrologue` stores to. -/
def decKs : List Nat := [14, 21, 22, 23, 24, 25, 26, 27, 28, 29]

/-- The argument slots, as the prologue stored them. -/
def ArgsD (s : State) (W : Nat → BitVec 64) : Prop := ∀ k ∈ decKs, W k = decW s k

theorem ArgsD.w {s : State} {W : Nat → BitVec 64} (h : ArgsD s W) :
    W 14 = stackArg s 15 ∧ W 21 = s.gpr .rdi ∧ W 22 = s.gpr .rcx ∧ W 23 = s.gpr .r8 ∧ W 24 = s.gpr .r9 ∧
    W 25 = stackArg s 0 ∧ W 26 = stackArg s 16 ∧ W 27 = stackArg s 11 ∧ W 28 = stackArg s 12 ∧
    W 29 = s.gpr .rdx := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (rw [h _ (by simp [decKs])]; simp [decW, upd])

theorem ArgsD.of {s : State} {W W' : Nat → BitVec 64} (h : ArgsD s W) (hW : ∀ k ∈ decKs, W' k = W k) :
    ArgsD s W' := fun k hk => (hW k hk).trans (h k hk)

/-! ## Bytes and masks -/

theorem andB_ones (b : Byte) : andB b (BitVec.allOnes 64) = b := by
  simp only [andB, BitVec.and_allOnes]; exact trunc_zext b

theorem andB_zero (b : Byte) : andB b 0 = 0 := by
  simp only [andB]; rw [show BitVec.setWidth 64 b &&& 0 = 0 from BitVec.and_zero]; rfl

/-! ## The outcome -/

/-- The result in its slot (word 30), and `EM` in our working space. -/
def ResD (V : Nat → Byte) (W : Nat → BitVec 64) (k : Nat) : Spec.Rsa.Outcome → Prop
  | .ok em => W 30 = 1 ∧ (List.range k).map (fun i => V (oEm + i)) = em
  | .invalid => W 30 = 0
  | .fault => W 30 = 2

variable {Hl Gm : Hash} (hH : HashOK Hl) (hG : HashOK Gm)
  (mH : MgfLink Hl hH) (mG : MgfLink Gm hG) {f : Fns} (hgi : Table.FnsGood f.init)
  (hgu : Table.FnsGood f.upd) (hgf : Table.FnsGood f.fin)

include hH hG mH mG hgi hgu hgf in
theorem decMain_ok {s t : State} (hp : DPre s) (he : EnvD s t) (hsy : t.syms = s.syms)
    (okL : Table.TabOK Hl.stream f s.syms) (hmL : Table.TabMem Hl.stream s.syms (stackArg s 17) s.mem)
    (hDmL : s.mem.readW (off (stackArg s 17) 48) 64 = BitVec.ofNat 64 Hl.D)
    (ok : Table.TabOK Gm.stream f s.syms) (hm : Table.TabMem Gm.stream s.syms (stackArg s 18) s.mem)
    (hDm : s.mem.readW (off (stackArg s 18) 48) 64 = BitVec.ofNat 64 Gm.D) (L : Lay t (fb s) (stackArg s 15))
    {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep t.mem (fb s) (stackArg s 15) V W) (hW : ArgsD s W)
    (h35 : W 35 = stackArg s 17)
    (hk : 2 * Hl.D + 2 ≤ (s.gpr .r8).toNat) {o : Spec.Rsa.Outcome} (hres : ResD V W (s.gpr .r8).toNat o) :
    WP isa (decMain Hl.stream f) t fun t' => EnvD s t' ∧
      Spec.RsaOaep.writtenDecrypt t'.mem (s.gpr .rdi) (s.gpr .rdx) (s.gpr .r8).toNat ((t'.gpr .rax).setWidth 32)
        (decOut mH.G mG.G (Spec.Rsa.bytesAt s.mem (stackArg s 11) (stackArg s 12).toNat) o) := by
  obtain ⟨w14, w21, w22, w23, w24, w25, w26, w27, w28, w29⟩ := hW.w
  obtain hk1 := hp.lv.1; have hk2 := hp.lv.2; have hsl := hp.hsl
  obtain hz := sizes hH.stream; have hzG := sizes hG.stream
  have hD := hH.hD0
  have hsD : Hl.stream.D = Hl.D := rfl
  have hgD : Gm.stream.D = Gm.D := rfl
  have c0 : oEm = 0 := rfl
  obtain w23' : W 23 = BitVec.ofNat 64 (s.gpr .r8).toNat := by rw [w23, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  unfold decMain seqs seqs seqs seqs seqs seqs seqs seqs seqs seqs seqs seqs
  -- The label's hash.
  obtain sS : Region.Sub ⟨stackArg s 15, oRsa⟩ (scrD s) := Region.sub_prefix (by unfold oRsa; omega_using [hsl])
  obtain A0 : LabAt t (fb s) (stackArg s 15) W (stackArg s 11) (stackArg s 12).toNat :=
    ⟨w27, by rw [w28, BitVec.ofNat_toNat, BitVec.setWidth_eq], (stackArg s 12).isLt,
      Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr, he.rd]; exact hp.hrd _ (by simp)),
      hp.dlbs.sub_right sS, hp.dKlb.sub_left (ret_subD s)⟩
  refine WP.seq (WP.mono_syms (wp_good (hashLabelT_good hgi hgu hgf oLh)
    (hashLabelT_ok hH.stream hgi hgu (Hs := mH.G) mH.hash (dtabL hp he hsy okL hmL hDmL) (Table.TJ.refl t _) rfl
      rfl L R h35 A0 (Or.inr rfl)))
    fun t1 ⟨⟨L1, rd1, wr1, cs1, V1, R1, hV1, hV1'⟩, sp1, mx1, f1⟩ sy1 => ?_)
  obtain he1 : EnvD s t1 := he.step rd1 wr1 sp1 (fun r hr _ => cs1 r hr) mx1 f1
  obtain hlab : Spec.Rsa.bytesAt t.mem (stackArg s 11) (stackArg s 12).toNat =
      Spec.Rsa.bytesAt s.mem (stackArg s 11) (stackArg s 12).toNat :=
    FrD.bytes he.fr hp.dKlb hp.dOlb hp.dMlb hp.dlbs.symm (by have := hp.wL; omega_using [])
  rw [hlab] at hV1'
  -- The seed unmasked.
  refine WP.seq (WP.mono_syms (wp_good (seedArgs_good _) (seedArgs_ok (H := Hl.stream) L1 R1 w23' (by omega_using [hz])
      (by omega_using [hk, hsD])))
    fun t2 ⟨⟨L2, k2, R2⟩, sp2, mx2, f2⟩ sy2 => ?_)
  obtain he2 : EnvD s t2 := he1.step k2.2.1 k2.2.2 sp2 (keep_cs3 k2 (by decide)) mx2 f2
  refine WP.seq (WP.mono_syms (wp_good (Table.mgfT_good hgi hgu hgf _) (Table.mgfXorT_ok hG.stream hgi hgu hgf
    mG.hash mG.len (valid_of_link hG mG) (dtab hp he2 (sy2.trans (sy1.trans hsy)) ok hm hDm)
        L2 R2 ⟨by unfold oEm oSt; omega_using [hk2, hz], by unfold oEm oSt; omega_using [hz], by omega_using [], by omega_using [hD, hsD], by omega_using [hz]⟩
    (mW_args _ _ _ _ _ _))) fun t3 ⟨⟨L3, rd3, wr3, cs3, V3, W3, R3, hW3, hV3⟩, sp3, mx3, f3⟩ sy3 => ?_)
  obtain he3 : EnvD s t3 := he2.step rd3 wr3 sp3 (fun r hr _ => cs3 r hr) mx3 f3
  obtain W3e : ∀ k, (k < 15 ∨ (18 < k ∧ k < 35)) → k < nW → k ≠ 19 → k ≠ 20 → W3 k = W k := fun k h1 h2 h3 h4 =>
    (hW3 k h2 h3 h4 (by omega_using [h1]) (by omega_using [h1])).trans (mW_other (by omega_using [h1]))
  -- `DB` unmasked.
  refine WP.seq (WP.mono_syms (wp_good (dbArgs_good _) (dbArgs_ok (H := Hl.stream) L3 R3
    ((W3e 23 (by omega_using []) (by decide) (by omega_using []) (by omega_using [])).trans w23') (by omega_using [hz])
        (by omega_using [hk, hsD])))
    fun t4 ⟨⟨L4, k4, R4⟩, sp4, mx4, f4⟩ sy4 => ?_)
  obtain he4 : EnvD s t4 := he3.step k4.2.1 k4.2.2 sp4 (keep_cs3 k4 (by decide)) mx4 f4
  refine WP.seq (WP.mono (wp_good (Table.mgfT_good hgi hgu hgf _) (Table.mgfXorT_ok hG.stream hgi hgu hgf
    mG.hash mG.len (valid_of_link hG mG)
        (dtab hp he4 (sy4.trans (sy3.trans (sy2.trans (sy1.trans hsy)))) ok hm hDm)
        L4 R4 ⟨by unfold oEm oSt; omega_using [hz], by unfold oEm oSt; omega_using [hk2, hz], by omega_using [], by omega_using [hk, hsD], by omega_using [hk2]⟩
    (mW_args _ _ _ _ _ _))) fun t5 ⟨⟨L5, rd5, wr5, cs5, V5, W5, R5, hW5, hV5⟩, sp5, mx5, f5⟩ => ?_)
  obtain he5 : EnvD s t5 := he4.step rd5 wr5 sp5 (fun r hr _ => cs5 r hr) mx5 f5
  obtain W5e : ∀ k, (k < 15 ∨ (18 < k ∧ k < 35)) → k < nW → k ≠ 19 → k ≠ 20 → W5 k = W k := fun k h1 h2 h3 h4 =>
    (hW5 k h2 h3 h4 (by omega_using [h1]) (by omega_using [h1])).trans ((mW_other (by omega_using [h1])).trans (W3e k h1 h2 h3 h4))
  obtain w5k : W5 23 = BitVec.ofNat 64 (s.gpr .r8).toNat :=
    (W5e 23 (by omega_using []) (by decide) (by omega_using []) (by omega_using [])).trans w23'
  -- `lHash'` against `lHash`.
  refine WP.seq (WP.mono (wp_good (accLh_good _) (accLh_ok (Hm := Hl.stream) L5 R5 hD (by omega_using [hz])))
    fun t6 ⟨⟨L6, k6, R6⟩, sp6, mx6, f6⟩ => ?_)
  obtain he6 : EnvD s t6 := he5.step k6.2.1 k6.2.2 sp6 (keep_cs3 k6 (by decide)) mx6 f6
  -- The scan.
  refine WP.seq (WP.mono (wp_good (scan_good _) (scan_ok (Hm := Hl.stream) L6 R6
    (by simp only [upd]; rw [ifn (by decide)]; exact w5k) (by omega_using [hk, hsD]) hk2 (by omega_using [hz])))
    fun t7 ⟨⟨L7, k7, R7⟩, sp7, mx7, f7⟩ => ?_)
  obtain he7 : EnvD s t7 := he6.step k7.2.1 k7.2.2 sp7 (keep_cs3 k7 (by decide)) mx7 f7
  obtain w7k : ∀ j, j ≠ 31 → j ≠ 32 → (upd (upd (upd W5 31 (accL V5 Hl.stream.D Hl.stream.D)) 31
      ((scanS (tF V5 Hl.stream.D) (upd W5 31 (accL V5 Hl.stream.D Hl.stream.D) 31)
        ((s.gpr .r8).toNat - (2 * Hl.stream.D + 1))).2.2 |||
       (scanS (tF V5 Hl.stream.D) (upd W5 31 (accL V5 Hl.stream.D Hl.stream.D) 31)
        ((s.gpr .r8).toNat - (2 * Hl.stream.D + 1))).1)) 32
      (scanS (tF V5 Hl.stream.D) (upd W5 31 (accL V5 Hl.stream.D Hl.stream.D) 31)
        ((s.gpr .r8).toNat - (2 * Hl.stream.D + 1))).2.1) j = W5 j := fun j h1 h2 => by
    simp only [upd, ifn h1, ifn h2]
  -- The buffer.
  refine WP.seq (WP.mono (wp_good (clearBuf_good _) (clearBuf_ok (Hm := Hl.stream) L7 R7 (k := (s.gpr .r8).toNat)
    (by rw [w7k 23 (by decide) (by decide)]; exact w5k) (by omega_using [hk, hsD]) (by omega_using [hz])))
    fun t8 ⟨⟨L8, k8, hsi8, h108, hcx8, R8⟩, sp8, mx8, f8⟩ => ?_)
  obtain he8 : EnvD s t8 := he7.step k8.2.1 k8.2.2 sp8 (keep_cs3 k8 (by decide)) mx8 f8
  refine WP.seq (WP.mono (wp_good copyT_good (copyT_ok (Hm := Hl.stream) L8 R8 hsi8 h108 hcx8
    (by omega_using [hk, hsD]) hk2 (by omega_using [hz])))
    fun t9 ⟨⟨L9, k9, hcx9, R9⟩, sp9, mx9, f9⟩ => ?_)
  obtain he9 : EnvD s t9 := he8.step k9.2.1 k9.2.2 sp9 (keep_cs3 k9 (by decide)) mx9 f9
  -- The shift.
  obtain ⟨idx, hidx, hidx'⟩ := scan_idx (tF V5 Hl.stream.D) (upd W5 31 (accL V5 Hl.stream.D Hl.stream.D) 31)
    ((s.gpr .r8).toNat - (2 * Hl.stream.D + 1))
  refine WP.seq (WP.mono (wp_good shift_good (shift_ok L9 R9 hcx9 (idx := idx) (by simp only [upd]; exact hidx)
    (by omega_using [hk2, hidx']) (fun x h1 h2 => by
      simp only [cpV, clrV]
      rw [ifn (by omega_using [hk2, h1]), ifp (by omega_using [h2])])))
    fun t10 ⟨⟨L10, k10, V10, W10, R10, hW10, hB10, hO10⟩, sp10, mx10, f10⟩ => ?_)
  obtain he10 : EnvD s t10 := he9.step k10.2.1 k10.2.2 sp10 (keep_cs3 k10 (by decide)) mx10 f10
  -- `ok`.
  refine WP.seq (WP.mono (wp_good (block_good _ rfl) (okMask_ok L10 R10))
    fun t11 ⟨⟨L11, k11, h11, R11⟩, sp11, mx11, f11⟩ => ?_)
  obtain he11 : EnvD s t11 := he10.step k11.2.1 k11.2.2 sp11 (keep_cs3 k11 (by decide)) mx11 f11
  obtain W11e : ∀ j, j < nW → j ≠ 31 → j ≠ 32 → j ≠ 33 → j ≠ 34 → j ≠ 35 → j ≠ 36 →
      (upd W10 33 (okW W10)) j = W5 j := fun j hj h1 h2 h3 h4 h5 h6 => by
    simp only [upd, ifn h3]
    rw [hW10 j hj h4 h5 h6, w7k j h1 h2]
  obtain Wk : ∀ j ∈ decKs, (upd W10 33 (okW W10)) j = W j := fun j hj => by
    simp only [decKs, List.mem_cons, List.not_mem_nil, or_false] at hj
    rw [W11e j (by rcases hj with h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide)
      (by omega_using [hj]) (by omega_using [hj]) (by omega_using [hj]) (by omega_using [hj]) (by omega_using [hj]) (by omega_using [hj])]
    exact W5e j (by omega_using [hj]) (by rcases hj with h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide)
      (by omega_using [hj]) (by omega_using [hj])
  obtain hW11 : ArgsD s (upd W10 33 (okW W10)) := hW.of Wk
  obtain ⟨-, x21, -, x23, -, -, -, -, -, x29⟩ := hW11.w
  -- `out`.
  obtain hout : (⟨s.gpr .rdi, (s.gpr .r8).toNat⟩ : Region) = outR s := by simp [outR, hp.hsi]
  obtain aO : Apart (fb s) (stackArg s 15) ⟨s.gpr .rdi, (s.gpr .r8).toNat⟩ := by
    rw [hout]; exact ⟨hp.dKO.sub_left (frame_subD s), hp.dOs.symm.sub_left sS, hp.dKO.sub_left (ret_subD s)⟩
  refine WP.seq (WP.mono (wp_good outLoop_good (outLoop_ok L11 R11 x21
    (by rw [x23, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by omega_using [hk1]) hk2 (by rw [he11.wr, hout]; simp)
    (by have := hp.wO; rw [hp.hsi] at this; exact this) aO))
    fun t12 ⟨⟨L12, k12, R12, ho12, fo12⟩, sp12, mx12, f12⟩ => ?_)
  obtain he12 : EnvD s t12 := he11.step k12.2.1 k12.2.2 sp12 (keep_cs3 k12 (by decide)) mx12 f12
  -- The length and the result.
  obtain aM : Apart (fb s) (stackArg s 15) (mlR s) :=
    ⟨hp.dKM.sub_left (frame_subD s), hp.dMs.symm.sub_left sS, hp.dKM.sub_left (ret_subD s)⟩
  refine WP.mono (wp_good (block_good _ rfl) (decRet_ok (Hm := Hl.stream) L12 R12 (pm := s.gpr .rdx)
    (k := (s.gpr .r8).toNat) x29 (by rw [x23, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by omega_using [hk, hsD]) (by omega_using [hz])
    (by rw [he12.wr]; simp [mlR]) hp.wM aM)) fun t13 ⟨⟨k13, hm13, hax13⟩, sp13, mx13, f13⟩ => ?_
  obtain he13 : EnvD s t13 := he12.step k13.2.1 k13.2.2 sp13 (keep_cs3 k13 (by decide)) mx13 f13
  refine ⟨he13, ?_⟩
  -- The bytes: `EM` unmasked, `lHash`, `T` and the buffer.
  have hlen : mH.G.len = Hl.D := mH.len
  obtain hlhl : (mH.G.hash (Spec.Rsa.bytesAt s.mem (stackArg s 11) (stackArg s 12).toNat)).length = Hl.D := by
    rw [(valid_of_link hH mH).2, hlen]
  simp only [hsD] at hV1' hV3 hV5 hidx hidx' hB10 w7k hW10 W11e hm13 hax13 ho12 hW5 W5e
  generalize hDD : Hl.D = D at *
  generalize hkk : (s.gpr .r8).toNat = k at *
  obtain nl : ∀ x, x < oSt → ¬ inR (labR oLh) x := fun x hx => by
    simp only [labR, inR_cons, inR_nil, or_false]; unfold oSt oLh oW at *; omega_using [hx]
  obtain v1 : ∀ x < k, V1 x = V x := fun x hx => hV1 x (nl x (by unfold oSt; omega_using [hk2, hx]))
  obtain v3 : ∀ x < k, V3 x = mixV V1 (Spec.Mgf1.mgf1 mG.G (srcB V1 (1 + D) (k - (D + 1))) D) 1 D x :=
    fun x hx => by rw [hV3 x (by unfold oRsa; omega_using [hk2, hx]) ((mOut_iff x).mpr (.inl (by unfold oSt; omega_using [hk2, hx])))]; rfl
  obtain v5 : ∀ x < k, V5 x = mixV V3 (Spec.Mgf1.mgf1 mG.G (srcB V3 1 D) (k - (D + 1))) (1 + D) (k - (D + 1)) x :=
    fun x hx => by rw [hV5 x (by unfold oRsa; omega_using [hk2, hx]) ((mOut_iff x).mpr (.inl (by unfold oSt; omega_using [hk2, hx])))]; rfl
  obtain hc5 := chain_eq (by omega_using [hk]) v1 v3 v5
  obtain lh5 : ∀ i < D, V5 (oLh + i) =
      (mH.G.hash (Spec.Rsa.bytesAt s.mem (stackArg s 11) (stackArg s 12).toNat)).getD i 0 := fun i hi => by
    obtain mo : mOut (oLh + i) := (mOut_iff _).mpr (.inr (.inl (by unfold oLh oDig oCtr; omega_using [hz, hsD, hi])))
    rw [hV5 _ (by unfold oLh oRsa; omega_using [hk2, hk, hi]) mo, mixV, ifn (by unfold oLh oEm at *; omega_using [hk2]),
      hV3 _ (by unfold oLh oRsa; omega_using [hk2, hk, hi]) mo, mixV, ifn (by unfold oLh oEm at *; omega_using [hk2, hk]), hV1' i hi]
  -- `T` and the scan.
  obtain hTl : (srcB V5 (1 + 2 * D) (k - (2 * D + 1))).length = k - (2 * D + 1) := by simp [srcB]
  obtain hTg : ∀ i < k - (2 * D + 1), (srcB V5 (1 + 2 * D) (k - (2 * D + 1))).getD i 0 = tF V5 D i := fun i hi => by
    rw [srcB, map_range_getD' _ hi]; simp only [tF, c0]
  obtain hsc : scanS (tF V5 D) (upd W5 31 (accL V5 D D) 31) (k - (2 * D + 1)) =
      scanS (fun i => (srcB V5 (1 + 2 * D) (k - (2 * D + 1))).getD i 0) (accL V5 D D)
        (srcB V5 (1 + 2 * D) (k - (2 * D + 1))).length := by
    rw [hTl, show upd W5 31 (accL V5 D D) 31 = accL V5 D D by simp [upd]]
    exact scanS_congr _ _ fun i hi => (hTg i hi).symm
  rw [hsc] at hidx w7k hW10
  generalize hT : srcB V5 (1 + 2 * D) (k - (2 * D + 1)) = T at *
  generalize hsc' : scanS (fun i => T.getD i 0) (accL V5 D D) T.length = sc at *
  -- The frame's words at the end.
  obtain e30 : (upd W10 33 (okW W10)) 30 = W 30 := by
    rw [W11e 30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact W5e 30 (by omega_using []) (by decide) (by decide) (by decide)
  obtain e31 : W10 31 = sc.2.2 ||| sc.1 := by
    rw [hW10 31 (by decide) (by decide) (by decide) (by decide)]; simp [upd]
  obtain e32 : (upd W10 33 (okW W10)) 32 = BitVec.ofNat 64 idx := by
    simp only [upd]; rw [ifn (by decide), hW10 32 (by decide) (by decide) (by decide) (by decide)]
    simp [upd, hidx]
  obtain e33 : (upd W10 33 (okW W10)) 33 = zM (W 30 ^^^ 1) &&& zM (sc.2.2 ||| sc.1) := by
    simp only [upd, ite_true, okW]
    rw [e31, show W10 30 = W 30 from (show W10 30 = (upd W10 33 (okW W10)) 30 by simp [upd]).trans e30]
  -- The outputs.
  have hTl' : T.length = k - (2 * D + 1) := hTl
  obtain hbuf : ∀ x, bufB (cpV (clrV V5 oBuf 2048) (tF (clrV V5 oBuf 2048) D) oBuf (k - (2 * D + 1))) x =
      T.getD x 0 := fun x => by
    obtain hge : ∀ y, k - (2 * D + 1) ≤ y → T.getD y 0 = 0 := fun y hy => by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show T.length ≤ y by omega_using [hTl', hy])]
    unfold bufB
    by_cases hx : x < 1024
    · rw [ifp hx, cpV]
      by_cases hxt : x < k - (2 * D + 1)
      · rw [ifp (by unfold oBuf; omega_using [hxt]), hTg x hxt, show oBuf + x - oBuf = x by omega_using [], tF, tF, clrV,
          ifn (by unfold oBuf oEm; omega_using [hk2, hxt])]
      · rw [ifn (by unfold oBuf; omega_using [hxt]), clrV, ifp (by unfold oBuf; omega_using [hx]), hge x (by omega_using [hxt])]
    · rw [ifn hx, hge x (by omega_using [hk2, hx])]
  obtain okv := zM (W 30 ^^^ 1) &&& zM (sc.2.2 ||| sc.1)
  obtain hfm : Frame [⟨s.gpr .rdx, 8⟩] t12.mem t13.mem := by
    rw [hm13]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain dom : Region.Disjoint ⟨s.gpr .rdi, k⟩ ⟨s.gpr .rdx, 8⟩ := by
    have := hp.dOM; rw [hp.hsi, hkk] at this; exact this
  obtain hout : ∀ i < k, t13.mem (s.gpr .rdi + BitVec.ofNat 64 i) =
      andB (T.getD (i + (idx + 1)) 0) (zM (W 30 ^^^ 1) &&& zM (sc.2.2 ||| sc.1)) := fun i hi => by
    rw [hfm.bytes (R := ⟨s.gpr .rdi, k⟩) (fun r hr => by rw [List.mem_singleton.mp hr]; exact dom)
      (show k ≤ 2 ^ 64 by omega_using [hsl]) hi, ho12 i hi, hB10 i (by omega_using [hk2, hi]), hbuf, e33]
  obtain hml : t13.mem.readW (s.gpr .rdx) 64 =
      (BitVec.ofNat 64 (k - (2 * D + 2)) - BitVec.ofNat 64 idx) &&& (zM (W 30 ^^^ 1) &&& zM (sc.2.2 ||| sc.1)) := by
    rw [hm13, Mem.readW_writeW_self64, e32, e33]
  obtain hrax : t13.gpr .rax = (zM (W 30 ^^^ 2) &&& 2) ||| ((zM (W 30 ^^^ 1) &&& zM (sc.2.2 ||| sc.1)) &&& 1) := by
    rw [hax13, faultW, e30, e33]
  -- The accumulator.
  obtain ⟨i1, -, -, i4⟩ := scanS_inv (fun i => T.getD i 0) (accL V5 D D) T.length
  rw [hsc'] at i1 i4
  obtain hacc : sc.2.2 ||| sc.1 = 0 ↔
      accL V5 D D = 0 ∧ ¬ bad (fun i => T.getD i 0) T.length ∧ ¬ lk (fun i => T.getD i 0) T.length := by
    rw [i4, i1, or_eq_zero, or_eq_zero, mk_eq_zero, mk_eq_zero, and_assoc]
  obtain zero_out : zM (W 30 ^^^ 1) &&& zM (sc.2.2 ||| sc.1) = 0 →
      Spec.Rsa.bytesAt t13.mem (s.gpr .rdi) k = Spec.RsaOaep.zeros k ∧ t13.mem.readW (s.gpr .rdx) 64 = 0 ∧
      (t13.gpr .rax).setWidth 32 = (zM (W 30 ^^^ 2) &&& 2).setWidth 32 := fun h0 =>
    ⟨out_zero fun i hi => by rw [hout i hi, h0, andB_zero], by rw [hml, h0]; exact BitVec.and_zero,
      by rw [hrax, h0, show (0 : BitVec 64) &&& 1 = 0 by decide,
        show ∀ x : BitVec 64, x ||| 0 = x from fun x => by simp]⟩
  cases o with
  | fault =>
    have h2 : W 30 = 2 := hres
    obtain ⟨a, b, c⟩ := zero_out (by rw [h2, show zM ((2 : BitVec 64) ^^^ 1) = 0 by decide]; exact BitVec.zero_and)
    exact ⟨by rw [c, h2]; decide, a, b⟩
  | invalid =>
    have h0 : W 30 = 0 := hres
    obtain ⟨a, b, c⟩ := zero_out (by rw [h0, show zM ((0 : BitVec 64) ^^^ 1) = 0 by decide]; exact BitVec.zero_and)
    exact ⟨by rw [c, h0]; decide, a, b⟩
  | ok em =>
    obtain ⟨h1, hem⟩ := hres
    subst hem
    obtain hV : (fun i => V (oEm + i)) = V := funext fun i => by rw [c0, Nat.zero_add]
    rw [hV]
    obtain hok : zM (W 30 ^^^ 1) &&& zM (sc.2.2 ||| sc.1) = zM (sc.2.2 ||| sc.1) := by
      rw [h1, show zM ((1 : BitVec 64) ^^^ 1) = BitVec.allOnes 64 by decide, BitVec.allOnes_and]
    obtain hf2 : zM (W 30 ^^^ 2) &&& 2 = 0 := by rw [h1]; decide
    rw [hok] at zero_out hout hml hrax
    rw [hf2, show ∀ x : BitVec 64, 0 ||| x = x from fun x => by simp] at hrax
    simp only [decOut]
    rw [decode_eq (H := mH.G) (valid_of_link hG mG) _ (by omega_using [hk]) hlen hc5, hT]
    obtain hz : ∀ (hne : sc.2.2 ||| sc.1 ≠ 0), _ := fun hne => zero_out (by simp only [zM]; rw [ifn hne])
    by_cases hfd : ¬ lk (fun i => T.getD i 0) T.length ∧ ¬ bad (fun i => T.getD i 0) T.length
    · obtain ⟨j₀, hj₀, hsj, hdw⟩ := scan_found T (accL V5 D D) hfd.1 hfd.2
      rw [hsc'] at hsj
      obtain hij : idx = j₀ := by
        have := hidx.symm.trans hsj
        have := congrArg BitVec.toNat this
        rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hsl, hidx']),
          Nat.mod_eq_of_lt (by omega_using [hsl, hTl', hj₀])] at this
      subst hij
      rw [hdw, show (1 : Byte) = 1#8 from rfl]
      simp only []
      obtain hV0 : V5 0 = V 0 := by
        rw [hc5 0 (by omega_using [hTl', hj₀]), mixV, ifn (by omega_using []), mixV, ifn (by omega_using [])]
      obtain htake : ((List.range k).map V).take 1 = [V 0] := by
        rw [show k = (k - 1) + 1 by omega_using [hTl', hj₀], List.range_succ_eq_map]; simp
      by_cases hc : ((List.range k).map V).take 1 = [0x00] ∧ srcB V5 (1 + D) D =
          mH.G.hash (Spec.Rsa.bytesAt s.mem (stackArg s 11) (stackArg s 12).toNat)
      · rw [ifp hc]
        obtain hacc0 : sc.2.2 ||| sc.1 = 0 := hacc.mpr ⟨(accL_eq_zero V5 D D).mpr ⟨by
            rw [c0, hV0]; rw [htake] at hc; exact List.head_eq_of_cons_eq hc.1, fun i hi => by
            rw [lh5 i hi, ← hc.2, srcB, map_range_getD' _ hi, c0]⟩, hfd.2, hfd.1⟩
        obtain hzm : zM (sc.2.2 ||| sc.1) = BitVec.allOnes 64 := by simp only [zM]; rw [ifp hacc0]
        rw [hzm] at hout hml hrax
        refine ⟨by rw [hrax]; decide, out_list (by omega_using [hTl']) hj₀ fun i hi => by rw [hout i hi, andB_ones], ?_⟩
        rw [hml, BitVec.and_allOnes, VG.Offset.ofNat_sub_ofNat (by omega_using [hTl', hj₀]), List.length_drop]
        congr 1; omega_using [hTl']
      · rw [ifn hc]
        obtain hne : sc.2.2 ||| sc.1 ≠ 0 := fun h0 => hc ⟨by
            rw [htake, ← hV0, show (0 : Nat) = oEm from rfl, ((accL_eq_zero V5 D D).mp (hacc.mp h0).1).1],
          by
            refine srcB_eq hlhl fun i hi => ?_
            rw [← lh5 i hi, ((accL_eq_zero V5 D D).mp (hacc.mp h0).1).2 i hi, c0]⟩
        obtain ⟨a, b, c⟩ := hz hne
        exact ⟨by rw [c, hf2]; rfl, a, b⟩
    · have hfail := scan_fail T (by
        by_contra hc; exact hfd ⟨fun h => hc (.inl h), fun h => hc (.inr h)⟩)
      obtain hne : sc.2.2 ||| sc.1 ≠ 0 := fun h0 => hfd ⟨(hacc.mp h0).2.2, (hacc.mp h0).2.1⟩
      obtain ⟨a, b, c⟩ := hz hne
      split
      · rename_i m heq
        split at heq
        · rename_i m' hm; exact absurd hm (hfail m')
        · cases heq
      · exact ⟨by rw [c, hf2]; rfl, a, b⟩

end VG.Proof.RsaOaep.X86_64
