module
public import VerifiedGarbage.Impl.RsaPss.X86_64.Encoding
public import VerifiedGarbage.Proof.RsaPss.X86_64.PrecomputedCtx
import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyCall
public import VerifiedGarbage.Proof.RsaPss.X86_64.ChkCtx

import VerifiedGarbage.Proof.RsaPss.X86_64.PrecomputedArgs
import VerifiedGarbage.Proof.RsaPss.X86_64.SignCall
import VerifiedGarbage.Proof.RsaPss.X86_64.SignCCall
import VerifiedGarbage.Proof.Framework.X86_64.CallFrame
import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyMain
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaPss.X86_64.Safe
import Mathlib.Tactic.Set
public import VerifiedGarbage.Impl.Rsa.X86_64
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
public import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyFrame

/-!
# RSASSA-PSS verification with cached public-key values on x86-64, around
the check of the encoding: the call of `checkEncoding`

`chkArgs` stores to `sAcc` whether the first `lo` bytes of the public-key
operation's output are zero (all ones if so), and `checkEncoding`'s
arguments: the digest, the last `emLen` bytes of the output, `emBits`, the
salt length's arguments, and the working space after the output
(`chkArgs_ok`); `checkEncoding` then runs under its contract and returns
whether the encoding is consistent, the frame and the output kept
(`chk_call`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Pc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep ifp ifn)

variable {G : Spec.Mgf1.Hash}

def cA1 : List Instr :=
  [.mov .rcx (.mem (sp sScr)), .movzx8 .r9 (at_ .rcx), .mov .r10 (.mem (sp sLo)), .mov32 .r11 (.imm 0),
    .alu .sub .r11 (.reg .r10), .alu .and .r9 (.reg .r11), .alu .cmp .r9 (.imm 1), .alu .sbb .r9 (.reg .r9),
    .store (sp sAcc) .r9]

/-- `sAcc`: all ones if the first `lo ≤ 1` bytes are zero. -/
def accV (lo : Nat) (b : Byte) : BitVec 64 := if lo = 0 ∨ b = 0 then BitVec.allOnes 64 else 0

theorem cA1_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {lo : Nat} (h26 : W 26 = BitVec.ofNat 64 lo) (hlo : lo ≤ 1) :
    WP isa (.block cA1) u fun u' => Keep [.rcx, .r9, .r10, .r11] u u' ∧
      u'.mem = u.mem.writeW (off F sAcc) (accV lo (V 0)) ∧ u'.gpr .rcx = S ∧ u'.gpr .r10 = BitVec.ofNat 64 lo := by
  have hs := L.slot
  simp only [Bignum.word] at hs
  have h0 : u.mem S = V 0 := by have := R.scr 0 (by decide); rwa [off_zero] at this
  have hl0 : InRegions (u.rd ++ u.wr) S 1 := by have := L.sld8 (d := 0) (by decide); rwa [off_zero] at this
  refine WP.mono (WP.keep [.rcx, .r9, .r10, .r11] (Q := fun u' =>
      u'.mem = u.mem.writeW (off F sAcc) (accV lo (V 0)) ∧ u'.gpr .rcx = S ∧ u'.gpr .r10 = BitVec.ofNat 64 lo) ?_ rfl)
    fun u' ⟨h, k⟩ => ⟨k, h⟩
  xrun [cA1, ea_sp, ea_at0, L.rsp, L.ld (d := sScr) (by decide), L.ld (d := sLo) (by decide),
    L.st (d := sAcc) (by decide), hs, hl0, h0, R.rd (d := sLo) 26 rfl (by decide), h26]
  refine congrArg (u.mem.writeW (off F sAcc)) ?_
  generalize V 0 = b
  rcases (show lo = 0 ∨ lo = 1 by omega) with rfl | rfl
  · revert b; decide
  · revert b; decide

def cA2 : List Instr :=
  [.mov .rdi (.mem (sp sDig)), .mov .rsi (.reg .rcx), .alu .add .rsi (.reg .r10), .mov .rdx (.mem (sp sEml)),
    .mov .r8 (.mem (arg 1)), .mov .r9 (.mem (arg 2))]

def cA3 : List Instr :=
  [.mov .rax (.mem (sp sK)), .alu .add .rax (.imm 7), .shift .shr .rax 3, .mov .r10 (.mem (sp sScrLen)),
    .alu .sub .r10 (.reg .rax), .store (sp 8) .r10, .shift .shl .rax 3, .alu .add .rax (.reg .rcx),
    .store (sp 0) .rax, .mov .rcx (.mem (sp sBits))]

theorem chkArgs_eq : chkArgs = cA1 ++ cA2 ++ cA3 := rfl

/-- `⌈k / 8⌉`, the words of the output. -/
def kw (k : Nat) : Nat := (k + 7) / 8

/-- The slots after `chkArgs`. -/
def chkW (W : Nat → BitVec 64) (s : State) (lo : Nat) (b : Byte) : Nat → BitVec 64 :=
  upd (upd (upd W 33 (accV lo b)) 1 (stackArg s 4 - BitVec.ofNat 64 (kw (s.gpr .rsi).toNat))) 0
    (off (stackArg s 3) (8 * kw (s.gpr .rsi).toNat))

theorem chkArgs_ok {s u : State} (hp : Pre G s) (L : Lay u (fb s) (stackArg s 3)) {V : Nat → Byte}
    {W : Nat → BitVec 64} (R : Rep u.mem (fb s) (stackArg s 3) V W) (hw : u.wr = frR s :: s.wr)
    (hrd : u.rd = s.rd) (hM : Frame (vwrR s) s.mem u.mem) {lo el eb : Nat}
    (h17 : W 17 = s.gpr .rsi) (h22 : W 22 = stackArg s 4) (h26 : W 26 = BitVec.ofNat 64 lo)
    (h27 : W 27 = BitVec.ofNat 64 eb) (h28 : W 28 = BitVec.ofNat 64 el) (h37 : W 37 = s.gpr .r8) (hlo : lo ≤ 1) :
    WP isa (.block chkArgs) u fun u' => Lay u' (fb s) (stackArg s 3) ∧
      Keep [.rcx, .r9, .r10, .r11, .rdi, .rsi, .rdx, .r8, .r9, .rax, .r10, .rcx] u u' ∧
      Rep u'.mem (fb s) (stackArg s 3) V (chkW W s lo (V 0)) ∧ Frame (vwrR s) s.mem u'.mem ∧
      u'.gpr .rdi = s.gpr .r8 ∧ u'.gpr .rsi = off (stackArg s 3) lo ∧ u'.gpr .rdx = BitVec.ofNat 64 el ∧
      u'.gpr .rcx = BitVec.ofNat 64 eb ∧ u'.gpr .r8 = stackArg s 1 ∧ u'.gpr .r9 = stackArg s 2 := by
  have G' := L.geo
  have hk1 := hp.k1; have hk2 := hp.k2
  set S := stackArg s 3
  rw [chkArgs_eq, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keepIn (by decide) (by exact Nat.zero_le 8) (cA1_ok L R h26 hlo))
    fun u1 ⟨⟨k1, hm1, hcx1, h101⟩, f1⟩ => ?_
  have hM1 := vframe_keep hp.toVPre hw L.rsp hM f1
  have R1 := R.wf G' (k := 33) (by decide) (accV lo (V 0))
  rw [show off (fb s) (8 * 33) = off (fb s) sAcc from rfl, ← hm1] at R1
  have L1 : Lay u1 (fb s) S := L.of_rep' R R1 (by simp [upd]) (k1.gpr (by decide)) k1.2.2
  refine WP.mono (WP.keep [.rdi, .rsi, .rdx, .r8, .r9] (Q := fun v => v.mem = u1.mem ∧ v.gpr .rdi = s.gpr .r8 ∧
      v.gpr .rsi = off S lo ∧ v.gpr .rdx = BitVec.ofNat 64 el ∧ v.gpr .r8 = stackArg s 1 ∧ v.gpr .r9 = stackArg s 2)
    ?_ rfl) fun v ⟨⟨hm2, hdi, hsi, hdx, h8, h9⟩, k2⟩ => ?_
  · xrun [cA2, arg, ea_sp, L1.rsp, L1.ld (d := sDig) (by decide), L1.ld (d := sEml) (by decide),
      R1.rd (d := sDig) 37 rfl (by decide), R1.rd (d := sEml) 28 rfl (by decide),
      arg_read hp (k1.2.1.trans hrd) (show 1 < 7 by decide), arg_read hp (k1.2.1.trans hrd) (show 2 < 7 by decide),
      arg_keep hp hM1 (show 1 < 7 by decide), arg_keep hp hM1 (show 2 < 7 by decide), hcx1, h101]
    simp [upd, h37, h28]
  have L2 : Lay v (fb s) S := L1.congr (k2.gpr (by decide)) k2.2.2 (by rw [hm2])
  have R2 : Rep v.mem (fb s) S V (upd W 33 (accV lo (V 0))) := by rw [hm2]; exact R1
  have Ra := R2.wf G' (k := 1) (by decide) (stackArg s 4 - BitVec.ofNat 64 (kw (s.gpr .rsi).toNat))
  have Rb := Ra.wf G' (k := 0) (by decide) (off S (8 * kw (s.gpr .rsi).toNat))
  rw [show off (fb s) (8 * 1) = off (fb s) 8 from rfl] at Ra Rb
  rw [show off (fb s) (8 * 0) = fb s from off_zero _] at Rb
  have hst0 : InRegions v.wr (fb s) 8 := by simpa only [off_zero] using L2.st (d := 0) (by decide)
  have hcx2 : v.gpr .rcx = S := by rw [k2.gpr (by decide)]; exact hcx1
  have hM2 : Frame (vwrR s) s.mem v.mem := by rw [hm2]; exact hM1
  refine WP.mono (WP.keepIn (by decide) (by exact Nat.zero_le 8) (WP.keep [.rax, .r10, .rcx] (Q := fun y =>
      y.mem = (v.mem.writeW (off (fb s) 8) (stackArg s 4 - BitVec.ofNat 64 (kw (s.gpr .rsi).toNat))).writeW (fb s)
      (off S (8 * kw (s.gpr .rsi).toNat)) ∧ y.gpr .rcx = BitVec.ofNat 64 eb) ?_ rfl))
    fun y ⟨⟨⟨hm3, hcx⟩, k3⟩, f3⟩ => ?_
  · xrun [cA3, ea_sp, L2.rsp, L2.ld (d := sK) (by decide), L2.ld (d := sScrLen) (by decide),
      L2.st (d := 8) (by decide), hst0, L2.ld (d := sBits) (by decide),
      R2.rd (d := sK) 17 rfl (by decide), R2.rd (d := sScrLen) 22 rfl (by decide), hcx2]
    have e1 : (s.gpr .rsi + BitVec.signExtend 64 (7 : BitVec 32)) >>> 3 = BitVec.ofNat 64 (kw (s.gpr .rsi).toNat) := by
      rw [show BitVec.signExtend 64 (7 : BitVec 32) = BitVec.ofNat 64 7 from rfl]
      unfold kw
      generalize s.gpr .rsi = x at *
      bv_omega
    have e2 : BitVec.ofNat 64 (kw (s.gpr .rsi).toNat) <<< 3 + S = off S (8 * kw (s.gpr .rsi).toNat) := by
      rw [BitVec.add_comm]; simp only [off]; congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
      unfold kw; rw [Nat.shiftLeft_eq]; omega
    simp only [upd, Nat.reduceEqDiff, ite_false, h17, h22, e1, e2]
    refine ⟨trivial, ?_⟩
    rw [Rb.rd (d := sBits) 27 rfl (by decide)]; simp [upd, h27]
  have R3 : Rep y.mem (fb s) S V (chkW W s lo (V 0)) := by rw [hm3]; exact Rb
  refine ⟨L2.of_rep' R2 R3 (by simp [chkW, upd]) (k3.gpr (by decide)) k3.2.2, (k1.trans k2).trans k3, R3,
    vframe_keep hp.toVPre (k2.2.2.trans (k1.2.2.trans hw)) L2.rsp hM2 f3, ?_, ?_, ?_, hcx, ?_, ?_⟩ <;>
    rw [k3.gpr (by decide)] <;> with_reducible assumption


/-! ## The call -/

variable (G) in
/-- What `checkEncoding` reads: the digest, the encoding and its stack
arguments. -/
def kRd (s : State) (lo el : Nat) : List Region :=
  [⟨s.gpr .r8, G.len⟩, ⟨off (stackArg s 3) lo, el⟩, ⟨fb s, 16⟩]

/-- What it writes: its working space, after the output. -/
def kWr (s : State) : List Region :=
  [⟨off (stackArg s 3) (8 * kw (s.gpr .rsi).toNat),
    (stackArg s 4 - BitVec.ofNat 64 (kw (s.gpr .rsi).toNat)).toNat * 8⟩]

theorem kw_le {k : Nat} : k ≤ 8 * kw k := by unfold kw; omega

theorem ck_pre {s t : State} (hp : Pre G s) (hsp : t.gpr .rsp = fb s) {lo eb el : Nat}
    (h0 : word t.mem (fb s) (8 * 0) = off (stackArg s 3) (8 * kw (s.gpr .rsi).toNat))
    (h1 : word t.mem (fb s) (8 * 1) = stackArg s 4 - BitVec.ofNat 64 (kw (s.gpr .rsi).toNat))
    (hdi : t.gpr .rdi = s.gpr .r8) (hsi : t.gpr .rsi = off (stackArg s 3) lo)
    (hdx : t.gpr .rdx = BitVec.ofNat 64 el) (hcx : t.gpr .rcx = BitVec.ofNat 64 eb)
    (hlo : lo + el ≤ (s.gpr .rsi).toNat) (heb1 : 1 ≤ eb) (heb2 : eb ≤ Proof.RsaPss.maxEmBits)
    (hel : el = Spec.RsaPss.emLength eb) :
    (chkK G).pre (t.callEntry.withRegions (kRd G s lo el) (kWr s)) := by
  have hE0 := (vstackArg_call hp.toVPre hsp (kRd G s lo el) (kWr s) (i := 0) (by decide)).trans h0
  have hE1 := (vstackArg_call hp.toVPre hsp (kRd G s lo el) (kWr s) (i := 1) (by decide)).trans h1
  simp only [chkK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.callEntry_rsp,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    hdi, hsi, hdx, hcx, hsp, stackArgAddr_call hsp, hE0, hE1]
  have hF := vfb_toNat hp.toVPre
  have := hp.sp1; have := hp.sp2
  have hk1 := hp.k1; have hk2 := hp.k2
  have hsl := hp.hsl; have wS := hp.wS
  have h392 : frameBytes = 392 := rfl
  have hvs : verifyStack = 800 := rfl
  have hcs : chkStack = 400 := rfl
  have c2 : oRsa = 8192 := rfl
  have h8' := vfb_sub8 hp.toVPre
  have hkw := kw_le (k := (s.gpr .rsi).toNat)
  have hkw2 : kw (s.gpr .rsi).toNat ≤ 128 := by unfold kw; omega
  have hsc : (stackArg s 4 - BitVec.ofNat 64 (kw (s.gpr .rsi).toNat)).toNat =
      (stackArg s 4).toNat - kw (s.gpr .rsi).toNat := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold kw at *; omega
  have hel2 : el ≤ 1024 := by omega
  have toNat_off : ∀ {p : Addr} {d : Nat}, p.toNat + d < 2 ^ 64 → (off p d).toNat = p.toNat + d := fun h => by
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [h]
  have hel' : (BitVec.ofNat 64 el).toNat = el := by rw [BitVec.toNat_ofNat]; omega
  have heb' : (BitVec.ofNat 64 eb).toNat = eb := by
    rw [BitVec.toNat_ofNat]; unfold Proof.RsaPss.maxEmBits at heb2; omega
  rw [hel', heb']
  have hsk : (kw (s.gpr .rsi).toNat) * 8 ≤ (stackArg s 4).toNat * 8 := by unfold kw at *; omega
  -- What lies in what.
  have sI : Region.Sub ⟨off (stackArg s 3) lo, el⟩ (vscrR s) := Offset.sub_base _ (by omega)
  have sR : Region.Sub ⟨off (stackArg s 3) (8 * kw (s.gpr .rsi).toNat),
      (stackArg s 4 - BitVec.ofNat 64 (kw (s.gpr .rsi).toNat)).toNat * 8⟩ (vscrR s) :=
    Offset.sub_base _ (by rw [hsc]; unfold kw at *; omega)
  have sA : Region.Sub ⟨fb s, 16⟩ (vstkR s) := fun a h => vframe_sub s a (Region.sub_prefix (by decide) a h)
  have sRet : Region.Sub ⟨fb s - 8, 8⟩ (vstkR s) := vret_sub s
  have sStk : Region.Sub ⟨fb s - 8 - BitVec.ofNat 64 chkStack, chkStack⟩ (vstkR s) := by
    simp only [vstkR, fb, show (8 : Addr) = BitVec.ofNat 64 8 from rfl, sub_sub']
    exact Offset.sub_below _ (by decide) (by decide)
  have dRA : (⟨fb s - 8, 8⟩ : Region).Disjoint ⟨fb s, 16⟩ :=
    (Offset.base_disjoint_below (fb s) (n := 8) (k := 16) (by omega)).symm
  have dKA : (⟨fb s - 8 - BitVec.ofNat 64 chkStack, chkStack⟩ : Region).Disjoint ⟨fb s, 16⟩ := by
    refine Region.Disjoint.sub_left (Offset.base_disjoint_below (fb s) (n := 408) (k := 16) (by omega)).symm ?_
    simp only [show (8 : Addr) = BitVec.ofNat 64 8 from rfl, sub_sub']
    exact Offset.sub_below _ (by decide) (by decide)
  have dIR : (⟨off (stackArg s 3) lo, el⟩ : Region).Disjoint
      ⟨off (stackArg s 3) (8 * kw (s.gpr .rsi).toNat), (stackArg s 4 - BitVec.ofNat 64 (kw (s.gpr .rsi).toNat)).toNat * 8⟩ :=
    Offset.disjoint _ (.inl (by omega)) (by omega) (by rw [hsc]; unfold kw at *; omega)
  have hsA : (vscrR s).Disjoint ⟨fb s, 16⟩ := (hp.dKs.sub_left sA).symm
  refine ⟨by unfold chkStack; omega, by omega, rfl, rfl,
    hp.ddgs.sub_right sR, dIR, hsA.sub_left sR,
    hp.dKdg.sub_left sRet, (hp.dKs.sub_left sRet).sub_right sI, (hp.dKs.sub_left sRet).sub_right sR, dRA,
    hp.dKdg.sub_left sStk, (hp.dKs.sub_left sStk).sub_right sI, (hp.dKs.sub_left sStk).sub_right sR, dKA,
    hp.wDg, by rw [toNat_off (by omega)]; omega, by rw [toNat_off (by omega), hsc]; unfold kw at *; omega,
    heb1, heb2, hel, by rw [hsc]; unfold Proof.RsaPss.encodingScratchWords kw at *; omega⟩

theorem ck_covers {s t : State} (hp : Pre G s) (hrd : t.rd = s.rd) (hwr : t.wr = frR s :: s.wr) {lo el : Nat}
    (hlo : lo + el ≤ (s.gpr .rsi).toNat) :
    Covers (kRd G s lo el ++ kWr s) (t.rd ++ t.wr) ∧ Covers (kWr s) t.wr := by
  have hsl := hp.hsl; have hk2 := hp.k2
  have hsc : (stackArg s 4 - BitVec.ofNat 64 (kw (s.gpr .rsi).toNat)).toNat =
      (stackArg s 4).toNat - kw (s.gpr .rsi).toNat := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold kw at *; omega
  have hfr : frR s ∈ t.wr := by rw [hwr]; exact List.mem_cons_self ..
  have hscr : (⟨stackArg s 3, (stackArg s 4).toNat * 8⟩ : Region) ∈ t.wr := by rw [hwr, hp.hwr]; simp
  have z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  have cw : Covers (kWr s) t.wr := Covers.of_sub fun r hr => by
    simp only [kWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact ⟨_, hscr, 8 * kw (s.gpr .rsi).toNat, rfl, by dsimp only; rw [hsc]; unfold kw at *; omega⟩
  have cr : Covers [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩,
      ⟨s.gpr .r8, G.len⟩, ⟨s.gpr .r9, (stackArg s 0).toNat⟩, ⟨stackArgAddr s 0, 40⟩]
      (t.rd ++ t.wr) := by rw [hrd]; exact hp.hrd.left
  refine ⟨Covers.append_left (Covers.of_forall fun r hr => ?_) cw.right, cw⟩
  simp only [kRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (Covers.of_mem (by intro r hr; rw [List.mem_singleton.mp hr]; simp)).trans cr
  · exact Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨_, List.mem_append_right _ hscr, lo, rfl, by dsimp only; omega⟩
  · exact Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨_, List.mem_append_right _ hfr, 0, z _, by dsimp only; decide⟩


theorem ck_call {chkN : String} {chkC : Prog isa}
    (hv : ∀ s, (chkK G).pre s → ∃ t s', Exec isa chkC s t s' ∧ abiPreserved s s' ∧ (chkK G).post s s')
    (hspC : SpSafe chkC) (hd : chkC.x86_64Depth ≤ chkStack)
    {s t : State} (hp : Pre G s) (hst : t.gpr .rsp = fb s) (hrd : t.rd = s.rd) (hwr : t.wr = frR s :: s.wr)
    (hM : Frame (vwrR s) s.mem t.mem) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem (fb s) (stackArg s 3) V W) {lo eb el : Nat}
    (h0 : word t.mem (fb s) (8 * 0) = off (stackArg s 3) (8 * kw (s.gpr .rsi).toNat))
    (h1 : word t.mem (fb s) (8 * 1) = stackArg s 4 - BitVec.ofNat 64 (kw (s.gpr .rsi).toNat))
    (hdi : t.gpr .rdi = s.gpr .r8) (hsi : t.gpr .rsi = off (stackArg s 3) lo)
    (hdx : t.gpr .rdx = BitVec.ofNat 64 el) (hcx : t.gpr .rcx = BitVec.ofNat 64 eb)
    (h8 : t.gpr .r8 = stackArg s 1) (h9 : t.gpr .r9 = stackArg s 2)
    (hlo : lo + el ≤ (s.gpr .rsi).toNat) (heb1 : 1 ≤ eb) (heb2 : eb ≤ Proof.RsaPss.maxEmBits)
    (hel : el = Spec.RsaPss.emLength eb) :
    WP isa (.call chkN chkC) t fun t' => t'.rd = t.rd ∧ t'.wr = t.wr ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧ t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 ∧
      Frame (vwrR s) s.mem t'.mem ∧
      Rep t'.mem (fb s) (stackArg s 3)
        (fun o => if inR [(8 * kw (s.gpr .rsi).toNat, oRsa - 8 * kw (s.gpr .rsi).toNat)] o then
          t'.mem (off (stackArg s 3) o) else V o) W ∧
      (t'.gpr .rax).setWidth 32 = if Spec.RsaPss.verifyEncoding G G (Spec.Rsa.bytesAt s.mem (s.gpr .r8) G.len)
        (Spec.Rsa.bytesAt t.mem (off (stackArg s 3) lo) el) eb
        (Spec.RsaPss.expectedSaltLen (stackArg s 1) ((stackArg s 2).setWidth 32)) then 1 else 0 := by
  obtain ⟨hc, hw⟩ := ck_covers hp hrd hwr hlo
  refine X86_64.WP.callF hv hspC (by unfold chkStack at hd; omega)
    (ck_pre hp hst h0 h1 hdi hsi hdx hcx hlo heb1 heb2 hel) hc hw ?_
  intro t' hrd' hwr' hcs hf ⟨s₂, hm₂, hg₂, hpost⟩ hmx
  have hF := vfb_toNat hp.toVPre
  have := hp.sp1; have := hp.sp2
  have hk2 := hp.k2; have hsl := hp.hsl; have wS := hp.wS
  have h392 : frameBytes = 392 := rfl
  have hvs : verifyStack = 800 := rfl
  have c2 : oRsa = 8192 := rfl
  have hkw := kw_le (k := (s.gpr .rsi).toNat)
  have hkw2 : kw (s.gpr .rsi).toNat ≤ 128 := by unfold kw; omega
  have hsc : (stackArg s 4 - BitVec.ofNat 64 (kw (s.gpr .rsi).toNat)).toNat =
      (stackArg s 4).toNat - kw (s.gpr .rsi).toNat := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold kw at *; omega
  rw [hst] at hf
  have sR : Region.Sub ⟨off (stackArg s 3) (8 * kw (s.gpr .rsi).toNat),
      (stackArg s 4 - BitVec.ofNat 64 (kw (s.gpr .rsi).toNat)).toNat * 8⟩ (vscrR s) :=
    Offset.sub_base _ (by rw [hsc]; unfold kw at *; omega)
  have sBel : Region.Sub (below (fb s) (chkC.x86_64Depth + 8)) (vstkR s) := by
    simp only [below, fb, vstkR, sub_sub']
    exact Offset.sub_below _ (by unfold chkStack at hd; omega) (by unfold chkStack at hd; omega)
  have dFb : (frR s).Disjoint (below (fb s) (chkC.x86_64Depth + 8)) :=
    Offset.base_disjoint_below (fb s) (by unfold chkStack at hd; omega)
  have hS8 : Region.Sub ⟨stackArg s 3, oRsa⟩ (vscrR s) := Region.sub_prefix (by omega)
  refine ⟨hrd', hwr', hcs, hmx, hM.trans (hf.sub fun r hr => ?_), ?_, ?_⟩
  · simp only [kWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), sR⟩
    · exact ⟨_, List.mem_cons_self .., sBel⟩
  · refine R.of_call hp.geo (fun x hx hin => hf x fun r hr hc => ?_) (by
      intro p hp'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
      subst hp'; dsimp only; omega)
    simp only [kWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rcases hin with hin | hin
      · refine hx _ (List.mem_singleton_self _) ?_
        have h1 := (Offset.lt_iff x (stackArg s 3) (d := 8 * kw (s.gpr .rsi).toNat)
          (n := (stackArg s 4 - BitVec.ofNat 64 (kw (s.gpr .rsi).toNat)).toNat * 8)
          (by rw [hsc]; unfold kw at *; omega)).mp (by simp only [Region.Contains, off] at hc; omega)
        have h2 : (x - stackArg s 3).toNat < oRsa := by simp only [Region.Contains] at hin; omega
        show (x - (stackArg s 3 + BitVec.ofNat 64 (8 * kw (s.gpr .rsi).toNat))).toNat + 1 ≤
          oRsa - 8 * kw (s.gpr .rsi).toNat
        have := (Offset.lt_iff x (stackArg s 3) (d := 8 * kw (s.gpr .rsi).toNat)
          (n := oRsa - 8 * kw (s.gpr .rsi).toNat) (by omega)).mpr ⟨h1.1, by omega⟩
        omega
      · exact (hp.dKs.sub_left (vframe_sub s)) x hin (sR x hc)
    · rcases hin with hin | hin
      · exact hp.dKs x (sBel x hc) (hS8 x hin)
      · exact dFb x hin hc
  · have fE : Frame [below (fb s) 8] t.mem t.callEntry.mem := by
      rw [State.callEntry_mem, hst]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))
    have fSE : Frame (vwrR s) s.mem t.callEntry.mem := hM.trans (fE.sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., vret_sub s⟩)
    have hel' : (BitVec.ofNat 64 el).toNat = el := by rw [BitVec.toNat_ofNat]; omega
    have heb' : (BitVec.ofNat 64 eb).toNat = eb := by
      rw [BitVec.toNat_ofNat]; unfold Proof.RsaPss.maxEmBits at heb2; omega
    simp only [chkK, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide),
      hdi, hsi, hdx, hcx, h8, h9, hg₂ .rax (by decide), hel', heb'] at hpost
    rw [bytesAt_frame fSE (p := s.gpr .r8) (len := G.len) (vin_apart hp.dKdg hp.ddgs) (by have := hp.wDg; omega),
      bytesAt_frame fE (p := off (stackArg s 3) lo) (len := el) (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact ((hp.dKs.sub_left (vret_sub s)).sub_right (Offset.sub_base _ (by omega) :
          Region.Sub ⟨off (stackArg s 3) lo, el⟩ (vscrR s))).symm) (by omega)] at hpost
    exact hpost


end VG.Proof.RsaPss.X86_64.Pc
