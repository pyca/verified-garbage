module

public import VerifiedGarbage.Proof.RsaPss.X86_64.PcChk
import VerifiedGarbage.Proof.RsaPss.X86_64.PcCArgs
public import VerifiedGarbage.Proof.RsaPss.X86_64.PrecomputedCall
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignCParams
public import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyPadding
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignCorrect
import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyBody
import VerifiedGarbage.Proof.RsaPss.X86_64.SignCCall
import VerifiedGarbage.Proof.RsaPss.X86_64.SignCCorrect
import VerifiedGarbage.Proof.RsaPss.SignEncode
import VerifiedGarbage.Proof.RsaPss.VerifyCases
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaPss.X86_64.Safe
import Mathlib.Tactic.Set
public import VerifiedGarbage.Impl.RsaPss.X86_64.Encoding
public import VerifiedGarbage.Proof.RsaPss.X86_64.PrecomputedCtx
public import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyCall

/-!
# RSASSA-PSS verification with cached public-key values on x86-64, around
the check of the encoding: correctness

`codeC_ok`: from the entry state, `verifyC` refuses a modulus whose first
byte is zero, computes `emBits`, calls the public-key operation for its
output at the start of `scratch`, and `checkEncoding` on its last `emLen`
bytes, and returns 1 exactly when those are a consistent encoding and the
bytes before them zero, which, when the cache matches the modulus, is
`RsaPss.verify` (`verify_encode`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Pc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep ifp ifn)
open VG.Proof.Rsa.X86_64 (PublicImpl)

variable {G : Spec.Mgf1.Hash}

variable (G) in
/-- Before the epilogue: the result in `rax` if the cache matches, the saved
registers in their slots. -/
structure CDone (s t : State) : Prop where
  L : Lay t (fb s) (stackArg s 3)
  wr : t.wr = frR s :: s.wr
  cs : ∀ r ∈ [Reg.r13, .r14, .r15], t.gpr r = s.gpr r
  rbx : t.mem.readW (off (fb s) sRbx) 64 = s.gpr .rbx
  rbp : t.mem.readW (off (fb s) sRbp) 64 = s.gpr .rbp
  r12 : t.mem.readW (off (fb s) sR12) 64 = s.gpr .r12
  out : validCache s → (t.gpr .rax).setWidth 32 = if verifyOut G s then 1 else 0

theorem restoreC_ok {s t : State} (D : CDone G s t) :
    WP isa (.block restoreRegs) t fun t' => t'.gpr .rsp = fb s ∧ t'.wr = (allocState frameBytes s).wr ∧
      (∀ r ∈ calleeSaved, (freedF t').gpr r = s.gpr r) ∧ (validCache s → (verifyK G).post s (freedF t')) := by
  refine WP.mono (WP.keep [.rbx, .rbp, .r12] (Q := fun t' => t'.mem = t.mem ∧ t'.gpr .rbx = s.gpr .rbx ∧
      t'.gpr .rbp = s.gpr .rbp ∧ t'.gpr .r12 = s.gpr .r12) ?_ rfl) fun t' ⟨⟨hm, h1, h2, h3⟩, k⟩ => ?_
  · xrun [restoreRegs, ea_sp, D.L.rsp, D.L.ld (d := sRbx) (by decide), D.L.ld (d := sRbp) (by decide),
      D.L.ld (d := sR12) (by decide), D.rbx, D.rbp, D.r12]
  have hsp : t'.gpr .rsp = fb s := (k.gpr (by decide)).trans D.L.rsp
  refine ⟨hsp, k.2.2.trans D.wr, fun r hr => ?_, ?_⟩
  · simp only [freedF, State.setReg]
    by_cases hr' : r = .rsp
    · subst hr'; simp only [ite_true, hsp, fb]; exact BitVec.sub_add_cancel _ _
    · simp only [hr', ite_false]
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact absurd rfl hr'
      · exact h3
      · rw [k.gpr (by decide)]; exact D.cs _ (by simp)
      · rw [k.gpr (by decide)]; exact D.cs _ (by simp)
      · rw [k.gpr (by decide)]; exact D.cs _ (by simp)
  · intro hc
    show (t'.gpr .rax).setWidth 32 = _
    rw [k.gpr (show Reg.rax ∉ [Reg.rbx, .rbp, .r12] by decide)]
    exact D.out hc

theorem written_getD {m : Mem} {out : Addr} {n : Nat} {r : BitVec 32} {o : Option (List Byte)}
    (h : Spec.Rsa.written m out n r o) : Spec.Rsa.bytesAt m out n = o.getD (Spec.RsaPss.zeros n) := by
  cases o with
  | none => exact h.2
  | some x => exact h.2

/-- The result: the check's, if the first `lo` bytes are zero. -/
theorem acc_out {lo : Nat} (hlo : lo ≤ 1) {x : List Byte} (hx : 1 ≤ x.length) {ve : Bool} {r : BitVec 64}
    (hr : r.setWidth 32 = if ve then 1 else 0) :
    (r &&& accV lo (x.getD 0 0)).setWidth 32 =
      if (x.take lo == Spec.RsaPss.zeros lo && ve) then 1 else 0 := by
  rw [BitVec.setWidth_and, hr]
  obtain ⟨a, t, rfl⟩ : ∃ a t, x = a :: t := by
    cases x with
    | nil => simp at hx
    | cons a t => exact ⟨a, t, rfl⟩
  rcases (show lo = 0 ∨ lo = 1 by omega) with rfl | rfl
  · cases ve <;> simp [accV, Spec.RsaPss.zeros]
  · by_cases ha : a = 0
    · subst ha; cases ve <;> simp [accV, Spec.RsaPss.zeros]
    · have ha' : (a = 0#8) ↔ False := ⟨ha, False.elim⟩
      cases ve <;> simp [accV, Spec.RsaPss.zeros, ha']

/-- The slots after `emBitsB`. -/
def vW (W : Nat → BitVec 64) (s : State) (eb : Nat) : Nat → BitVec 64 :=
  upd (upd (upd W 27 (BitVec.ofNat 64 eb)) 28 (BitVec.ofNat 64 (Spec.RsaPss.emLength eb))) 26
    (BitVec.ofNat 64 ((s.gpr .rsi).toNat - Spec.RsaPss.emLength eb))

/-- `emBits`, then the public-key operation's arguments. -/
theorem vprep_ok {s u : State} (hp : Pre G s) (L : Lay u (fb s) (stackArg s 3)) {V : Nat → Byte}
    {W : Nat → BitVec 64} (R : Rep u.mem (fb s) (stackArg s 3) V W) (hw : u.wr = frR s :: s.wr) (hrd : u.rd = s.rd)
    (hM : Frame (vwrR s) s.mem u.mem) (h17 : W 17 = s.gpr .rsi) (h19 : W 19 = s.gpr .rdx) (h20 : W 20 = s.gpr .rcx)
    (h22 : W 22 = stackArg s 4) (h38 : W 38 = s.gpr .r9) {x : Nat} (hx : x < 256) (h0 : x ≠ 0) (hax : u.gpr .rax = BitVec.ofNat 64 x) :
    WP isa (.block (emBitsB ++ pubArgsC)) u fun u' => Lay u' (fb s) (stackArg s 3) ∧
      Keep [.rdx, .rax, .r8, .rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] u u' ∧
      (∃ W', Rep u'.mem (fb s) (stackArg s 3) V W' ∧ (∀ i < 4, W' i = vArg s i) ∧
        (∀ i < nW, 4 ≤ i → W' i = vW W s (ebV (s.gpr .rsi).toNat x) i)) ∧
      u'.gpr .rdi = stackArg s 3 ∧ u'.gpr .rsi = s.gpr .rsi ∧ u'.gpr .rdx = stackArg s 5 ∧
      u'.gpr .rcx = stackArg s 6 ∧ u'.gpr .r8 = s.gpr .rdx ∧ u'.gpr .r9 = s.gpr .rcx ∧
      Frame (vwrR s) s.mem u'.mem := by
  have hk1 := hp.k1; have hk2 := hp.k2
  rw [WP.block_append_iff]
  refine WP.mono (WP.keepIn (by decide) (by exact Nat.zero_le 8) (emBitsB_ok L R (k := (s.gpr .rsi).toNat)
    (x := x) (by rw [h17, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by omega) hk2 hx h0 hax)) fun t ⟨⟨L3, k3, R3⟩, f3⟩ => ?_
  have hM3 := vframe_keep hp.toVPre hw L.rsp hM f3
  exact WP.mono (WP.keepIn (by decide) (by exact Nat.zero_le 8) (pubArgsC_ok hp L3 R3 (k3.2.2.trans hw)
    (k3.2.1.trans hrd) hM3 (by simp [upd, h17]) (by simp [upd, h19]) (by simp [upd, h20])
    (by simp [upd, h22]) (by simp [upd, h38])))
    fun t' ⟨⟨k4, L4, hW, a, b, c, d, e, f⟩, f4⟩ =>
      ⟨L4, k3.trans k4, hW, a, b, c, d, e, f, vframe_keep hp.toVPre (k3.2.2.trans hw) L3.rsp hM3 f4⟩

theorem codeC_ok {chkN : String} {chkC : Prog isa}
    (hvK : ∀ s, (chkK G).pre s → ∃ t s', Exec isa chkC s t s' ∧ abiPreserved s s' ∧ (chkK G).post s s')
    (hspK : SpSafe chkC) (hdK : chkC.x86_64Depth ≤ chkStack) (v : PublicImpl)
    {s : State} (h : (Spec.RsaPss.verifyPrecomputedContract G G abi verifyStack).pre s) :
    WP isa (verifyC chkN chkC v.name v.code) s fun s' => (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      (validCache s → (verifyK G).post s s') ∧ s'.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 := by
  have hp := pre_of G h
  have hF := vfb_toNat hp.toVPre
  have hk1 := hp.k1; have hk2 := hp.k2
  refine wp_frame (by have := hp.sp1; unfold verifyStack frameBytes at *; omega_arith) ?_
  rw [verifyCBody]
  simp only [seqs]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono_mx (by decide) (verifyPro_ok hp.toVPre) fun t1 ⟨k1, L1, R1, f1⟩ hmx1 => ?_
  have e1 : t1.mxcsr = s.mxcsr := hmx1
  have hM1 : Frame (vwrR s) s.mem t1.mem := f1.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., vframe_sub s⟩
  refine WP.mono_mx (by decide) (vn0_ok hp.toVPre L1 R1 (by simp [vproW, upd]) k1.2.1 hM1)
    fun t2 ⟨k2, hm2, hax2, hz2⟩ hmx2 => ?_
  have e2 : t2.mxcsr = s.mxcsr := hmx2.trans e1
  have L2 : Lay t2 (fb s) (stackArg s 3) := L1.congr (k2.gpr (by decide)) k2.2.2 (by rw [hm2])
  have R2 : Rep t2.mem (fb s) (stackArg s 3) _ (vproW s) := hm2 ▸ R1
  have hM2 : Frame (vwrR s) s.mem t2.mem := hm2 ▸ hM1
  have hw2 : t2.wr = frR s :: s.wr := k2.2.2.trans k1.2.2
  have hrd2 : t2.rd = s.rd := k2.2.1.trans k1.2.1
  have hcs2 : ∀ r ∈ [Reg.r13, .r14, .r15], t2.gpr r = s.gpr r := fun r hr => by
    have : r ∉ [Reg.rsi, .rax] := by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp
    rw [k2.gpr this, k1.gpr (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp)]
    simp only [allocState_gpr']; rw [ifn (by simp at hr; rcases hr with rfl | rfl | rfl <;> simp)]
  refine WP.seq (WP.mono (Q := fun (t3 : State) => CDone G s t3 ∧
      t3.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10) ?_
    fun t3 ⟨D, hm⟩ => WP.mono_mx (by decide) (restoreC_ok D) fun t' ⟨a, b, c, d⟩ hm' =>
      ⟨a, b, c, d, by rw [show (freedF t').mxcsr = t'.mxcsr from rfl, hm']; exact hm⟩)
  -- The modulus as `n₀ ‖ rest`.
  set n₀ := s.mem (s.gpr .rdi) with hn₀
  set rest := Spec.Rsa.bytesAt s.mem (s.gpr .rdi + 1) ((s.gpr .rsi).toNat - 1) with hrest
  have hnB : Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat = n₀ :: rest := bytesAt_cons _ _ (by omega_arith)
  have hrl : rest.length = (s.gpr .rsi).toNat - 1 := by simp [hrest, Spec.Rsa.bytesAt]
  refine WP.ite (M := isa) _ (show isa.eval .e t2 = _ from hz2) (fun hb => ?_) (fun hb => ?_)
  · -- `n₀ = 0`: refused.
    rw [decide_eq_true_eq] at hb
    have h0 : n₀ = 0 := BitVec.eq_of_toNat_eq hb
    refine WP.mono_mx (by decide) (vfail_done L2 R2 hw2 hcs2 (by simp [vproW, upd]) (by simp [vproW, upd])
      (by simp [vproW, upd]) ?_) fun _ D hm' => ⟨⟨D.L, D.wr, D.cs, D.rbx, D.rbp, D.r12, fun _ => D.out⟩,
        by rw [hm', e2]⟩
    rw [verifyOut, hnB, h0]; exact RsaPss.verify_zero ..
  rw [decide_eq_false_iff_not] at hb
  have h0 : n₀ ≠ 0 := fun h => hb (by rw [h]; rfl)
  have hl8 := RsaPss.log2_lt8 n₀
  set k := (s.gpr .rsi).toNat with hk
  set eb := ebV k n₀.toNat with heb_def
  set el := Spec.RsaPss.emLength eb with hel_def
  set lo := k - el with hlo_def
  have hlo : lo ≤ 1 := lo_le hl8 (by omega_arith)
  have heb : Spec.RsaPss.bitLength (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) k)) - 1 = eb := by
    rw [hnB, RsaPss.emBits_eq rest h0, hrl]; rfl
  have heb1 : 1 ≤ eb := by rw [heb_def]; unfold ebV; omega_arith
  have heb2 : eb ≤ Proof.RsaPss.maxEmBits := by
    rw [heb_def]; unfold ebV Proof.RsaPss.maxEmBits; omega_arith
  have hlok : lo + el = k := by
    rw [hlo_def, hel_def, heb_def]; unfold Spec.RsaPss.emLength ebV; omega_arith
  -- `emBits` and the public-key operation's arguments.
  refine WP.seq (WP.mono_mx (by decide) (vprep_ok hp L2 R2 hw2 hrd2 hM2 (by simp [vproW, upd])
    (by simp [vproW, upd]) (by simp [vproW, upd]) (by simp [vproW, upd]) (by simp [vproW, upd]) n₀.isLt hb hax2)
    fun t4 ⟨L4, k4, ⟨W4, R4, hW4a, hW4b⟩, hdi4, hsi4, hdx4, hcx4, h84, h94, hM4⟩ hmx4 => ?_)
  have e4 : t4.mxcsr = s.mxcsr := hmx4.trans e2
  have hw4 : t4.wr = frR s :: s.wr := k4.2.2.trans hw2
  have hrd4 : t4.rd = s.rd := k4.2.1.trans hrd2
  have g4 : ∀ j, j < nW → 4 ≤ j → j ≠ 26 → j ≠ 27 → j ≠ 28 → W4 j = vproW s j := fun j hj h4 a b c => by
    rw [hW4b j hj h4]; simp only [vW, upd]; rw [ifn a, ifn c, ifn b]
  -- The public-key operation.
  refine WP.seq (WP.mono (call_ok v hp L4.rsp hrd4 hw4 hM4
    (fun i hi => (R4.fr i (by unfold nW frameBytes; omega_arith)).trans (hW4a i hi)) hdi4 hsi4 hdx4 hcx4 h84 h94)
    fun t5 ⟨rd5, wr5, cs5, mx5, hM5, hk5, hout5⟩ => ?_)
  have R5 := R4.of_call L4.geo (m' := t5.mem) (rgs := [(0, k)]) (fun x hx hin => hk5 x (by
      rcases hin with hin | hin
      · refine .inr ⟨hin, ?_⟩
        have := hx _ (List.mem_singleton_self _)
        rwa [off_zero] at this
      · exact .inl hin)) (by
      intro p hp'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
      subst hp'; dsimp only; unfold oRsa; omega_arith)
  set V5 := fun o => if inR [(0, k)] o then t5.mem (off (stackArg s 3) o)
    else (fun o => s.mem (off (stackArg s 3) o)) o with hV5
  have L5 : Lay t5 (fb s) (stackArg s 3) := L4.of_rep' R4 R5 rfl (cs5 .rsp (by decide)) wr5
  -- `sAcc` and `checkEncoding`'s arguments.
  refine WP.seq (WP.mono_mx (by decide) (chkArgs_ok hp L5 R5 (wr5.trans hw4) (rd5.trans hrd4) hM5
    (lo := lo) (el := el) (eb := eb)
    ((g4 17 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (by simp [vproW, upd]))
    ((g4 22 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (by simp [vproW, upd]))
    (by rw [hW4b 26 (by decide) (by decide)]; simp only [vW, upd, ↓reduceIte]; try rfl)
    (by rw [hW4b 27 (by decide) (by decide)]; simp only [vW, upd, Nat.reduceEqDiff, ↓reduceIte]; try rfl)
    (by rw [hW4b 28 (by decide) (by decide)]; simp only [vW, upd, Nat.reduceEqDiff, ↓reduceIte]; try rfl)
    ((g4 37 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (by simp [vproW, upd])) hlo)
    fun t6 ⟨L6, k6, R6, hM6, hdi6, hsi6, hdx6, hcx6, h86, h96⟩ hmx6 => ?_)
  -- `checkEncoding`.
  refine WP.seq (WP.mono (ck_call hvK hspK hdK hp L6.rsp (k6.2.1.trans (rd5.trans hrd4))
    (k6.2.2.trans (wr5.trans hw4)) hM6 R6 ((R6.fr 0 (by decide)).trans (by simp [chkW, upd]))
    ((R6.fr 1 (by decide)).trans (by simp [chkW, upd])) hdi6 hsi6 hdx6 hcx6 h86 h96 (by omega_arith) heb1 heb2 rfl)
    fun t7 ⟨rd7, wr7, cs7, mx7, hM7, R7, hax7⟩ => ?_)
  have L7 : Lay t7 (fb s) (stackArg s 3) := L6.of_rep' R6 R7 rfl (cs7 .rsp (by decide)) wr7
  -- The result, if the first `lo` bytes are zero.
  refine WP.mono_mx (by decide) (WP.keep [.rax] (Q := fun y => y.mem = t7.mem ∧
      y.gpr .rax = t7.gpr .rax &&& accV lo (V5 0)) ?_ rfl) fun y ⟨⟨hm8, hax8⟩, k8⟩ hmx8 => ?_
  · xrun [ea_sp, L7.rsp, L7.ld (d := sAcc) (by decide), R7.rd (d := sAcc) 33 rfl (by decide)]
    simp [chkW, upd]
  have R8 := hm8 ▸ R7
  have w : ∀ j, 40 < j → j < nW → chkW W4 s lo (V5 0) j = vproW s j := fun j hj hj' => by
    simp only [chkW, upd]; rw [ifn (by omega_arith), ifn (by omega_arith), ifn (by omega_arith)]
    exact g4 j hj' (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
  refine ⟨⟨L7.congr (k8.gpr (by decide)) k8.2.2 (by rw [hm8]), k8.2.2.trans (wr7.trans (k6.2.2.trans
      (wr5.trans hw4))), fun r hr => ?_, ?_, ?_, ?_, fun hc => ?_⟩, ?_⟩
  · have h1 : r ∈ calleeSaved := by simp at hr; rcases hr with rfl | rfl | rfl <;> decide
    rw [k8.gpr (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp), cs7 r h1,
      k6.gpr (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp), cs5 r h1,
      k4.gpr (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp), hcs2 r hr]
  · rw [R8.rd (d := sRbx) 41 rfl (by decide), w 41 (by decide) (by decide)]; simp [vproW, upd]
  · rw [R8.rd (d := sRbp) 42 rfl (by decide), w 42 (by decide) (by decide)]; simp [vproW, upd]
  · rw [R8.rd (d := sR12) 43 rfl (by decide), w 43 (by decide) (by decide)]; simp [vproW, upd]
  · have hbx := written_getD (hout5 hc)
    set x := (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) k)
      (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .r9) k)).getD
        (Spec.RsaPss.zeros k) with hx
    have hxl : x.length = k := by rw [← hbx, bytesAt_length]
    have hin : ∀ o, o < k → inR [(0, k)] o := fun o ho =>
      ⟨_, List.mem_singleton_self _, by dsimp only; omega, by dsimp only; omega⟩
    have hb0 : V5 0 = x.getD 0 0 := by
      rw [← hbx, hV5]; dsimp only; rw [ifp (hin 0 (by omega_arith))]
      rw [List.getD_eq_getElem?_getD, Spec.Rsa.bytesAt, List.getElem?_map, List.getElem?_range (by omega_arith)]
      simp [off]
    have hem : Spec.Rsa.bytesAt t6.mem (off (stackArg s 3) lo) el = x.drop lo := by
      rw [← hbx]
      apply List.ext_getElem (by simp [Spec.Rsa.bytesAt]; omega_arith)
      intro i h1 h2
      simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at h1
      simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, List.getElem_drop, off_plus]
      rw [R6.scr _ (by unfold oRsa; omega_arith), hV5]; dsimp only
      rw [ifp (hin _ (by omega_arith))]
    rw [hem] at hax7
    rw [hax8, hb0, acc_out hlo (by omega_arith) hax7, verifyOut,
      RsaPss.verify_encode G heb (by rw [bytesAt_length, bytesAt_length])
        (by rw [bytesAt_length]; unfold Spec.RsaPss.emLength at *; omega_arith)]
    simp only [bytesAt_length]
    rfl
  · rw [hmx8, mx7, hmx6, mx5, e4]

end VG.Proof.RsaPss.X86_64.Pc
