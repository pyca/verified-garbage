module

public import VerifiedGarbage.Proof.RsaOaep.AArch64.EncCall
public import VerifiedGarbage.Impl.RsaOaep.AArch64.Precomputed
public import VerifiedGarbage.Proof.RsaOaep.AArch64.EncEntry
public import VerifiedGarbage.Proof.RsaOaep.Encode
import VerifiedGarbage.Proof.RsaOaep.AArch64.EncMain
import VerifiedGarbage.Proof.RsaOaep.AArch64.Args
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncCorrect
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# RSAES-OAEP encryption on AArch64: correctness

After the checks (`encMain_ok`): `EM` written, `DB` masked with MGF1 of the
seed and the seed with MGF1 of the masked `DB`, then the precomputed public
operation of it into `out`. The frames, the prologue and the checks of `k`
and the message's length, with zeros to `out` if either fails: `enc_ok`,
against the shared contract, whose result is encryption's if `pre` holds the
values for `n`.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.AArch64.Enc

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Impl.RsaOaep.AArch64.Mgf1 (seqs)
open VG.Proof.Mgf1 (ifp ifn)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (StreamOK)
open VG.Proof.RsaPkcs1Sig.AArch64 (PdChecked)
open VG.Proof.RsaOaep.AArch64.Dec (entered)
open VG.Proof.RsaPkcs1Enc.AArch64.Enc (popped_mem popped_sp popped_v popped_gpr_self popped_gpr_ne freed_mem freed_sp
  freed_v freed_gpr add_add)

variable {Hl Gm : Hash} (hH : StreamOK Hl.stream) (hG : StreamOK Gm.stream)

include hH hG in
theorem encMain_ok {Hs Gs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = Hl.D)
    (hHv : Proof.Mgf1.Valid Hs) (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = Gm.D)
    (hGv : Proof.Mgf1.Valid Gs) (c : PdChecked) {L : ELay} (hL : L.Ok) (hP : c.stack ≤ L.P) (hP16 : 16 ≤ L.P)
    (hD : L.D = Hl.D) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} (hp : PreOk L m₀) {t : State}
    (hc : Ctx L g vv m₀ t) {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep t.mem L.Q L.scr V W) (hS : Slots L W)
    (hk : 2 * Hl.D + 2 + L.ml.toNat ≤ L.k.toNat) :
    WP isa (Impl.RsaOaep.AArch64.Precomputed.encMain Hl Gm c.name c.code) t fun t' => Ctx L g vv m₀ t' ∧
      (Consistent L m₀ → Spec.Rsa.written t'.mem L.out L.k.toNat ((t'.gpr .x0).setWidth 32)
        (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt m₀ L.n L.k.toNat) (Spec.Rsa.bytesAt m₀ L.e L.el.toNat)
          (emOf Gs Hl.D L.k.toNat L.ml.toNat (Spec.Rsa.bytesAt m₀ L.sd Hl.D)
            (Hs.hash (Spec.Rsa.bytesAt m₀ L.lab L.labl.toNat)) (Spec.Rsa.bytesAt m₀ L.msg L.ml.toNat)))) := by
  obtain ⟨-, hzF, -, hzDF, hD0⟩ := sizes hH
  have hD64 : Hl.D ≤ 64 := Nat.le_trans hzDF hzF
  replace hD0 : 0 < Hl.D := hD0
  have hk1024 := hL.k1024
  have cSt : oSt = 3072 := rfl
  have cR : oRsa = 8192 := rfl
  have hk3 : W 21 = BitVec.ofNat 64 L.k.toNat := by rw [hS.k, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have f4 : MFit 1 Hl.D (1 + Hl.D) (L.k.toNat - Hl.D - 1) :=
    ⟨by rw [cSt]; omega_arith, by rw [cSt]; omega_arith, by omega_arith, by omega_arith, by omega_arith⟩
  have f2 : MFit (1 + Hl.D) (L.k.toNat - Hl.D - 1) 1 Hl.D :=
    ⟨by rw [cSt]; omega_arith, by rw [cSt]; omega_arith, by omega_arith, by omega_arith, by omega_arith⟩
  unfold Impl.RsaOaep.AArch64.Precomputed.encMain seqs seqs seqs seqs seqs seqs
  -- `EM` before masking.
  refine WP.seq (WP.mono (encEm_ok hH hHh hL hP16 hD hc R hS hk) fun t5 ⟨hc5, V5, R5, E⟩ => ?_)
  -- `DB` masked.
  refine WP.seq (WP.mono (dbArgs_ok (hc5.lay hL hP16 R5 hS.scr) R5 hk3 (by omega_arith) (by omega_arith) hk1024 [])
    fun t6 ⟨_, S6, R6⟩ => ?_)
  have hc6 := hc5.step hL hP16 S6 nil_ws
  have hS6 : Slots L (mW W L.scr 1 Hl.D (1 + Hl.D) (L.k.toNat - Hl.D - 1)) :=
    hS.of fun j _ _ h3 => mW_eq _ _ _ _ _ _ (by omega_arith)
  refine WP.seq (WP.mono (mgfXor_ok hG hGh hGl hGv (hc6.lay hL hP16 R6 hS6.scr) R6 f4 (mW_args _ _ _ _ _ _))
    fun t7 ⟨_, S7, V7, W7, R7, hW7, hV7⟩ => ?_)
  have hc7 := hc6.step hL hP16 S7 nil_ws
  have hS7 : Slots L W7 := hS6.of fun j _ h2 h3 => hW7 j (by unfold nW frameBytes; omega_arith) (by omega_arith) (by omega_arith)
  -- The seed masked.
  refine WP.seq (WP.mono (seedArgs_ok (hc7.lay hL hP16 R7 hS7.scr) R7 (by rw [hS7.k, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]) (by omega_arith) (by omega_arith) hk1024 []) fun t8 ⟨_, S8, R8⟩ => ?_)
  have hc8 := hc7.step hL hP16 S8 nil_ws
  have hS8 : Slots L (mW W7 L.scr (1 + Hl.D) (L.k.toNat - Hl.D - 1) 1 Hl.D) :=
    hS7.of fun j _ _ h3 => mW_eq _ _ _ _ _ _ (by omega_arith)
  refine WP.seq (WP.mono (mgfXor_ok hG hGh hGl hGv (hc8.lay hL hP16 R8 hS8.scr) R8 f2 (mW_args _ _ _ _ _ _))
    fun t9 ⟨_, S9, V9, W9, R9, hW9, hV9⟩ => ?_)
  have hc9 := hc8.step hL hP16 S9 nil_ws
  have hS9 : Slots L W9 := hS8.of fun j _ h2 h3 => hW9 j (by unfold nW frameBytes; omega_arith) (by omega_arith) (by omega_arith)
  -- The call.
  refine WP.seq ?_
  rw [Impl.RsaOaep.AArch64.Precomputed.pubArgs, pubArgs_eq, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (pubW_ok hL hP16 hc9 R9 hS9) fun t10 ⟨hc10, R10⟩ => ?_
  have hS10 : Slots L (pubW L W9) := hS9.of fun j h1 _ _ => by
    simp only [pubW, upd]; rw [ifn (by omega_arith), ifn (by omega_arith)]
  refine WP.mono (pubR_ok hL hP16 hc10 R10 hS10) fun t₁₁ ⟨hc₁₁, hm₁₁, hr₁₁⟩ => ?_
  refine WP.mono (loads_ok hL hP16 hc₁₁ hp hr₁₁) fun t11 ⟨hc11, hm11', hr11⟩ => ?_
  have R11 : Rep t11.mem L.Q L.scr V9 (pubW L W9) := hm11' ▸ hm₁₁ ▸ R10
  refine WP.mono (pd_call c hL hP hc11 hp hr11 R11 ⟨by simp [pubW, upd], by simp [pubW, upd]⟩)
    fun t12 ⟨hc12, hout⟩ => ⟨hc12, fun hq => ?_⟩
  -- `EM` masked.
  have hlhl : (Hs.hash (Spec.Rsa.bytesAt m₀ L.lab L.labl.toNat)).length = Hl.D := by rw [hHv.2, hHl]
  have hml : (Spec.Rsa.bytesAt m₀ L.msg L.ml.toNat).length = L.ml.toNat := by simp [Spec.Rsa.bytesAt]
  have hsdl : (Spec.Rsa.bytesAt m₀ L.sd Hl.D).length = Hl.D := by simp [Spec.Rsa.bytesAt]
  have e1 : L.k.toNat - (Hl.D + 1) = L.k.toNat - Hl.D - 1 := by omega_arith
  have hm : ∀ o, o < L.k.toNat → mOut o := fun o ho => (mOut_iff o).mpr (.inl (by unfold oSt; omega_arith))
  have hsrc : srcB V7 (1 + Hl.D) (L.k.toNat - Hl.D - 1) =
      srcB (mixV V5 (Spec.Mgf1.mgf1 Gs (srcB V5 1 Hl.D) (L.k.toNat - Hl.D - 1)) (1 + Hl.D)
        (L.k.toNat - Hl.D - 1)) (1 + Hl.D) (L.k.toNat - Hl.D - 1) :=
    List.map_congr_left fun i hi => by
      have := List.mem_range.mp hi
      exact hV7 _ (by unfold oRsa; omega_arith) (hm _ (by omega_arith))
  have hlist : Spec.Rsa.bytesAt t11.mem (L.scr + BitVec.ofNat 64 0) L.k.toNat =
      emOf Gs Hl.D L.k.toNat L.ml.toNat (Spec.Rsa.bytesAt m₀ L.sd Hl.D)
        (Hs.hash (Spec.Rsa.bytesAt m₀ L.lab L.labl.toNat)) (Spec.Rsa.bytesAt m₀ L.msg L.ml.toNat) := by
    unfold emOf
    rw [← em_mask hGv (V₁ := V5) (by omega_arith) hsdl (by
        simp only [List.length_append, List.length_cons, hlhl, hml, Spec.RsaOaep.zeros, List.length_replicate]; omega_arith)
      E.z0 E.sd (E.db hlhl hml hk)]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    have hi' := List.mem_range.mp hi
    rw [BitVec.add_zero, show L.scr + BitVec.ofNat 64 i = off L.scr i from rfl, R11.scr i (by omega_arith),
      hV9 _ (by omega_arith) (hm _ hi'), hsrc]
    exact mixV_congr _ _ _ (hV7 _ (by omega_arith) (hm _ hi'))
  rw [hlist] at hout
  exact hout hq

/-! ## The checks -/

section
variable {u : State} {F S : Addr} (Ly : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
  (R : Rep u.mem F S V W)
include Ly R

/-- `x11` all ones iff `k < 2 hLen + 2`. -/
theorem chkK_ok {H : Hash} {k : Nat} (hk : W 21 = BitVec.ofNat 64 k) (hk' : k ≤ 1024) (hD : 2 * H.D + 2 < 65536) :
    WP isa (.block (chkK H)) u fun u' => Lay u' F S ∧ Step F S [] u u' ∧ u'.mem = u.mem ∧
      u'.gpr .x11 = if 2 * H.D + 2 ≤ k then 0 else BitVec.allOnes 64 := by
  have h168 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 168) 8 := Ly.ld (d := 168) (by decide)
  have rk := R.rdK hk
  refine WP.mono (Q := fun (u' : State) => u'.mem = u.mem ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧
      u'.v = u.v ∧ (∀ r ∈ preserved, r ≠ .x30 → u'.gpr r = u.gpr r) ∧
      u'.gpr .x11 = if 2 * H.D + 2 ≤ k then 0 else BitVec.allOnes 64) ?_
    fun u' ⟨hm, hrd, hwr, hsp, hv, hcs, x11⟩ =>
      ⟨Ly.congr hsp hwr (by rw [hm]), Step.blk _ hrd hwr hsp hv hcs hm, hm, x11⟩
  oaep_run [chkK, sK, h168, Ly.sp, rk, imm16 hD, sbc_self]
  refine ⟨trivial, trivial, trivial, trivial, trivial, cs_rfl, ?_⟩
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega_arith),
    Nat.mod_eq_of_lt (show 2 * H.D + 2 < 2 ^ 64 by omega_arith)]

/-- `x11` all ones iff `mLen > k - 2 hLen - 2`. -/
theorem chkMsg_ok {H : Hash} {k mLen : Nat} (hk : W 21 = BitVec.ofNat 64 k) (hml : W 28 = BitVec.ofNat 64 mLen)
    (hk' : k ≤ 1024) (hmL : mLen < 2 ^ 64) (hD : 2 * H.D + 2 ≤ k) :
    WP isa (.block (chkMsg H)) u fun u' => Lay u' F S ∧ Step F S [] u u' ∧ u'.mem = u.mem ∧
      u'.gpr .x11 = if mLen ≤ k - (2 * H.D + 2) then 0 else BitVec.allOnes 64 := by
  have h168 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 168) 8 := Ly.ld (d := 168) (by decide)
  have h224 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 224) 8 := Ly.ld (d := 224) (by decide)
  have rk := R.rdK hk
  have rml := R.rd8 (d := 224) (k := 28) rfl (by decide) hml
  refine WP.mono (Q := fun (u' : State) => u'.mem = u.mem ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧
      u'.v = u.v ∧ (∀ r ∈ preserved, r ≠ .x30 → u'.gpr r = u.gpr r) ∧
      u'.gpr .x11 = if mLen ≤ k - (2 * H.D + 2) then 0 else BitVec.allOnes 64) ?_
    fun u' ⟨hm, hrd, hwr, hsp, hv, hcs, x11⟩ =>
      ⟨Ly.congr hsp hwr (by rw [hm]), Step.blk _ hrd hwr hsp hv hcs hm, hm, x11⟩
  oaep_run [chkMsg, sK, sMsgLen, h168, h224, Ly.sp, rk, rml, sbc_self, show 2 * H.D + 2 < 4096 by omega_arith,
    Offset.ofNat_sub_ofNat hD]
  refine ⟨trivial, trivial, trivial, trivial, trivial, cs_rfl, ?_⟩
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k - (2 * H.D + 2) < 2 ^ 64 by omega_arith),
    Nat.mod_eq_of_lt hmL]

/-- Zeros to `out`, and 0. -/
theorem encFail_ok {o : Addr} {k : Nat} (ho : W 19 = o) (hk : W 21 = BitVec.ofNat 64 k) (hk0 : 0 < k)
    (hk1 : k ≤ 1024) (hw : Covers [⟨o, k⟩] u.wr) (hnw : o.toNat + k ≤ 2 ^ 64) (ha : Apart F S ⟨o, k⟩) :
    WP isa encFail u fun u' => Lay u' F S ∧ Step F S [⟨o, k⟩] u u' ∧ (∀ i < k, u'.mem (off o i) = 0) ∧
      u'.gpr .x0 = 0 := by
  refine WP.seq (WP.mono (zeroOut_ok Ly R ho hk hk0 hk1 hw hnw ha) fun u1 ⟨L1, S1, _, _, z1⟩ => ?_)
  refine WP.mono (Q := fun (u' : State) => u'.mem = u1.mem ∧ u'.rd = u1.rd ∧ u'.wr = u1.wr ∧ u'.sp = u1.sp ∧
      u'.v = u1.v ∧ (∀ r ∈ preserved, r ≠ .x30 → u'.gpr r = u1.gpr r) ∧ u'.gpr .x0 = 0) ?_
    fun u' ⟨hm, hrd, hwr, hsp, hv, hcs, x0⟩ => ⟨L1.congr hsp hwr (by rw [hm]),
      S1.trans (Step.blk _ hrd hwr hsp hv hcs hm), fun i hi => by rw [hm]; exact z1 i hi, x0⟩
  oaep_run []
  refine ⟨trivial, trivial, trivial, trivial, trivial, cs_rfl, ?_⟩
  decide

end

/-! ## The body -/

/-- `out`, apart from the frame, our working space and the 16 bytes below
the frame. -/
theorem out_apart {L : ELay} (hL : L.Ok) (hP : 16 ≤ L.P) : Apart L.Q L.scr L.OUT where
  dF := by
    have hf := ELay.Ok.sub_stk (L := L) (d := 0) (n := frameBytes) (by decide)
    rw [BitVec.add_zero] at hf
    exact hL.kO.symm.sub_right hf
  dS := hL.oS.sub_right hL.ours_scr
  dK := hL.kO.symm.sub_right (Dec.sub_trans (ELay.Ok.ret_low (L := L) hP) ELay.Ok.low_stk)

theorem encBody_eq (main : Prog isa) :
    encBodyWith Hl main = .seq (.block (encPrologue ++ chkK Hl)) (.ite (.nonzero .x .x11) encFail
      (.seq (.block (chkMsg Hl)) (.ite (.nonzero .x .x11) encFail main))) := rfl

/-- A stack argument, as the entry memory has it from the frame's base. -/
theorem arg_mem (D P : Nat) (s : State) (j : Nat) :
    s.mem.readW ((lay D P s).Q + BitVec.ofNat 64 (288 + 8 * j)) 64 = stackArg s j := by
  rw [stackArg, stackArgAddr, ← lay_Q D P s, add_add]

theorem preOk_lay {Hs Gs : Spec.Mgf1.Hash} {P : Nat} {s : State} (h : (encSpec Hs Gs P).pre s) :
    PreOk (lay Hs.len P s) s.mem := by
  have e5 : preW (lay Hs.len P s) s.mem = stackArg s 5 := arg_mem Hs.len P s 5
  have e6 : prlW (lay Hs.len P s) s.mem = stackArg s 6 := arg_mem Hs.len P s 6
  exact ⟨by rw [PRE, e5, e6]; rfl, rfl, by rw [e6]; exact (lay_pre h).2.2.2.1⟩

theorem consistent_iff (D P : Nat) (s : State) :
    Consistent (lay D P s) s.mem ↔ Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) =
      some (Spec.Rsa.wordsAt s.mem (stackArg s 5) (stackArg s 6).toNat) := by
  have e5 : preW (lay D P s) s.mem = stackArg s 5 := arg_mem D P s 5
  have e6 : prlW (lay D P s) s.mem = stackArg s 6 := arg_mem D P s 6
  rw [Consistent, e5, e6]; rfl

/-- Zeros to `out` and 0 from a state with our arguments in their slots. -/
theorem fail_ok {L : ELay} (hL : L.Ok) (hP : 16 ≤ L.P) {g : Reg → BitVec 64} {vv : VReg → BitVec 128}
    {m₀ : Mem} {t : State} (hc : Ctx L g vv m₀ t) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem L.Q L.scr V W) (hS : Slots L W) :
    WP isa encFail t fun t' => Ctx L g vv m₀ t' ∧
      Spec.Rsa.written t'.mem L.out L.k.toNat ((t'.gpr .x0).setWidth 32) none := by
  have hk64 := hL.k64
  refine WP.mono (encFail_ok (hc.lay hL hP R hS.scr) R hS.out (by rw [hS.k, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]) (by omega_arith) hL.k1024
    (Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨L.OUT, by rw [hc.wr]; simp, 0, (BitVec.add_zero _).symm, by simp⟩)
    hL.bO (out_apart hL hP)) fun t' ⟨_, S', hz, x0⟩ =>
      ⟨hc.step hL hP S' fun r hr => by rw [List.mem_singleton.mp hr]; exact fun _ h => h, by rw [x0]; rfl, ?_⟩
  simp only [Spec.Rsa.bytesAt]
  exact (List.map_congr_left fun i hi => hz i (List.mem_range.mp hi)).trans
    (by rw [List.map_const', List.length_range])

include hH hG in
theorem body_ok {Hs Gs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = Hl.D)
    (hHv : Proof.Mgf1.Valid Hs) (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = Gm.D)
    (hGv : Proof.Mgf1.Valid Gs) (c : PdChecked) {P : Nat} (hP : c.stack ≤ P) (hP16 : 16 ≤ P) {s : State}
    (h : (encSpec Hs Gs P).pre s) :
    WP isa (encBodyWith Hl (Impl.RsaOaep.AArch64.Precomputed.encMain Hl Gm c.name c.code)) (entered s) fun u =>
      Ctx (lay Hs.len P s) s.gpr s.v s.mem u ∧ (Consistent (lay Hs.len P s) s.mem →
      Spec.Rsa.written u.mem (lay Hs.len P s).out (lay Hs.len P s).k.toNat ((u.gpr .x0).setWidth 32)
        (Spec.RsaOaep.encrypt Hs Gs (Spec.Rsa.bytesAt s.mem (lay Hs.len P s).n (lay Hs.len P s).k.toNat)
          (Spec.Rsa.bytesAt s.mem (lay Hs.len P s).e (lay Hs.len P s).el.toNat)
          (Spec.Rsa.bytesAt s.mem (lay Hs.len P s).lab (lay Hs.len P s).labl.toNat)
          (Spec.Rsa.bytesAt s.mem (lay Hs.len P s).msg (lay Hs.len P s).ml.toNat)
          (Spec.Rsa.bytesAt s.mem (lay Hs.len P s).sd Hs.len))) := by
  have hL := lay_ok h
  have hpo := preOk_lay h
  obtain ⟨-, hzF, -, hzDF, hD0⟩ := sizes hH
  have hD64 : Hl.D ≤ 64 := Nat.le_trans hzDF hzF
  have hk1024 := hL.k1024
  have hk64 := hL.k64
  have hp := prologue_ok h
  obtain ⟨L, hLL⟩ : ∃ L, lay Hs.len P s = L := ⟨_, rfl⟩
  rw [hLL] at hL hp hk1024 hk64 hpo ⊢
  have hLP : L.P = P := by rw [← hLL]; rfl
  have hLD : L.D = Hl.D := by rw [← hLL]; exact hHl
  rw [← hLP] at hP hP16
  have hnB : (Spec.Rsa.bytesAt s.mem L.n L.k.toNat).length = L.k.toNat := by simp [Spec.Rsa.bytesAt]
  have hmB : (Spec.Rsa.bytesAt s.mem L.msg L.ml.toNat).length = L.ml.toNat := by simp [Spec.Rsa.bytesAt]
  have hsB : (Spec.Rsa.bytesAt s.mem L.sd Hs.len).length = Hs.len := by simp [Spec.Rsa.bytesAt]
  have enone : 2 * Hl.D + 2 + L.ml.toNat > L.k.toNat →
      Spec.RsaOaep.encrypt Hs Gs (Spec.Rsa.bytesAt s.mem L.n L.k.toNat) (Spec.Rsa.bytesAt s.mem L.e L.el.toNat)
        (Spec.Rsa.bytesAt s.mem L.lab L.labl.toNat) (Spec.Rsa.bytesAt s.mem L.msg L.ml.toNat)
        (Spec.Rsa.bytesAt s.mem L.sd Hs.len) = none := fun hgt =>
    encrypt_none (by rw [hnB, hmB, hHl]; omega_arith)
  rw [encBody_eq]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono hp fun t ⟨hc, _, hS⟩ => ?_
  have R : Rep t.mem L.Q L.scr (fun o => t.mem (off L.scr o)) (fun j => word t.mem L.Q (8 * j)) :=
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  have hk3 : (fun j => word t.mem L.Q (8 * j)) 21 = BitVec.ofNat 64 L.k.toNat :=
    hS.k.trans (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])
  refine WP.mono (chkK_ok (H := Hl) (hc.lay hL hP16 R hS.scr) R hk3 hk1024 (by omega_arith))
    fun t1 ⟨_, S1, hm1, x11⟩ => ?_
  have hc1 := hc.step hL hP16 S1 nil_ws
  have R1 : Rep t1.mem L.Q L.scr (fun o => t.mem (off L.scr o)) (fun j => word t.mem L.Q (8 * j)) := hm1 ▸ R
  refine WP.ite _ (eval_nonzero t1 .x11) (fun hb => ?_) (fun hb => ?_)
  · have hkD : L.k.toNat < 2 * Hl.D + 2 := by
      by_contra hc'; rw [x11, ifp (by omega_arith)] at hb; exact absurd hb (by decide)
    refine WP.mono (fail_ok hL hP16 hc1 R1 hS) fun u ⟨hcu, hw⟩ => ⟨hcu, fun _ => ?_⟩
    rw [enone (by omega_arith)]; exact hw
  · have hkD : 2 * Hl.D + 2 ≤ L.k.toNat := by
      by_contra hc'; rw [x11, ifn (by omega_arith)] at hb; exact absurd hb (by decide)
    refine WP.seq (WP.mono (chkMsg_ok (H := Hl) (hc1.lay hL hP16 R1 hS.scr) R1 hk3
      (hS.ml.trans (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])) hk1024 L.ml.isLt hkD) fun t2 ⟨_, S2, hm2, x11'⟩ => ?_)
    have hc2 := hc1.step hL hP16 S2 nil_ws
    have R2 : Rep t2.mem L.Q L.scr (fun o => t.mem (off L.scr o)) (fun j => word t.mem L.Q (8 * j)) := hm2 ▸ R1
    refine WP.ite _ (eval_nonzero t2 .x11) (fun hb' => ?_) (fun hb' => ?_)
    · have hmk : L.k.toNat - (2 * Hl.D + 2) < L.ml.toNat := by
        by_contra hc'; rw [x11', ifp (by omega_arith)] at hb'; exact absurd hb' (by decide)
      refine WP.mono (fail_ok hL hP16 hc2 R2 hS) fun u ⟨hcu, hw⟩ => ⟨hcu, fun _ => ?_⟩
      rw [enone (by omega_arith)]; exact hw
    · have hmk : L.ml.toNat ≤ L.k.toNat - (2 * Hl.D + 2) := by
        by_contra hc'; rw [x11', ifn (by omega_arith)] at hb'; exact absurd hb' (by decide)
      refine WP.mono (encMain_ok hH hG hHh hHl hHv hGh hGl hGv c hL hP hP16 hLD hpo hc2 R2 hS (by omega_arith))
        fun u ⟨hcu, hw⟩ => ⟨hcu, fun hq => ?_⟩
      rw [encrypt_some hsB (by rw [hnB, hmB]; omega_arith), hnB, hmB, hHl]
      exact hw hq

/-! ## The whole function -/

/-- The stack the contract gives. -/
theorem spec_sp {Hs Gs : Spec.Mgf1.Hash} {P : Nat} {s : State} (h : (encSpec Hs Gs P).pre s) :
    P + 288 ≤ s.sp.toNat :=
  (lay_pre h).2.2.2.2

/-- The postcondition, from what the body wrote. -/
theorem result_ok {Hs Gs : Spec.Mgf1.Hash} {P : Nat} {s : State} {t : State}
    (hw : Consistent (lay Hs.len P s) s.mem →
      Spec.Rsa.written t.mem (lay Hs.len P s).out (lay Hs.len P s).k.toNat ((t.gpr .x0).setWidth 32)
      (Spec.RsaOaep.encrypt Hs Gs (Spec.Rsa.bytesAt s.mem (lay Hs.len P s).n (lay Hs.len P s).k.toNat)
        (Spec.Rsa.bytesAt s.mem (lay Hs.len P s).e (lay Hs.len P s).el.toNat)
        (Spec.Rsa.bytesAt s.mem (lay Hs.len P s).lab (lay Hs.len P s).labl.toNat)
        (Spec.Rsa.bytesAt s.mem (lay Hs.len P s).msg (lay Hs.len P s).ml.toNat)
        (Spec.Rsa.bytesAt s.mem (lay Hs.len P s).sd Hs.len))) :
    (encSpec Hs Gs P).post s t := by
  sig_post [Spec.RsaOaep.encryptPrecomputedContract, Spec.RsaOaep.encryptPrecomputedSig, AArch64.abi,
    AArch64.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq]
  intro hq
  exact hw ((consistent_iff Hs.len P s).2 hq)

include hH hG in
/-- `vg_rsa_oaep_<H>_mgf1_<G>_encrypt` meets the shared contract and the calling convention. -/
theorem enc_ok {Hs Gs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = Hl.D)
    (hHv : Proof.Mgf1.Valid Hs) (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = Gm.D)
    (hGv : Proof.Mgf1.Valid Gs) (c : PdChecked) {P : Nat} (hP : c.stack ≤ P) (hP16 : 16 ≤ P) {s : State}
    (h : (encSpec Hs Gs P).pre s) :
    WP isa (Impl.RsaOaep.AArch64.Precomputed.encrypt Hl Gm c.name c.code) s fun s' =>
      abiPreserved s s' ∧ (encSpec Hs Gs P).post s s' := by
  have hsp := spec_sp h
  refine WP.frame (by omega_arith) (WP.alloc (by decide) ?_ ?_)
  · show 272 ≤ (s.sp - 16).toNat
    rw [BitVec.toNat_sub_of_le (by show 16 ≤ s.sp.toNat; omega_arith)]
    show 272 ≤ s.sp.toNat - 16
    omega_arith
  · show WP isa (encBodyWith Hl (Impl.RsaOaep.AArch64.Precomputed.encMain Hl Gm c.name c.code)) (entered s) _
    refine WP.mono (body_ok hH hG hHh hHl hHv hGh hGl hGv c hP hP16 h) fun u' ⟨hc', hw'⟩ => ?_
    have hsp' : (freed frameBytes u').sp = (lay Hs.len P s).Q + BitVec.ofNat 64 272 := by
      rw [freed_sp, hc'.sp]; rfl
    refine ⟨⟨fun r hr => ?_, ?_, fun r hr => ?_⟩, ?_⟩
    · by_cases h30 : r = .x30
      · subst r
        rw [popped_gpr_self, freed_mem, hsp']; exact hc'.lr
      · rw [popped_gpr_ne _ h30, freed_gpr]
        exact hc'.cs r hr h30
    · rw [popped_sp, hsp']
      show (lay Hs.len P s).Q + BitVec.ofNat 64 272 + BitVec.ofNat 64 16 = s.sp
      rw [add_add]; exact lay_Q _ _ s
    · rw [popped_v, freed_v]
      exact hc'.vs r hr
    · refine result_ok fun hq => ?_
      rw [popped_mem, freed_mem, popped_gpr_ne _ (by decide), freed_gpr]
      exact hw' hq

end VG.Proof.RsaOaep.AArch64.Enc
