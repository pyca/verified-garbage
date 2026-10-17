module

public import VerifiedGarbage.Proof.RsaOaep.AArch64.EncCall
public import VerifiedGarbage.Impl.RsaOaep.AArch64.Precomputed
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs

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
open VG.Proof.Pbkdf2.Md.AArch64 (Tier MdHash)
open VG.Proof.RsaPkcs1Enc.AArch64.Enc (popped_mem popped_sp popped_v popped_gpr_self popped_gpr_ne freed_mem freed_sp
  freed_v freed_gpr add_add)

variable {hs : List Hash} {Hl Gm : Hash} (hH : StreamOK Hl.stream) (hG : StreamOK Gm.stream)

include hH hG in
theorem encMain_ok {Hs Gs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = Hl.D)
    (hHv : Proof.Mgf1.Valid Hs) (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = Gm.D)
    (hGv : Proof.Mgf1.Valid Gs) (c : PdChecked) {L : ELay} (hL : L.Ok) (hP : c.stack ≤ L.P) (hP16 : 16 ≤ L.P)
    (hnH : Num hs L.hh.toNat Hl) (hnG : Num hs L.gh.toNat Gm) (hD : L.D = Hl.D) (hDG : L.DG = Gm.D)
    {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} (hp : PreOk L m₀) {t : State}
    (hc : Ctx L g vv m₀ t) {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep t.mem L.Q L.scr V W) (hS : Slots L W)
    (hk : 2 * Hl.D + 2 + L.ml.toNat ≤ L.k.toNat) :
    WP isa (Impl.RsaOaep.AArch64.Precomputed.encMain hs c.name c.code) t fun t' => Ctx L g vv m₀ t' ∧
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
  refine WP.seq (WP.mono (encEm_ok hH hHh hL hnH hP16 hD hc R hS hk) fun t5 ⟨hc5, V5, R5, E⟩ => ?_)
  have hl : ∀ {W' : Nat → BitVec 64}, Slots L W' → W' 4 = BitVec.ofNat 64 Hl.D := fun h => hD ▸ h.hsl.hlen
  have hm : ∀ {W' : Nat → BitVec 64}, Slots L W' → MSel W' L.gh.toNat Gm.D := fun h => hDG ▸ h.hsl.msel
  -- `DB` masked.
  refine WP.seq (WP.mono (dbArgs_ok (hc5.lay hL hP16 R5 hS.scr) R5 hk3 (hl hS) (by omega_arith) (by omega_arith) hk1024 [])
    fun t6 ⟨_, S6, R6⟩ => ?_)
  have hc6 := hc5.step hL hP16 S6 nil_ws
  have hS6 : Slots L (mW W L.scr 1 Hl.D (1 + Hl.D) (L.k.toNat - Hl.D - 1)) :=
    hS.of fun j _ _ h3 => mW_eq _ _ _ _ _ _ (by omega_arith)
  refine WP.seq (WP.mono (mgfXor_ok hnG hG hGh hGl hGv (hc6.lay hL hP16 R6 hS6.scr) R6 f4 (mW_args _ _ _ _ _ _) (hm hS6))
    fun t7 ⟨_, S7, V7, W7, R7, hW7, hV7⟩ => ?_)
  have hc7 := hc6.step hL hP16 S7 nil_ws
  have hS7 : Slots L W7 := hS6.of fun j _ h2 h3 => hW7 j (by unfold nW frameBytes; omega_arith) (by omega_arith) (by omega_arith)
  -- The seed masked.
  refine WP.seq (WP.mono (seedArgs_ok (hc7.lay hL hP16 R7 hS7.scr) R7 (by rw [hS7.k, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]) (hl hS7) (by omega_arith) (by omega_arith) hk1024 []) fun t8 ⟨_, S8, R8⟩ => ?_)
  have hc8 := hc7.step hL hP16 S8 nil_ws
  have hS8 : Slots L (mW W7 L.scr (1 + Hl.D) (L.k.toNat - Hl.D - 1) 1 Hl.D) :=
    hS7.of fun j _ _ h3 => mW_eq _ _ _ _ _ _ (by omega_arith)
  refine WP.seq (WP.mono (mgfXor_ok hnG hG hGh hGl hGv (hc8.lay hL hP16 R8 hS8.scr) R8 f2 (mW_args _ _ _ _ _ _) (hm hS8))
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

/-- `x11` all ones iff `mLen > k - 2 hLen - 2`. -/
theorem chkMsg_ok {D k mLen : Nat} (hk : W 21 = BitVec.ofNat 64 k) (hml : W 28 = BitVec.ofNat 64 mLen)
    (hl : W 4 = BitVec.ofNat 64 D) (hk' : k ≤ 1024) (hmL : mLen < 2 ^ 64) (hD : 2 * D + 2 ≤ k) :
    WP isa (.block chkMsg) u fun u' => Lay u' F S ∧ Step F S [] u u' ∧ u'.mem = u.mem ∧
      u'.gpr .x11 = if mLen ≤ k - (2 * D + 2) then 0 else BitVec.allOnes 64 := by
  have h168 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 168) 8 := Ly.ld (d := 168) (by decide)
  have h224 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 224) 8 := Ly.ld (d := 224) (by decide)
  have rk := R.rdK hk
  have rml := R.rd8 (d := 224) (k := 28) rfl (by decide) hml
  have h32 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 32) 8 := Ly.ld (d := 32) (by decide)
  have rl := R.rd8 (d := 32) (k := 4) rfl (by decide) hl
  have e2 : ∀ x : BitVec 64, x - BitVec.ofNat 64 D - BitVec.ofNat 64 D - BitVec.ofNat 64 2 =
      x - BitVec.ofNat 64 (2 * D + 2) := fun x => by
    rw [BitVec.sub_sub, BitVec.sub_sub, BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat,
      show D + (D + 2) = 2 * D + 2 by omega]
  refine WP.mono (Q := fun (u' : State) => u'.mem = u.mem ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧
      u'.v = u.v ∧ (∀ r ∈ preserved, r ≠ .x30 → u'.gpr r = u.gpr r) ∧
      u'.gpr .x11 = if mLen ≤ k - (2 * D + 2) then 0 else BitVec.allOnes 64) ?_
    fun u' ⟨hm, hrd, hwr, hsp, hv, hcs, x11⟩ =>
      ⟨Ly.congr hsp hwr (by rw [hm]), Step.blk _ hrd hwr hsp hv hcs hm, hm, x11⟩
  oaep_run [chkMsg, sK, sMsgLen, sHl, h168, h224, h32, Ly.sp, rk, rml, rl, e2, sbc_self, Offset.ofNat_sub_ofNat hD]
  refine ⟨trivial, trivial, trivial, trivial, trivial, cs_rfl, ?_⟩
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k - (2 * D + 2) < 2 ^ 64 by omega_arith),
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

theorem encBody_eq (hs : List Hash) (main : Prog isa) :
    encBodyWith hs main = .seq (.block encPrologue) (.seq (hashSetup hs 8 9) (.seq (.block chkK)
      (.ite (.nonzero .x .x11) encFail (.seq (.block chkMsg) (.ite (.nonzero .x .x11) encFail main))))) := rfl

/-- A stack argument, as the entry memory has it from the frame's base. -/
theorem arg_mem (DG P : Nat) (s : State) (j : Nat) :
    s.mem.readW ((lay DG P s).Q + BitVec.ofNat 64 (288 + 8 * j)) 64 = stackArg s j := by
  rw [stackArg, stackArgAddr, ← lay_Q DG P s, add_add]

theorem preOk_lay {DG P : Nat} {s : State} (h : (encSpec P).pre s) : PreOk (lay DG P s) s.mem := by
  have e6 : preW (lay DG P s) s.mem = stackArg s 6 := arg_mem DG P s 6
  have e7 : prlW (lay DG P s) s.mem = stackArg s 7 := arg_mem DG P s 7
  exact ⟨by rw [PRE, e6, e7]; rfl, rfl, by rw [e7]; exact (lay_pre (DG := DG) h).2.2.2.1, arg_mem DG P s 8,
    arg_mem DG P s 9⟩

theorem consistent_iff (DG P : Nat) (s : State) :
    Consistent (lay DG P s) s.mem ↔ Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) =
      some (Spec.Rsa.wordsAt s.mem (stackArg s 6) (stackArg s 7).toNat) := by
  have e6 : preW (lay DG P s) s.mem = stackArg s 6 := arg_mem DG P s 6
  have e7 : prlW (lay DG P s) s.mem = stackArg s 7 := arg_mem DG P s 7
  rw [Consistent, e6, e7]; rfl

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

/-- Our stack argument at `Q + d` (`hash` or `mgf1_hash`), as on entry. -/
theorem selAt {L : ELay} (hL : L.Ok) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
    (hc : Ctx L g vv m₀ t) (hp : PreOk L m₀) {j : Nat} (hj : j = 8 ∨ j = 9) :
    InRegions (t.rd ++ t.wr) (L.Q + BitVec.ofNat 64 (arg j)) 8 ∧
      t.mem.read (L.Q + BitVec.ofNat 64 (arg j)) 8 =
        BitVec.ofNat 64 (if j = 8 then L.hh else L.gh).toNat := by
  have hA := hp.al
  have := hL.nQa
  have ha : arg j = 288 + 8 * j := rfl
  refine ⟨⟨L.ARGS, List.mem_append_left _ (by rw [hc.rd]; simp),
    Offset.contains _ (show 288 ≤ arg j by omega) (by omega) (by omega)⟩, ?_⟩
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have k := arg_keep hL hc (d := arg j) (by omega) (by omega)
  rcases hj with rfl | rfl
  · exact k.trans hp.hh
  · exact k.trans hp.gh

/-- The hash functions' numbers and lengths to their slots, after the
prologue. -/
theorem encSetup_ok {hs : List Hash} {Hl Gm : Hash} {L : ELay} (hL : L.Ok) (hP16 : 16 ≤ L.P)
    (hnH : Num hs L.hh.toNat Hl) (hnG : Num hs L.gh.toNat Gm) (hDH : Hl.D < 65536) (hDG : Gm.D < 65536)
    {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} (hp : PreOk L m₀) {u : State}
    (hc : Ctx L g vv m₀ u) {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep u.mem L.Q L.scr V W)
    (hS : Prologued L W) :
    WP isa (hashSetup hs 8 9) u fun u' => Ctx L g vv m₀ u' ∧
      Rep u'.mem L.Q L.scr V (setW W L.hh.toNat Hl.D L.gh.toNat Gm.D) := by
  have Ly := hc.lay hL hP16 R hS.scr
  obtain ⟨ld8, v8⟩ := selAt hL hc hp (j := 8) (.inl rfl)
  refine WP.seq (WP.mono (selArg_ok hnH hDH Ly R (j := 8) (a := 2) (b := 4) (by decide) (by decide) (by decide)
    (by decide) (by decide) ld8 v8 []) fun u1 ⟨L1, S1, R1⟩ => ?_)
  have hc1 := hc.step hL hP16 S1 nil_ws
  obtain ⟨ld9, v9⟩ := selAt hL hc1 hp (j := 9) (.inr rfl)
  exact WP.mono (selArg_ok hnG hDG L1 R1 (j := 9) (a := 3) (b := 5) (by decide) (by decide) (by decide)
    (by decide) (by decide) ld9 v9 []) fun u2 ⟨_, S2, R2⟩ => ⟨hc1.step hL hP16 S2 nil_ws, R2⟩

/-- The hash functions' slots, with our arguments'. -/
theorem slots_setW {L : ELay} {W : Nat → BitVec 64} (hS : Prologued L W) {DH DG : Nat} (hDH : L.D = DH)
    (hDG : L.DG = DG) : Slots L (setW W L.hh.toNat DH L.gh.toNat DG) :=
  hS.slots (fun j h1 _ _ => setW_eq _ _ _ _ _ (by omega)) (hDH ▸ hDG ▸ setW_slots _ _ _ _ _)

/-- The tier's hash functions for the layout's numbers. -/
theorem tier_hs (t : Tier) {L : ELay} (hL : L.Ok) :
    ∃ vH vG : MdHash, Num (tierHs t) L.hh.toNat vH.H ∧ Num (tierHs t) L.gh.toNat vG.H ∧
      Spec.HashId.mgf1 L.hh.toNat = some vH.mgf.G ∧ Spec.HashId.mgf1 L.gh.toNat = some vG.mgf.G :=
  let ⟨vH, h1, h2⟩ := tier_num t hL.hhk
  let ⟨vG, g1, g2⟩ := tier_num t hL.ghk
  ⟨vH, vG, h1, g1, h2, g2⟩

theorem body_ok (t : Tier) (c : PdChecked) {P : Nat} (hP : c.stack ≤ P) (hP16 : 16 ≤ P) {s : State}
    (h : (encSpec P).pre s) :
    WP isa (encBodyWith (tierHs t) (Impl.RsaOaep.AArch64.Precomputed.encMain (tierHs t) c.name c.code)) (entered s)
      fun u => Ctx (lay (lenAt (tierHs t) (stackArg s 9).toNat) P s) s.gpr s.v s.mem u ∧
        ∃ Hs Gs, Spec.HashId.mgf1 (stackArg s 8).toNat = some Hs ∧ Spec.HashId.mgf1 (stackArg s 9).toNat = some Gs ∧
        (Consistent (lay (lenAt (tierHs t) (stackArg s 9).toNat) P s) s.mem →
          Spec.Rsa.written u.mem (s.gpr .x0) (s.gpr .x3).toNat ((u.gpr .x0).setWidth 32)
            (Spec.RsaOaep.encrypt Hs Gs (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
              (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat)
              (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)
              (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
              (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat))) := by
  have hL := lay_ok (DG := lenAt (tierHs t) (stackArg s 9).toNat) h
  have hpo := preOk_lay (DG := lenAt (tierHs t) (stackArg s 9).toNat) h
  have hp := prologue_ok (DG := lenAt (tierHs t) (stackArg s 9).toNat) h
  obtain ⟨L, hLL⟩ : ∃ L, lay (lenAt (tierHs t) (stackArg s 9).toNat) P s = L := ⟨_, rfl⟩
  have e0 : s.gpr .x0 = L.out := by rw [← hLL]; rfl
  have e2 : s.gpr .x2 = L.n := by rw [← hLL]; rfl
  have e3 : s.gpr .x3 = L.k := by rw [← hLL]; rfl
  have e4 : s.gpr .x4 = L.e := by rw [← hLL]; rfl
  have e5 : s.gpr .x5 = L.el := by rw [← hLL]; rfl
  have e6 : s.gpr .x6 = L.lab := by rw [← hLL]; rfl
  have e7 : s.gpr .x7 = L.labl := by rw [← hLL]; rfl
  have a0 : stackArg s 0 = L.msg := by rw [← hLL]; rfl
  have a1 : stackArg s 1 = L.ml := by rw [← hLL]; rfl
  have a2 : stackArg s 2 = L.sd := by rw [← hLL]; rfl
  have a3 : (stackArg s 3).toNat = L.D := by rw [← hLL]; rfl
  have a8 : stackArg s 8 = L.hh := by rw [← hLL]; rfl
  have a9 : stackArg s 9 = L.gh := by rw [← hLL]; rfl
  have hLDG : L.DG = lenAt (tierHs t) L.gh.toNat := by rw [← a9, ← hLL]; rfl
  rw [hLL] at hL hp hpo ⊢
  rw [e0, e2, e3, e4, e5, e6, e7, a0, a1, a2, a3, a8, a9]
  have hLP : L.P = P := by rw [← hLL]; rfl
  rw [← hLP] at hP hP16
  obtain ⟨vH, vG, hnH, hnG, hmH, hmG⟩ := tier_hs t hL
  have hHl := vH.mgf.len
  have hLD : L.D = vH.H.D := (hL.hsd _ hmH).trans hHl
  have hLDG' : L.DG = vG.H.D := hLDG.trans hnG.lenAt
  obtain ⟨-, hzF, -, hzDF, hD0⟩ := sizes vH.ok.stream
  have hD64 : vH.H.D ≤ 64 := Nat.le_trans hzDF hzF
  obtain ⟨-, gzF, -, gzDF, -⟩ := sizes vG.ok.stream
  have gD64 : vG.H.D ≤ 64 := Nat.le_trans gzDF gzF
  have hk1024 := hL.k1024
  have hk64 := hL.k64
  have hnB : (Spec.Rsa.bytesAt s.mem L.n L.k.toNat).length = L.k.toNat := by simp [Spec.Rsa.bytesAt]
  have hmB : (Spec.Rsa.bytesAt s.mem L.msg L.ml.toNat).length = L.ml.toNat := by simp [Spec.Rsa.bytesAt]
  have hsB : (Spec.Rsa.bytesAt s.mem L.sd L.D).length = vH.mgf.G.len := by
    simp [Spec.Rsa.bytesAt, hLD, hHl]
  have enone : 2 * vH.H.D + 2 + L.ml.toNat > L.k.toNat →
      Spec.RsaOaep.encrypt vH.mgf.G vG.mgf.G (Spec.Rsa.bytesAt s.mem L.n L.k.toNat)
        (Spec.Rsa.bytesAt s.mem L.e L.el.toNat) (Spec.Rsa.bytesAt s.mem L.lab L.labl.toNat)
        (Spec.Rsa.bytesAt s.mem L.msg L.ml.toNat) (Spec.Rsa.bytesAt s.mem L.sd L.D) = none := fun hgt =>
    encrypt_none (by rw [hnB, hmB, hHl]; omega_arith)
  rw [encBody_eq]
  refine WP.seq (WP.mono hp fun t₀ ⟨hc, _, hS⟩ => ?_)
  have R : Rep t₀.mem L.Q L.scr (fun o => t₀.mem (off L.scr o)) (fun j => word t₀.mem L.Q (8 * j)) :=
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  -- The hash functions' slots.
  refine WP.seq (WP.mono (encSetup_ok hL hP16 hnH hnG (by omega) (by omega) hpo hc R hS) fun t₁ ⟨hc1, R1⟩ => ?_)
  have hS1 := slots_setW hS hLD hLDG'
  have hk3 : setW (fun j => word t₀.mem L.Q (8 * j)) L.hh.toNat vH.H.D L.gh.toNat vG.H.D 21 =
      BitVec.ofNat 64 L.k.toNat := hS1.k.trans (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])
  have hl1 := hLD ▸ hS1.hsl.hlen
  refine WP.seq (WP.mono (chkK_ok (hc1.lay hL hP16 R1 hS1.scr) R1 hk3 hl1 hk1024 hD64)
    fun t2 ⟨_, S2, hm2, x11⟩ => ?_)
  have hc2 := hc1.step hL hP16 S2 nil_ws
  have R2 := hm2 ▸ R1
  refine WP.ite _ (eval_nonzero t2 .x11) (fun hb => ?_) (fun hb => ?_)
  · have hkD : L.k.toNat < 2 * vH.H.D + 2 := by
      by_contra hc'; rw [x11, ifp (by omega_arith)] at hb; exact absurd hb (by decide)
    refine WP.mono (fail_ok hL hP16 hc2 R2 hS1) fun u ⟨hcu, hw⟩ => ⟨hcu, _, _, hmH, hmG, fun _ => ?_⟩
    rw [enone (by omega_arith)]; exact hw
  · have hkD : 2 * vH.H.D + 2 ≤ L.k.toNat := by
      by_contra hc'; rw [x11, ifn (by omega_arith)] at hb; exact absurd hb (by decide)
    refine WP.seq (WP.mono (chkMsg_ok (hc2.lay hL hP16 R2 hS1.scr) R2 hk3
      (hS1.ml.trans (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])) hl1 hk1024 L.ml.isLt hkD)
      fun t3 ⟨_, S3, hm3, x11'⟩ => ?_)
    have hc3 := hc2.step hL hP16 S3 nil_ws
    have R3 := hm3 ▸ R2
    refine WP.ite _ (eval_nonzero t3 .x11) (fun hb' => ?_) (fun hb' => ?_)
    · have hmk : L.k.toNat - (2 * vH.H.D + 2) < L.ml.toNat := by
        by_contra hc'; rw [x11', ifp (by omega_arith)] at hb'; exact absurd hb' (by decide)
      refine WP.mono (fail_ok hL hP16 hc3 R3 hS1) fun u ⟨hcu, hw⟩ => ⟨hcu, _, _, hmH, hmG, fun _ => ?_⟩
      rw [enone (by omega_arith)]; exact hw
    · have hmk : L.ml.toNat ≤ L.k.toNat - (2 * vH.H.D + 2) := by
        by_contra hc'; rw [x11', ifn (by omega_arith)] at hb'; exact absurd hb' (by decide)
      refine WP.mono (encMain_ok vH.ok.stream vG.ok.stream vH.mgf.hash hHl (mgf_valid vH.mgf) vG.mgf.hash vG.mgf.len
        (mgf_valid vG.mgf) c hL hP hP16 hnH hnG hLD hLDG' hpo hc3 R3 hS1 (by omega_arith))
        fun u ⟨hcu, hw⟩ => ⟨hcu, _, _, hmH, hmG, fun hq => ?_⟩
      rw [encrypt_some hsB (by rw [hnB, hmB]; omega_arith), hnB, hmB, hHl, hLD]
      exact hw hq

/-! ## The whole function -/

/-- The stack the contract gives. -/
theorem spec_sp {P : Nat} {s : State} (h : (encSpec P).pre s) : P + 288 ≤ s.sp.toNat :=
  (lay_pre (DG := 0) h).2.2.2.2

/-- The postcondition, from what the body wrote. -/
theorem result_ok {DG P : Nat} {s : State} {t : State} {Hs Gs : Spec.Mgf1.Hash}
    (hH : Spec.HashId.mgf1 (stackArg s 8).toNat = some Hs) (hG : Spec.HashId.mgf1 (stackArg s 9).toNat = some Gs)
    (hw : Consistent (lay DG P s) s.mem →
      Spec.Rsa.written t.mem (s.gpr .x0) (s.gpr .x3).toNat ((t.gpr .x0).setWidth 32)
      (Spec.RsaOaep.encrypt Hs Gs (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat))) :
    (encSpec P).post s t := by
  sig_post [Spec.RsaOaep.encryptAnyContract, Spec.RsaOaep.encryptAnySig, AArch64.abi,
    AArch64.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq]
  intro H G hH' hG' hq
  rw [hH] at hH'; rw [hG] at hG'
  cases hH'; cases hG'
  exact hw ((consistent_iff DG P s).2 hq)

/-- `vg_rsa_oaep_encrypt_precomputed` meets the shared contract and the calling convention. -/
theorem enc_ok (t : Tier) (c : PdChecked) {P : Nat} (hP : c.stack ≤ P) (hP16 : 16 ≤ P) {s : State}
    (h : (encSpec P).pre s) :
    WP isa (Impl.RsaOaep.AArch64.Precomputed.encrypt (tierHs t) c.name c.code) s fun s' =>
      abiPreserved s s' ∧ (encSpec P).post s s' := by
  have hsp := spec_sp h
  refine WP.frame (by omega_arith) (WP.alloc (by decide) ?_ ?_)
  · show 272 ≤ (s.sp - 16).toNat
    rw [BitVec.toNat_sub_of_le (by show 16 ≤ s.sp.toNat; omega_arith)]
    show 272 ≤ s.sp.toNat - 16
    omega_arith
  · show WP isa (encBodyWith (tierHs t) (Impl.RsaOaep.AArch64.Precomputed.encMain (tierHs t) c.name c.code))
      (entered s) _
    refine WP.mono (body_ok t c hP hP16 h) fun u' ⟨hc', Hs, Gs, hmH, hmG, hw'⟩ => ?_
    have hsp' : (freed frameBytes u').sp =
        (lay (lenAt (tierHs t) (stackArg s 9).toNat) P s).Q + BitVec.ofNat 64 272 := by
      rw [freed_sp, hc'.sp]; rfl
    refine ⟨⟨fun r hr => ?_, ?_, fun r hr => ?_⟩, ?_⟩
    · by_cases h30 : r = .x30
      · subst r
        rw [popped_gpr_self, freed_mem, hsp']; exact hc'.lr
      · rw [popped_gpr_ne _ h30, freed_gpr]
        exact hc'.cs r hr h30
    · rw [popped_sp, hsp']
      show (lay (lenAt (tierHs t) (stackArg s 9).toNat) P s).Q + BitVec.ofNat 64 272 + BitVec.ofNat 64 16 = s.sp
      rw [add_add]; exact lay_Q _ _ s
    · rw [popped_v, freed_v]
      exact hc'.vs r hr
    · refine result_ok (DG := lenAt (tierHs t) (stackArg s 9).toNat) hmH hmG fun hq => ?_
      rw [popped_mem, freed_mem, popped_gpr_ne _ (by decide), freed_gpr]
      exact hw' hq

end VG.Proof.RsaOaep.AArch64.Enc
