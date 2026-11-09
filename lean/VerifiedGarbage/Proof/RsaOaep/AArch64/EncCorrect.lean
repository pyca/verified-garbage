module

public import VerifiedGarbage.Proof.RsaOaep.AArch64.EncCall
public import VerifiedGarbage.Impl.RsaOaep.AArch64.Precomputed
public import VerifiedGarbage.Proof.HashTable.AArch64
public import VerifiedGarbage.Proof.RsaOaep.AArch64.EncEntry
public import VerifiedGarbage.Proof.RsaOaep.Encode
import VerifiedGarbage.Proof.RsaOaep.AArch64.EncMain
import VerifiedGarbage.Proof.RsaOaep.AArch64.LabelT
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
operation of it into `out`. The frames, the prologue, the branch on the
digest length of the label's hash function (the table `hash`), and the
checks of `k` and the message's length, with zeros to `out` if either fails:
`enc_ok`, against the shared contract, whose result is encryption's if `pre`
holds the values for `n`.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.AArch64.Enc

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Impl.RsaOaep.AArch64.Mgf1 (seqs)
open VG.Proof.Mgf1 (ifp ifn)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash Stream)
open VG.Impl.RsaOaep.AArch64.Mgf1.Table (Fns)
open VG.Proof.Pbkdf2.Md.AArch64 (MdHash)
open VG.Proof.HashTable.AArch64 (tables fnsOf Coh tabOK_of held_tableOf hashAt_tableOf)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (StreamOK)
open VG.Proof.RsaPkcs1Sig.AArch64 (PdChecked)
open VG.Proof.RsaOaep.AArch64.Dec (entered)
open VG.Proof.RsaPkcs1Enc.AArch64.Enc (popped_mem popped_sp popped_v popped_gpr_self popped_gpr_ne freed_mem freed_sp
  freed_v freed_gpr add_add)

variable {Hl : Hash} {Gm : Stream} (hH : StreamOK Hl.stream) (hG : StreamOK Gm) {f : Fns}

include hH hG in
theorem encMain_ok {Hs Gs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = Hl.D)
    (hHv : Proof.Mgf1.Valid Hs) (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = Gm.D)
    (hGv : Proof.Mgf1.Valid Gs) (c : PdChecked) {L : ELay} (hL : L.Ok) (hP : c.stack ≤ L.P) (hP16 : 16 ≤ L.P)
    (hD : L.D = Hl.D) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} (hp : PreOk L m₀) {t : State}
    (hc : Ctx L g vv m₀ t) {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep t.mem L.Q L.scr V W) (hS : Slots L W)
    (hk : 2 * Hl.D + 2 + L.ml.toNat ≤ L.k.toNat) (okL : Table.TabOK Hl.stream f t.syms)
    (hmL : Table.TabMem Hl.stream t.syms (tabLW L m₀) m₀)
    (hDL : m₀.readW (tabLW L m₀ + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 Hl.stream.D)
    (ok : Table.TabOK Gm f t.syms) (hm : Table.TabMem Gm t.syms (tabW L m₀) m₀)
    (hDm : m₀.readW (tabW L m₀ + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 Gm.D) :
    WP isa (Impl.RsaOaep.AArch64.Precomputed.encMain Hl f c.name c.code) t fun t' => Ctx L g vv m₀ t' ∧
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
  have f4 : MFit 1 Hl.D (1 + Hl.D) (L.k.toNat - Hl.D - 1) :=
    ⟨by rw [cSt]; omega_arith, by rw [cSt]; omega_arith, by omega_arith, by omega_arith, by omega_arith⟩
  have f2 : MFit (1 + Hl.D) (L.k.toNat - Hl.D - 1) 1 Hl.D :=
    ⟨by rw [cSt]; omega_arith, by rw [cSt]; omega_arith, by omega_arith, by omega_arith, by omega_arith⟩
  unfold Impl.RsaOaep.AArch64.Precomputed.encMain seqs seqs seqs seqs seqs seqs
  -- `EM` before masking.
  refine WP.seq (WP.mono (Table.wp_sy (encEm_ok hH hHh hL hP16 hD hc R hS hk (tabL_of hL hP16 hc hp okL hmL hDL)))
    fun t5 ⟨⟨hc5, V5, R5, E⟩, sy5⟩ => ?_)
  have hS5 : Slots L (upd W 32 (tabLW L m₀)) := hS.of fun j _ h2 _ => by simp only [upd]; rw [ifn (by omega_arith)]
  have hk3 : (upd W 32 (tabLW L m₀)) 21 = BitVec.ofNat 64 L.k.toNat := by
    rw [hS5.k, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  -- `DB` masked.
  refine WP.seq (WP.mono (Table.wp_sy (dbArgs_ok (hc5.lay hL hP16 R5 hS5.scr) R5 hk3 (by omega_arith) (by omega_arith)
      hk1024 []))
    fun t6 ⟨⟨_, S6, R6⟩, sy6⟩ => ?_)
  have hc6 := hc5.step hL hP16 S6 nil_ws
  have hS6 : Slots L (mW (upd W 32 (tabLW L m₀)) L.scr 1 Hl.D (1 + Hl.D) (L.k.toNat - Hl.D - 1)) :=
    hS5.of fun j _ _ h3 => mW_eq _ _ _ _ _ _ (by omega_arith)
  have sy6' : t6.syms = t.syms := sy6.trans sy5
  have T6 := tab_of hL hP16 hc6 hp (sy6' ▸ ok) (sy6' ▸ hm) hDm
  refine WP.seq (WP.mono (Table.wp_sy (Table.mgfXorT_ok hG hGh hGl hGv (by decide) T6 (hc6.lay hL hP16 R6 hS6.scr) R6
      f4 (mW_args _ _ _ _ _ _)))
    fun t7 ⟨⟨_, S7, V7, W7, R7, hW7, hV7⟩, sy7⟩ => ?_)
  have hc7 := hc6.step hL hP16 S7 nil_ws
  have hS7 : Slots L W7 := hS6.of fun j _ h2 h3 => hW7 j (by unfold nW frameBytes; omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith)
  -- The seed masked.
  refine WP.seq (WP.mono (Table.wp_sy (seedArgs_ok (hc7.lay hL hP16 R7 hS7.scr) R7 (by rw [hS7.k, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]) (by omega_arith) (by omega_arith) hk1024 [])) fun t8 ⟨⟨_, S8, R8⟩, sy8⟩ => ?_)
  have hc8 := hc7.step hL hP16 S8 nil_ws
  have hS8 : Slots L (mW W7 L.scr (1 + Hl.D) (L.k.toNat - Hl.D - 1) 1 Hl.D) :=
    hS7.of fun j _ _ h3 => mW_eq _ _ _ _ _ _ (by omega_arith)
  have sy8' : t8.syms = t.syms := sy8.trans (sy7.trans sy6')
  have T8 := tab_of hL hP16 hc8 hp (sy8' ▸ ok) (sy8' ▸ hm) hDm
  refine WP.seq (WP.mono (Table.mgfXorT_ok hG hGh hGl hGv (by decide) T8 (hc8.lay hL hP16 R8 hS8.scr) R8 f2
      (mW_args _ _ _ _ _ _))
    fun t9 ⟨_, S9, V9, W9, R9, hW9, hV9⟩ => ?_)
  have hc9 := hc8.step hL hP16 S9 nil_ws
  have hS9 : Slots L W9 := hS8.of fun j _ h2 h3 => hW9 j (by unfold nW frameBytes; omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith)
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

theorem encBody_eq (main : Nat → Prog isa) :
    encBodyWith main = .seq (.block encPrologue) (.seq (.block (tabSlot 8)) (.seq (.block lenLoad)
      (byLen (fun d => encChecks (ofLen d) (main d)) lens))) := rfl

/-- The checks for a digest length, which is all they use of the hash
function's shape. -/
theorem encChecks_D {G G' : Hash} (h : G.D = G'.D) (main : Prog isa) : encChecks G main = encChecks G' main := by
  simp only [encChecks, chkK, chkMsg, h]

theorem encMain_D {G G' : Hash} (h : G.D = G'.D) (f : Fns) (pubN : String) (pubC : Prog isa) :
    Impl.RsaOaep.AArch64.Precomputed.encMain G f pubN pubC = Impl.RsaOaep.AArch64.Precomputed.encMain G' f pubN pubC := by
  simp only [Impl.RsaOaep.AArch64.Precomputed.encMain, encEm, copySeed, copyLh, dbArgs, seedArgs, h]

/-- A stack argument, as the entry memory has it from the frame's base. -/
theorem arg_mem (D P : Nat) (s : State) (j : Nat) :
    s.mem.readW ((lay D P s).Q + BitVec.ofNat 64 (288 + 8 * j)) 64 = stackArg s j := by
  rw [stackArg, stackArgAddr, ← lay_Q D P s, add_add]

theorem tabW_lay (D P : Nat) (s : State) : tabW (lay D P s) s.mem = stackArg s 9 := arg_mem D P s 9

theorem tabLW_lay (D P : Nat) (s : State) : tabLW (lay D P s) s.mem = stackArg s 8 := arg_mem D P s 8

theorem preOk_lay {Hs : Spec.Mgf1.Hash} {ts : List FnTable} {P : Nat} {s : State} (h : (encSpec ts P).pre s)
    (hH : Spec.HashTable.hashAt 64 s.mem (stackArg s 8) = some Hs) : PreOk (lay Hs.len P s) s.mem := by
  have e6 : preW (lay Hs.len P s) s.mem = stackArg s 6 := arg_mem Hs.len P s 6
  have e7 : prlW (lay Hs.len P s) s.mem = stackArg s 7 := arg_mem Hs.len P s 7
  exact ⟨by rw [PRE, TABJ, TABJ, e6, e7, show tabJ (lay Hs.len P s) s.mem 8 = stackArg s 8 from tabLW_lay _ _ _,
    show tabJ (lay Hs.len P s) s.mem 9 = stackArg s 9 from tabW_lay _ _ _]; rfl, rfl,
    by rw [e7]; exact (lay_pre h hH).2.2.2.1⟩

theorem consistent_iff (D P : Nat) (s : State) :
    Consistent (lay D P s) s.mem ↔ Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) =
      some (Spec.Rsa.wordsAt s.mem (stackArg s 6) (stackArg s 7).toNat) := by
  have e6 : preW (lay D P s) s.mem = stackArg s 6 := arg_mem D P s 6
  have e7 : prlW (lay D P s) s.mem = stackArg s 7 := arg_mem D P s 7
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

include hH hG in
theorem body_ok {Hs Gs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = Hl.D)
    (hHv : Proof.Mgf1.Valid Hs) (hHm : Hs ∈ Proof.Pbkdf2.Md.AArch64.mdHashes)
    (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = Gm.D)
    (hGv : Proof.Mgf1.Valid Gs) (c : PdChecked) {P : Nat} (hP : c.stack ≤ P) (hP16 : 16 ≤ P) {ts : List FnTable}
    {s : State} (h : (encSpec ts P).pre s) (hHa : Spec.HashTable.hashAt 64 s.mem (stackArg s 8) = some Hs)
    (okL : Table.TabOK Hl.stream f s.syms) (hmL : Table.TabMem Hl.stream s.syms (stackArg s 8) s.mem)
    (hDL : s.mem.readW (stackArg s 8 + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 Hl.stream.D)
    (ok : Table.TabOK Gm f s.syms) (hm : Table.TabMem Gm s.syms (stackArg s 9) s.mem)
    (hDm : s.mem.readW (stackArg s 9 + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 Gm.D) :
    WP isa (encBodyWith fun d => Impl.RsaOaep.AArch64.Precomputed.encMain (ofLen d) f c.name c.code) (entered s)
      fun u => Ctx (lay Hs.len P s) s.gpr s.v s.mem u ∧ (Consistent (lay Hs.len P s) s.mem →
      Spec.Rsa.written u.mem (lay Hs.len P s).out (lay Hs.len P s).k.toNat ((u.gpr .x0).setWidth 32)
        (Spec.RsaOaep.encrypt Hs Gs (Spec.Rsa.bytesAt s.mem (lay Hs.len P s).n (lay Hs.len P s).k.toNat)
          (Spec.Rsa.bytesAt s.mem (lay Hs.len P s).e (lay Hs.len P s).el.toNat)
          (Spec.Rsa.bytesAt s.mem (lay Hs.len P s).lab (lay Hs.len P s).labl.toNat)
          (Spec.Rsa.bytesAt s.mem (lay Hs.len P s).msg (lay Hs.len P s).ml.toNat)
          (Spec.Rsa.bytesAt s.mem (lay Hs.len P s).sd Hs.len))) := by
  have hL := lay_ok h hHa
  have hpo := preOk_lay h hHa
  obtain ⟨-, hzF, -, hzDF, hD0⟩ := sizes hH
  have hD64 : Hl.D ≤ 64 := Nat.le_trans hzDF hzF
  have hk1024 := hL.k1024
  have hk64 := hL.k64
  have hp := prologue_ok h hHa
  have hDl : Hl.stream.D ∈ lens := by
    show Hl.D ∈ lens
    rw [← hHl]; exact mem_lens hHm
  have e9 := tabW_lay Hs.len P s
  have e8 := tabLW_lay Hs.len P s
  obtain ⟨L, hLL⟩ : ∃ L, lay Hs.len P s = L := ⟨_, rfl⟩
  rw [hLL] at e9 e8
  rw [← e9] at hm hDm
  rw [← e8] at hmL hDL
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
  refine WP.seq (WP.mono (Table.wp_sy hp) fun t ⟨⟨hc, _, hS⟩, sy⟩ => ?_)
  have R : Rep t.mem L.Q L.scr (fun o => t.mem (off L.scr o)) (fun j => word t.mem L.Q (8 * j)) :=
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  -- The address of the table of the label's hash function to its slot, and its digest length to `x16`.
  have TL := tabL_of hL hP16 hc hpo (sy ▸ okL) (sy ▸ hmL) hDL
  refine WP.seq (WP.mono (Table.wp_sy (tabSlot_ok (by decide) (hc.lay hL hP16 R hS.scr) R TL))
    fun ta ⟨⟨La, Sa, Ra, _⟩, sya⟩ => ?_)
  have TLa := TL.step Sa sya
  refine WP.seq (WP.mono (Table.wp_sy (lenLoad_ok La Ra (by simp [upd]) TLa.rdD (TLa.mem _ (Frame.refl _ _)).2.1))
    fun tb ⟨⟨Sb, hmb, h16, _⟩, syb⟩ => ?_)
  refine byLen_ok (F := L.Q) (S := L.scr) hDl (by decide) (mem_lens_lt hDl) h16 fun t₀ Sc hmc syc _ => ?_
  show WP isa (encChecks (ofLen Hl.stream.D) (Impl.RsaOaep.AArch64.Precomputed.encMain (ofLen Hl.stream.D) f c.name
    c.code)) t₀ _
  rw [encChecks_D (G := ofLen Hl.stream.D) (G' := Hl) rfl, encMain_D (G := ofLen Hl.stream.D) (G' := Hl) rfl]
  unfold encChecks seqs seqs
  have hc₀ := ((hc.step hL hP16 Sa nil_ws).step hL hP16 Sb nil_ws).step hL hP16 Sc nil_ws
  have R₀ : Rep t₀.mem L.Q L.scr (fun o => t.mem (off L.scr o)) (upd (fun j => word t.mem L.Q (8 * j)) 32 (tabLW L s.mem)) :=
    (hmc.trans hmb) ▸ Ra
  have hS₀ : Slots L (upd (fun j => word t.mem L.Q (8 * j)) 32 (tabLW L s.mem)) :=
    hS.of fun j _ h2 _ => by simp only [upd]; rw [ifn (by omega_arith)]
  have sy₀ : t₀.syms = s.syms := syc.trans (syb.trans (sya.trans sy))
  have hk3 : (upd (fun j => word t.mem L.Q (8 * j)) 32 (tabLW L s.mem)) 21 = BitVec.ofNat 64 L.k.toNat :=
    hS₀.k.trans (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])
  refine WP.seq (WP.mono (Table.wp_sy (chkK_ok (H := Hl) (hc₀.lay hL hP16 R₀ hS₀.scr) R₀ hk3 hk1024 (by omega_arith)))
    fun t1 ⟨⟨_, S1, hm1, x11⟩, sy1⟩ => ?_)
  have hc1 := hc₀.step hL hP16 S1 nil_ws
  have R1 := hm1 ▸ R₀
  refine WP.ite _ (eval_nonzero t1 .x11) (fun hb => ?_) (fun hb => ?_)
  · have hkD : L.k.toNat < 2 * Hl.D + 2 := by
      by_contra hc'; rw [x11, ifp (by omega_arith)] at hb; exact absurd hb (by decide)
    refine WP.mono (fail_ok hL hP16 hc1 R1 hS₀) fun u ⟨hcu, hw⟩ => ⟨hcu, fun _ => ?_⟩
    rw [enone (by omega_arith)]; exact hw
  · have hkD : 2 * Hl.D + 2 ≤ L.k.toNat := by
      by_contra hc'; rw [x11, ifn (by omega_arith)] at hb; exact absurd hb (by decide)
    refine WP.seq (WP.mono (Table.wp_sy (chkMsg_ok (H := Hl) (hc1.lay hL hP16 R1 hS₀.scr) R1 hk3
      (hS₀.ml.trans (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])) hk1024 L.ml.isLt hkD))
      fun t2 ⟨⟨_, S2, hm2, x11'⟩, sy2⟩ => ?_)
    have hc2 := hc1.step hL hP16 S2 nil_ws
    have R2 := hm2 ▸ R1
    refine WP.ite _ (eval_nonzero t2 .x11) (fun hb' => ?_) (fun hb' => ?_)
    · have hmk : L.k.toNat - (2 * Hl.D + 2) < L.ml.toNat := by
        by_contra hc'; rw [x11', ifp (by omega_arith)] at hb'; exact absurd hb' (by decide)
      refine WP.mono (fail_ok hL hP16 hc2 R2 hS₀) fun u ⟨hcu, hw⟩ => ⟨hcu, fun _ => ?_⟩
      rw [enone (by omega_arith)]; exact hw
    · have hmk : L.ml.toNat ≤ L.k.toNat - (2 * Hl.D + 2) := by
        by_contra hc'; rw [x11', ifn (by omega_arith)] at hb'; exact absurd hb' (by decide)
      have sy' : t2.syms = s.syms := sy2.trans (sy1.trans sy₀)
      refine WP.mono (encMain_ok hH hG hHh hHl hHv hGh hGl hGv c hL hP hP16 hLD hpo hc2 R2 hS₀ (by omega_arith)
          (sy' ▸ okL) (sy' ▸ hmL) hDL (sy' ▸ ok) (sy' ▸ hm) hDm)
        fun u ⟨hcu, hw⟩ => ⟨hcu, fun hq => ?_⟩
      rw [encrypt_some hsB (by rw [hnB, hmB]; omega_arith), hnB, hmB, hHl]
      exact hw hq

/-! ## The whole function -/

/-- The stack the contract gives. -/
theorem spec_sp {ts : List FnTable} {P : Nat} {s : State} (h : (encSpec ts P).pre s) :
    P + 288 ≤ s.sp.toNat := by
  enc_pre at h
  exact h.1

/-- The postcondition, from what the body wrote with `Hs` and `Gs`, the hash
functions the tables name. -/
theorem result_ok {Hs Gs : Spec.Mgf1.Hash} {ts : List FnTable} {P : Nat} {s : State} {t : State}
    (hH : Spec.HashTable.hashAt 64 s.mem (stackArg s 8) = some Hs)
    (hG : Spec.HashTable.hashAt 64 s.mem (stackArg s 9) = some Gs)
    (hw : Consistent (lay Hs.len P s) s.mem →
      Spec.Rsa.written t.mem (lay Hs.len P s).out (lay Hs.len P s).k.toNat ((t.gpr .x0).setWidth 32)
      (Spec.RsaOaep.encrypt Hs Gs (Spec.Rsa.bytesAt s.mem (lay Hs.len P s).n (lay Hs.len P s).k.toNat)
        (Spec.Rsa.bytesAt s.mem (lay Hs.len P s).e (lay Hs.len P s).el.toNat)
        (Spec.Rsa.bytesAt s.mem (lay Hs.len P s).lab (lay Hs.len P s).labl.toNat)
        (Spec.Rsa.bytesAt s.mem (lay Hs.len P s).msg (lay Hs.len P s).ml.toNat)
        (Spec.Rsa.bytesAt s.mem (lay Hs.len P s).sd Hs.len))) :
    (encSpec ts P).post s t := by
  sig_post [Spec.RsaOaep.encryptTablesContract, Spec.RsaOaep.encryptTablesSig,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
    AArch64.abi, AArch64.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq]
  intro H' G' hH' hG' hq
  obtain rfl : Hs = H' := Option.some.inj (hH.symm.trans hH')
  obtain rfl : Gs = G' := Option.some.inj (hG.symm.trans hG')
  exact hw ((consistent_iff Hs.len P s).2 hq)

/-- `vg_rsa_oaep_encrypt_precomputed` meets the shared contract and the
calling convention, with both hash functions the tables of `vs`. -/
theorem enc_ok {vs : List MdHash} (hc : Coh vs) (c : PdChecked) {P : Nat} (hP : c.stack ≤ P)
    (hP16 : 16 ≤ P) {s : State} (h : (encSpec (tables vs) P).pre s) :
    WP isa (Impl.RsaOaep.AArch64.Precomputed.encrypt (fnsOf vs) c.name c.code) s fun s' =>
      abiPreserved s s' ∧ (encSpec (tables vs) P).post s s' := by
  have hsp := spec_sp h
  obtain ⟨⟨T₁, hT₁, hheld₁⟩, ⟨T, hT, hheld⟩, hpw⟩ := spec_tab h
  obtain ⟨w₁, hw₁, rfl⟩ := List.mem_map.mp hT₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  obtain ⟨hmL, hixL, hDL⟩ := held_tableOf hheld₁
  obtain ⟨hm, hix, hDm⟩ := held_tableOf hheld
  have okL := tabOK_of hc hpw hw₁
  have ok := tabOK_of hc hpw hw
  have hHa := hashAt_tableOf hixL
  have hGa := hashAt_tableOf hix
  refine WP.frame (by omega_arith) (WP.alloc (by decide) ?_ ?_)
  · show 272 ≤ (s.sp - 16).toNat
    rw [BitVec.toNat_sub_of_le (by show 16 ≤ s.sp.toNat; omega_arith)]
    show 272 ≤ s.sp.toNat - 16
    omega_arith
  · show WP isa (encBodyWith fun d => Impl.RsaOaep.AArch64.Precomputed.encMain (ofLen d) (fnsOf vs) c.name c.code)
      (entered s) _
    refine WP.mono (body_ok w₁.ok.stream w.ok.stream w₁.mgf.hash w₁.mgf.len (mgf_valid w₁.mgf) w₁.mgf.mem
      w.mgf.hash w.mgf.len (mgf_valid w.mgf) c hP hP16 h hHa okL hmL hDL ok hm hDm)
      fun u' ⟨hc', hw'⟩ => ?_
    have hsp' : (freed frameBytes u').sp = (lay w₁.mgf.G.len P s).Q + BitVec.ofNat 64 272 := by
      rw [freed_sp, hc'.sp]; rfl
    refine ⟨⟨fun r hr => ?_, ?_, fun r hr => ?_⟩, ?_⟩
    · by_cases h30 : r = .x30
      · subst r
        rw [popped_gpr_self, freed_mem, hsp']; exact hc'.lr
      · rw [popped_gpr_ne _ h30, freed_gpr]
        exact hc'.cs r hr h30
    · rw [popped_sp, hsp']
      show (lay w₁.mgf.G.len P s).Q + BitVec.ofNat 64 272 + BitVec.ofNat 64 16 = s.sp
      rw [add_add]; exact lay_Q _ _ s
    · rw [popped_v, freed_v]
      exact hc'.vs r hr
    · refine result_ok hHa hGa fun hq => ?_
      rw [popped_mem, freed_mem, popped_gpr_ne _ (by decide), freed_gpr]
      exact hw' hq

end VG.Proof.RsaOaep.AArch64.Enc
