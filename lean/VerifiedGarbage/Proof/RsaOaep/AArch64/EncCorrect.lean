import VerifiedGarbage.Proof.RsaOaep.AArch64.EncCall

/-!
# RSAES-OAEP encryption on AArch64: correctness

After the checks (`encMain_ok`): `EM` written, `DB` masked with MGF1 of the
seed and the seed with MGF1 of the masked `DB`, then `vg_rsa_public_checked`
of it into `out`. The frames, the prologue and the checks of `k` and the
message's length, with zeros to `out` if either fails: `enc_ok`, against the
shared contract.
-/

namespace VG.Proof.RsaOaep.AArch64.Enc

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Impl.RsaOaep.AArch64.Mgf1 (seqs)
open VG.Proof.Mgf1 (ifp ifn)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (StreamOK)
open VG.Proof.RsaPkcs1Enc.AArch64 (PubImpl)
open VG.Proof.RsaOaep.AArch64.Dec (entered)
open VG.Proof.RsaPkcs1Enc.AArch64.Enc (popped_mem popped_sp popped_v popped_gpr_self popped_gpr_ne freed_mem freed_sp
  freed_v freed_gpr add_add)

variable {Hl Gm : Hash} (hH : StreamOK Hl.stream) (hG : StreamOK Gm.stream)

include hH hG in
theorem encMain_ok {Hs Gs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = Hl.D)
    (hHv : Proof.Mgf1.Valid Hs) (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = Gm.D)
    (hGv : Proof.Mgf1.Valid Gs) (pv : PubImpl) {L : ELay} (hL : L.Ok) (hP : pv.S + 1 ≤ L.P) (hP16 : 16 ≤ L.P)
    (hD : L.D = Hl.D) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
    (hc : Ctx L g vv m₀ t) {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep t.mem L.Q L.scr V W) (hS : Slots L W)
    (hk : 2 * Hl.D + 2 + L.ml.toNat ≤ L.k.toNat) :
    WP isa (encMain Hl Gm pv.name pv.code) t fun t' => Ctx L g vv m₀ t' ∧
      Spec.Rsa.written t'.mem L.out L.k.toNat ((t'.gpr .x0).setWidth 32)
        (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt m₀ L.n L.k.toNat) (Spec.Rsa.bytesAt m₀ L.e L.el.toNat)
          (emOf Gs Hl.D L.k.toNat L.ml.toNat (Spec.Rsa.bytesAt m₀ L.sd Hl.D)
            (Hs.hash (Spec.Rsa.bytesAt m₀ L.lab L.labl.toNat)) (Spec.Rsa.bytesAt m₀ L.msg L.ml.toNat))) := by
  obtain ⟨-, hzF, -, hzDF, hD0⟩ := sizes hH
  have hD64 : Hl.D ≤ 64 := Nat.le_trans hzDF hzF
  replace hD0 : 0 < Hl.D := hD0
  have hk1024 := hL.k1024
  have cSt : oSt = 3072 := rfl
  have cR : oRsa = 8192 := rfl
  have hk3 : W 21 = BitVec.ofNat 64 L.k.toNat := by rw [hS.k, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have f4 : MFit 1 Hl.D (1 + Hl.D) (L.k.toNat - Hl.D - 1) :=
    ⟨by rw [cSt]; omega, by rw [cSt]; omega, by omega, by omega, by omega⟩
  have f2 : MFit (1 + Hl.D) (L.k.toNat - Hl.D - 1) 1 Hl.D :=
    ⟨by rw [cSt]; omega, by rw [cSt]; omega, by omega, by omega, by omega⟩
  unfold encMain seqs seqs seqs seqs seqs seqs
  -- `EM` before masking.
  refine WP.seq (WP.mono (encEm_ok hH hHh hL hP16 hD hc R hS hk) fun t5 ⟨hc5, V5, R5, E⟩ => ?_)
  -- `DB` masked.
  refine WP.seq (WP.mono (dbArgs_ok (hc5.lay hL hP16 R5 hS.scr) R5 hk3 (by omega) (by omega) hk1024 [])
    fun t6 ⟨_, S6, R6⟩ => ?_)
  have hc6 := hc5.step hL hP16 S6 nil_ws
  have hS6 : Slots L (mW W L.scr 1 Hl.D (1 + Hl.D) (L.k.toNat - Hl.D - 1)) :=
    hS.of fun j _ _ h3 => mW_eq _ _ _ _ _ _ (by omega)
  refine WP.seq (WP.mono (mgfXor_ok hG hGh hGl hGv (hc6.lay hL hP16 R6 hS6.scr) R6 f4 (mW_args _ _ _ _ _ _))
    fun t7 ⟨_, S7, V7, W7, R7, hW7, hV7⟩ => ?_)
  have hc7 := hc6.step hL hP16 S7 nil_ws
  have hS7 : Slots L W7 := hS6.of fun j _ h2 h3 => hW7 j (by unfold nW frameBytes; omega) (by omega) (by omega)
  -- The seed masked.
  refine WP.seq (WP.mono (seedArgs_ok (hc7.lay hL hP16 R7 hS7.scr) R7 (by rw [hS7.k, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]) (by omega) (by omega) hk1024 []) fun t8 ⟨_, S8, R8⟩ => ?_)
  have hc8 := hc7.step hL hP16 S8 nil_ws
  have hS8 : Slots L (mW W7 L.scr (1 + Hl.D) (L.k.toNat - Hl.D - 1) 1 Hl.D) :=
    hS7.of fun j _ _ h3 => mW_eq _ _ _ _ _ _ (by omega)
  refine WP.seq (WP.mono (mgfXor_ok hG hGh hGl hGv (hc8.lay hL hP16 R8 hS8.scr) R8 f2 (mW_args _ _ _ _ _ _))
    fun t9 ⟨_, S9, V9, W9, R9, hW9, hV9⟩ => ?_)
  have hc9 := hc8.step hL hP16 S9 nil_ws
  have hS9 : Slots L W9 := hS8.of fun j _ h2 h3 => hW9 j (by unfold nW frameBytes; omega) (by omega) (by omega)
  -- The call.
  refine WP.seq ?_
  rw [pubArgs_eq, WP.block_append_iff]
  refine WP.mono (pubW_ok hL hP16 hc9 R9 hS9) fun t10 ⟨hc10, R10⟩ => ?_
  have hS10 : Slots L (pubW L W9) := hS9.of fun j h1 _ _ => by
    simp only [pubW, upd]; rw [ifn (by omega), ifn (by omega)]
  refine WP.mono (pubR_ok hL hP16 hc10 R10 hS10) fun t11 ⟨hc11, hm11, hr11⟩ => ?_
  have R11 : Rep t11.mem L.Q L.scr V9 (pubW L W9) := hm11 ▸ R10
  refine WP.mono (pub_call pv hL hP hP16 hc11 hr11 R11 ⟨by simp [pubW, upd], by simp [pubW, upd]⟩)
    fun t12 ⟨hc12, hout⟩ => ⟨hc12, ?_⟩
  -- `EM` masked.
  have hlhl : (Hs.hash (Spec.Rsa.bytesAt m₀ L.lab L.labl.toNat)).length = Hl.D := by rw [hHv.2, hHl]
  have hml : (Spec.Rsa.bytesAt m₀ L.msg L.ml.toNat).length = L.ml.toNat := by simp [Spec.Rsa.bytesAt]
  have hsdl : (Spec.Rsa.bytesAt m₀ L.sd Hl.D).length = Hl.D := by simp [Spec.Rsa.bytesAt]
  have e1 : L.k.toNat - (Hl.D + 1) = L.k.toNat - Hl.D - 1 := by omega
  have hm : ∀ o, o < L.k.toNat → mOut o := fun o ho => (mOut_iff o).mpr (.inl (by unfold oSt; omega))
  have hsrc : srcB V7 (1 + Hl.D) (L.k.toNat - Hl.D - 1) =
      srcB (mixV V5 (Spec.Mgf1.mgf1 Gs (srcB V5 1 Hl.D) (L.k.toNat - Hl.D - 1)) (1 + Hl.D)
        (L.k.toNat - Hl.D - 1)) (1 + Hl.D) (L.k.toNat - Hl.D - 1) :=
    List.map_congr_left fun i hi => by
      have := List.mem_range.mp hi
      exact hV7 _ (by unfold oRsa; omega) (hm _ (by omega))
  have hlist : Spec.Rsa.bytesAt t11.mem (L.scr + BitVec.ofNat 64 0) L.k.toNat =
      emOf Gs Hl.D L.k.toNat L.ml.toNat (Spec.Rsa.bytesAt m₀ L.sd Hl.D)
        (Hs.hash (Spec.Rsa.bytesAt m₀ L.lab L.labl.toNat)) (Spec.Rsa.bytesAt m₀ L.msg L.ml.toNat) := by
    unfold emOf
    rw [← em_mask hGv (V₁ := V5) (by omega) hsdl (by
        simp only [List.length_append, List.length_cons, hlhl, hml, Spec.RsaOaep.zeros, List.length_replicate]; omega)
      E.z0 E.sd (E.db hlhl hml hk)]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    have hi' := List.mem_range.mp hi
    rw [BitVec.add_zero, show L.scr + BitVec.ofNat 64 i = off L.scr i from rfl, R11.scr i (by omega),
      hV9 _ (by omega) (hm _ hi'), hsrc]
    exact mixV_congr _ _ _ (hV7 _ (by omega) (hm _ hi'))
  rw [hlist] at hout
  exact hout

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
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show 2 * H.D + 2 < 2 ^ 64 by omega)]

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
  oaep_run [chkMsg, sK, sMsgLen, h168, h224, Ly.sp, rk, rml, sbc_self, show 2 * H.D + 2 < 4096 by omega,
    Offset.ofNat_sub_ofNat hD]
  refine ⟨trivial, trivial, trivial, trivial, trivial, cs_rfl, ?_⟩
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k - (2 * H.D + 2) < 2 ^ 64 by omega),
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

theorem encBody_eq (pubN : String) (pubC : Prog isa) :
    encBody Hl Gm pubN pubC = .seq (.block (encPrologue ++ chkK Hl)) (.ite (.nonzero .x .x11) encFail
      (.seq (.block (chkMsg Hl)) (.ite (.nonzero .x .x11) encFail (encMain Hl Gm pubN pubC)))) := rfl

/-- Zeros to `out` and 0 from a state with our arguments in their slots. -/
theorem fail_ok {L : ELay} (hL : L.Ok) (hP : 16 ≤ L.P) {g : Reg → BitVec 64} {vv : VReg → BitVec 128}
    {m₀ : Mem} {t : State} (hc : Ctx L g vv m₀ t) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem L.Q L.scr V W) (hS : Slots L W) :
    WP isa encFail t fun t' => Ctx L g vv m₀ t' ∧
      Spec.Rsa.written t'.mem L.out L.k.toNat ((t'.gpr .x0).setWidth 32) none := by
  have hk64 := hL.k64
  refine WP.mono (encFail_ok (hc.lay hL hP R hS.scr) R hS.out (by rw [hS.k, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]) (by omega) hL.k1024
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
    (hGv : Proof.Mgf1.Valid Gs) (pv : PubImpl) {P : Nat} (hP : pv.S + 1 ≤ P) (hP16 : 16 ≤ P) {s : State}
    (h : (encSpec Hs Gs P).pre s) :
    WP isa (encBody Hl Gm pv.name pv.code) (entered s) fun u => Ctx (lay Hs.len P s) s.gpr s.v s.mem u ∧
      Spec.Rsa.written u.mem (lay Hs.len P s).out (lay Hs.len P s).k.toNat ((u.gpr .x0).setWidth 32)
        (Spec.RsaOaep.encrypt Hs Gs (Spec.Rsa.bytesAt s.mem (lay Hs.len P s).n (lay Hs.len P s).k.toNat)
          (Spec.Rsa.bytesAt s.mem (lay Hs.len P s).e (lay Hs.len P s).el.toNat)
          (Spec.Rsa.bytesAt s.mem (lay Hs.len P s).lab (lay Hs.len P s).labl.toNat)
          (Spec.Rsa.bytesAt s.mem (lay Hs.len P s).msg (lay Hs.len P s).ml.toNat)
          (Spec.Rsa.bytesAt s.mem (lay Hs.len P s).sd Hs.len)) := by
  have hL := lay_ok h
  obtain ⟨-, hzF, -, hzDF, hD0⟩ := sizes hH
  have hD64 : Hl.D ≤ 64 := Nat.le_trans hzDF hzF
  have hk1024 := hL.k1024
  have hk64 := hL.k64
  have hp := prologue_ok h
  obtain ⟨L, hLL⟩ : ∃ L, lay Hs.len P s = L := ⟨_, rfl⟩
  rw [hLL] at hL hp hk1024 hk64 ⊢
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
    encrypt_none (by rw [hnB, hmB, hHl]; omega)
  rw [encBody_eq]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono hp fun t ⟨hc, _, hS⟩ => ?_
  have R : Rep t.mem L.Q L.scr (fun o => t.mem (off L.scr o)) (fun j => word t.mem L.Q (8 * j)) :=
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  have hk3 : (fun j => word t.mem L.Q (8 * j)) 21 = BitVec.ofNat 64 L.k.toNat :=
    hS.k.trans (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])
  refine WP.mono (chkK_ok (H := Hl) (hc.lay hL hP16 R hS.scr) R hk3 hk1024 (by omega))
    fun t1 ⟨_, S1, hm1, x11⟩ => ?_
  have hc1 := hc.step hL hP16 S1 nil_ws
  have R1 : Rep t1.mem L.Q L.scr (fun o => t.mem (off L.scr o)) (fun j => word t.mem L.Q (8 * j)) := hm1 ▸ R
  refine WP.ite _ (eval_nonzero t1 .x11) (fun hb => ?_) (fun hb => ?_)
  · have hkD : L.k.toNat < 2 * Hl.D + 2 := by
      by_contra hc'; rw [x11, ifp (by omega)] at hb; exact absurd hb (by decide)
    refine WP.mono (fail_ok hL hP16 hc1 R1 hS) fun u ⟨hcu, hw⟩ => ⟨hcu, ?_⟩
    rw [enone (by omega)]; exact hw
  · have hkD : 2 * Hl.D + 2 ≤ L.k.toNat := by
      by_contra hc'; rw [x11, ifn (by omega)] at hb; exact absurd hb (by decide)
    refine WP.seq (WP.mono (chkMsg_ok (H := Hl) (hc1.lay hL hP16 R1 hS.scr) R1 hk3
      (hS.ml.trans (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])) hk1024 L.ml.isLt hkD) fun t2 ⟨_, S2, hm2, x11'⟩ => ?_)
    have hc2 := hc1.step hL hP16 S2 nil_ws
    have R2 : Rep t2.mem L.Q L.scr (fun o => t.mem (off L.scr o)) (fun j => word t.mem L.Q (8 * j)) := hm2 ▸ R1
    refine WP.ite _ (eval_nonzero t2 .x11) (fun hb' => ?_) (fun hb' => ?_)
    · have hmk : L.k.toNat - (2 * Hl.D + 2) < L.ml.toNat := by
        by_contra hc'; rw [x11', ifp (by omega)] at hb'; exact absurd hb' (by decide)
      refine WP.mono (fail_ok hL hP16 hc2 R2 hS) fun u ⟨hcu, hw⟩ => ⟨hcu, ?_⟩
      rw [enone (by omega)]; exact hw
    · have hmk : L.ml.toNat ≤ L.k.toNat - (2 * Hl.D + 2) := by
        by_contra hc'; rw [x11', ifn (by omega)] at hb'; exact absurd hb' (by decide)
      refine WP.mono (encMain_ok hH hG hHh hHl hHv hGh hGl hGv pv hL hP hP16 hLD hc2 R2 hS (by omega))
        fun u ⟨hcu, hw⟩ => ⟨hcu, ?_⟩
      rw [encrypt_some hsB (by rw [hnB, hmB]; omega), hnB, hmB, hHl]
      exact hw

/-! ## The whole function -/

/-- The stack the contract gives. -/
theorem spec_sp {Hs Gs : Spec.Mgf1.Hash} {P : Nat} {s : State} (h : (encSpec Hs Gs P).pre s) :
    P + 288 ≤ s.sp.toNat := by
  sig_pre [Spec.RsaOaep.encryptContract, Spec.RsaOaep.encryptSig, AArch64.abi, AArch64.argRegs,
    _root_.List.range, _root_.List.range.loop, List.append_eq] at h
  exact h.1

/-- The postcondition, from what the body wrote. -/
theorem result_ok {Hs Gs : Spec.Mgf1.Hash} {P : Nat} {s : State} {t : State}
    (hw : Spec.Rsa.written t.mem (lay Hs.len P s).out (lay Hs.len P s).k.toNat ((t.gpr .x0).setWidth 32)
      (Spec.RsaOaep.encrypt Hs Gs (Spec.Rsa.bytesAt s.mem (lay Hs.len P s).n (lay Hs.len P s).k.toNat)
        (Spec.Rsa.bytesAt s.mem (lay Hs.len P s).e (lay Hs.len P s).el.toNat)
        (Spec.Rsa.bytesAt s.mem (lay Hs.len P s).lab (lay Hs.len P s).labl.toNat)
        (Spec.Rsa.bytesAt s.mem (lay Hs.len P s).msg (lay Hs.len P s).ml.toNat)
        (Spec.Rsa.bytesAt s.mem (lay Hs.len P s).sd Hs.len))) :
    (encSpec Hs Gs P).post s t := by
  sig_post [Spec.RsaOaep.encryptContract, Spec.RsaOaep.encryptSig, AArch64.abi, AArch64.argRegs,
    _root_.List.range, _root_.List.range.loop, List.append_eq]
  exact hw

include hH hG in
/-- `vg_rsa_oaep_<H>_mgf1_<G>_encrypt` meets the shared contract and the calling convention. -/
theorem enc_ok {Hs Gs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = Hl.D)
    (hHv : Proof.Mgf1.Valid Hs) (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = Gm.D)
    (hGv : Proof.Mgf1.Valid Gs) (pv : PubImpl) {P : Nat} (hP : pv.S + 1 ≤ P) (hP16 : 16 ≤ P) {s : State}
    (h : (encSpec Hs Gs P).pre s) :
    WP isa (encrypt Hl Gm pv.name pv.code) s fun s' =>
      abiPreserved s s' ∧ (encSpec Hs Gs P).post s s' := by
  have hsp := spec_sp h
  refine WP.frame (by omega) (WP.alloc (by decide) ?_ ?_)
  · show 272 ≤ (s.sp - 16).toNat
    rw [BitVec.toNat_sub_of_le (by show 16 ≤ s.sp.toNat; omega)]
    show 272 ≤ s.sp.toNat - 16
    omega
  · show WP isa (encBody Hl Gm pv.name pv.code) (entered s) _
    refine WP.mono (body_ok hH hG hHh hHl hHv hGh hGl hGv pv hP hP16 h) fun u' ⟨hc', hw'⟩ => ?_
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
    · refine result_ok ?_
      rw [popped_mem, freed_mem, popped_gpr_ne _ (by decide), freed_gpr]
      exact hw'

end VG.Proof.RsaOaep.AArch64.Enc
