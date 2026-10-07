import VerifiedGarbage.Proof.RsaOaep.AArch64.DecPriv

/-!
# RSAES-OAEP decryption on AArch64: correctness

The frames' pushes, the prologue (`prologue_ok`), the private-key operation
(`privW_ok`, `privR_ok`, `priv_call`), its result to its slot and the check
of `k` (`resK_ok`): zeros to `out` and `*msg_len` if `k` is too small
(`decFail_ok`), the decoding otherwise (`decMain_ok`); and the pops:
`dec_ok`, for every implementation of the hash functions and of
`vg_rsa_private_checked`, against the shared contract.
-/

namespace VG.Proof.RsaOaep.AArch64.Dec

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Proof.Mgf1 (ifp ifn)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (StreamOK)
open VG.Proof.RsaPkcs1Enc.AArch64 (PrivImpl)
open VG.Proof.RsaPkcs1Enc.AArch64.Enc (popped_mem popped_sp popped_v popped_gpr_self popped_gpr_ne freed_mem freed_sp
  freed_v freed_gpr add_add)

/-- The private-key operation's result to its slot, zero-extended, and the
check of `k`: `x11` all ones iff `k < 2 hLen + 2`. -/
theorem resK_ok {H : Hash} {u : State} {F S : Addr} (Ly : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {k : Nat} (hk : W 21 = BitVec.ofNat 64 k) (hk' : k ≤ 1024) (hD : 2 * H.D + 2 < 65536) :
    WP isa (.block (([.logic .orr .w .x0 .x0 .x0, .addSp .x9 0, .str .x .x0 .x9 sR] : List Instr) ++ chkK H)) u
      fun u' => Lay u' F S ∧ Step F S [] u u' ∧
        Rep u'.mem F S V (upd W 28 (((u.gpr .x0).setWidth 32).setWidth 64)) ∧
        u'.gpr .x11 = if 2 * H.D + 2 ≤ k then 0 else BitVec.allOnes 64 := by
  have G' := Ly.geo
  have h168 : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 168) 8 := Ly.ld (d := 168) (by decide)
  have w224 : InRegions u.wr (F + BitVec.ofNat 64 224) 8 := Ly.st (d := 224) (by decide)
  have R1 : Rep (u.mem.write (off F 224) 8 (((u.gpr .x0).setWidth 32).setWidth 64)) F S V
      (upd W 28 (((u.gpr .x0).setWidth 32).setWidth 64)) := R.wq G' (k := 28) (by decide) _
  have rk : (u.mem.write (off F 224) 8 (((u.gpr .x0).setWidth 32).setWidth 64)).read
      (F + BitVec.ofNat 64 168) 8 = BitVec.ofNat 64 k :=
    R1.rd8 (d := 168) (k := 21) rfl (by decide) (by simp only [upd]; exact hk)
  refine WP.mono (Q := fun (u' : State) => u'.mem = u.mem.write (off F 224) 8 (((u.gpr .x0).setWidth 32).setWidth 64) ∧
      u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧ u'.v = u.v ∧ (∀ r ∈ preserved, r ≠ .x30 → u'.gpr r = u.gpr r) ∧
      u'.gpr .x11 = if 2 * H.D + 2 ≤ k then 0 else BitVec.allOnes 64) ?_
    fun u' ⟨hm, hrd, hwr, hsp, hv, hcs, x11⟩ => ?_
  · oaep_run [chkK, sR, sK, h168, w224, Ly.sp, rk, imm16 hD, sbc_self, BitVec.add_zero, BitVec.or_self]
    refine ⟨trivial, trivial, trivial, trivial, trivial, cs_rfl, ?_⟩
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show 2 * H.D + 2 < 2 ^ 64 by omega)]
  have R' : Rep u'.mem F S V (upd W 28 (((u.gpr .x0).setWidth 32).setWidth 64)) := by rw [hm]; exact R1
  have S' : Step F S [] u u' := ⟨hrd, hwr, hsp, hcs, fun r _ => by rw [hv], by
    rw [hm]; exact Frame.write (Frame.refl _ _) (List.mem_cons_self ..) _ (cF F (by decide))⟩
  refine ⟨Ly.congr hsp hwr ?_, S', R', x11⟩
  rw [show sScr = 8 * 12 from rfl, R'.fr 12 (by decide), R.fr 12 (by decide)]
  rfl

/-! ## After the prologue -/

/-- What the body leaves: `Ctx`, and `out`, `*msg_len` and the result as
decryption with the private-key operation's outcome says. -/
def Fin (Hs Gs : Spec.Mgf1.Hash) (L : DLay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem)
    (u : State) : Prop :=
  Ctx L g vv m₀ u ∧ Spec.RsaOaep.writtenDecrypt u.mem L.out L.ml L.k.toNat ((u.gpr .x0).setWidth 32)
    (decOut Hs Gs (Spec.Rsa.bytesAt m₀ L.lab L.labl.toNat) (privOut L m₀))

/-- The result in its slot and `EM` in our working space, from the call. -/
theorem resD_of {L : DLay} {m₀ : Mem} {u : State} {W : Nat → BitVec 64}
    (hw : Spec.Rsa.writtenOutcome u.mem (L.scr + BitVec.ofNat 64 0) L.k.toNat ((u.gpr .x0).setWidth 32)
      (privOut L m₀)) :
    ResD (fun o => u.mem (off L.scr o)) (upd W 28 (((u.gpr .x0).setWidth 32).setWidth 64)) L.k.toNat
      (privOut L m₀) := by
  have e28 : upd W 28 (((u.gpr .x0).setWidth 32).setWidth 64) 28 = ((u.gpr .x0).setWidth 32).setWidth 64 := by
    simp [upd]
  revert hw
  cases privOut L m₀ with
  | ok em =>
    rintro ⟨hr, hb⟩
    refine ⟨by rw [e28, hr]; rfl, ?_⟩
    rw [← hb]
    refine List.map_congr_left fun i _ => ?_
    show u.mem (L.scr + BitVec.ofNat 64 (0 + i)) = u.mem (L.scr + BitVec.ofNat 64 0 + BitVec.ofNat 64 i)
    rw [Nat.zero_add, BitVec.add_zero]
  | invalid => rintro ⟨hr, -⟩; show _ = _; rw [e28, hr]; rfl
  | fault => rintro ⟨hr, -⟩; show _ = _; rw [e28, hr]; rfl

theorem resD_len {V : Nat → Byte} {W : Nat → BitVec 64} {k : Nat} {o : Spec.Rsa.Outcome} (h : ResD V W k o) :
    ∀ em, o = .ok em → em.length = k := by
  intro em ho
  subst ho
  rw [← h.2]; simp

variable {Hl Gm : Hash} (hH : StreamOK Hl.stream) (hG : StreamOK Gm.stream)

theorem decBody_eq (privN : String) (privC : Prog isa) :
    decBody Hl Gm privN privC = .seq (.block (decPrologue ++ privArgs)) (.seq (.call privN privC)
      (.seq (.block (([.logic .orr .w .x0 .x0 .x0, .addSp .x9 0, .str .x .x0 .x9 sR] : List Instr) ++ chkK Hl))
        (.ite (.nonzero .x .x11) decFail (decMain Hl Gm)))) := rfl

include hH hG in
theorem rest_ok {Hs Gs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = Hl.D)
    (hHv : Proof.Mgf1.Valid Hs) (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = Gm.D)
    (hGv : Proof.Mgf1.Valid Gs) (pv : PrivImpl) {L : DLay} (hL : L.Ok) (hP : L.P = pv.S + 1)
    {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State} (hc : Ctx L g vv m₀ t)
    (h9 : t.gpr .x9 = L.Q) (hpw : Prologued L (fun j => word t.mem L.Q (8 * j))) :
    WP isa (.block privArgs) t fun u => WP isa (.seq (.call pv.name pv.code)
      (.seq (.block (([.logic .orr .w .x0 .x0 .x0, .addSp .x9 0, .str .x .x0 .x9 sR] : List Instr) ++ chkK Hl))
        (.ite (.nonzero .x .x11) decFail (decMain Hl Gm)))) u (Fin Hs Gs L g vv m₀) := by
  have hS15 := pv.S15
  have hP16 : 16 ≤ L.P := by omega
  obtain ⟨-, hzF, -, hzDF, hD0⟩ := sizes hH
  have hD64 : Hl.D ≤ 64 := Nat.le_trans hzDF hzF
  have hk64 := hL.k64
  have hk1024 := hL.k1024
  rw [privArgs_eq, WP.block_append_iff]
  have R₀ : Rep t.mem L.Q L.scr (fun o => t.mem (off L.scr o)) (fun j => word t.mem L.Q (8 * j)) :=
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  refine WP.mono (privW_ok hL hP16 hc h9 R₀ hpw.slots) fun u1 ⟨hc1, _, R1⟩ => ?_
  have hS1 : Slots L (privW L fun j => word t.mem L.Q (8 * j)) :=
    hpw.slots.of fun j _ _ h3 => by simp only [privW, upd]; rw [ifn (by omega), ifn (by omega)]
  refine WP.mono (privR_ok hL hP16 hc1 R1 hS1) fun u2 ⟨hc2, hm2, hr2⟩ => ?_
  have R2 : Rep u2.mem L.Q L.scr (fun o => t.mem (off L.scr o)) (privW L fun j => word t.mem L.Q (8 * j)) :=
    hm2 ▸ R1
  have hA : CallArgs L (privW L fun j => word t.mem L.Q (8 * j)) :=
    ⟨by simp only [privW, upd]; exact hpw.p, fun j hj => by
      simp only [privW, upd]; rw [ifn (by omega), ifn (by omega)]; exact hpw.args j hj,
      by simp [privW, upd], by simp [privW, upd]⟩
  refine WP.seq (WP.mono (priv_call pv hL hP hc2 hr2 R2 hA) fun u3 hcl => ?_)
  have Ly3 := hcl.ctx.lay hL hP16 hcl.rep hS1.scr
  have hk3 : (privW L fun j => word t.mem L.Q (8 * j)) 21 = BitVec.ofNat 64 L.k.toNat := by
    rw [hS1.k, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.seq (WP.mono (resK_ok (H := Hl) Ly3 hcl.rep hk3 hk1024 (by omega)) fun u4 ⟨Ly4, S4, R4, x11⟩ => ?_)
  have hc4 := hcl.ctx.step hL hP16 S4 fun r h => absurd h List.not_mem_nil
  generalize hW4 : upd (privW L fun j => word t.mem L.Q (8 * j)) 28 (((u3.gpr .x0).setWidth 32).setWidth 64) = W4
    at R4
  have hres := resD_of (W := privW L fun j => word t.mem L.Q (8 * j)) hcl.out
  rw [hW4] at hres
  have hS4 : Slots L W4 := hW4 ▸ hS1.of fun j _ _ h3 => by simp only [upd]; rw [ifn (by omega)]
  have hk4 : W4 21 = BitVec.ofNat 64 L.k.toNat := by rw [hS4.k, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have O4 := hc4.outAt hL hP16 hS4
  have hws : ∀ r ∈ [L.OUT, L.ML], r = L.OUT ∨ r = L.ML := fun r hr => by simpa using hr
  refine WP.ite _ (eval_nonzero u4 .x11) (fun hb => ?_) (fun hb => ?_)
  · -- `k < 2 hLen + 2`: zeros.
    have hkD : L.k.toNat < 2 * Hl.D + 2 := by
      by_contra hc; rw [x11, ifp (by omega)] at hb; exact absurd hb (by decide)
    refine WP.mono (decFail_ok Ly4 R4 O4.ho O4.hml hk4 (by omega) hk1024 O4.hw O4.hnw O4.ha O4.hwm O4.ham O4.hom)
      fun u5 ⟨_, S5, hz5, hm5, hx5⟩ => ⟨hc4.step hL hP16 S5 hws, ?_⟩
    rw [decOut_short (resD_len hres) (by rw [hHl]; exact hkD)]
    have hzs := out_zero (m := u5.mem) (o := L.out) (k := L.k.toNat) hz5
    revert hres
    cases privOut L m₀ with
    | ok em => intro hr; exact ⟨by rw [hx5, fltW, hr.1]; rfl, hzs, hm5⟩
    | invalid => intro hr; exact ⟨by rw [hx5, fltW, show W4 28 = 0 from hr]; rfl, hzs, hm5⟩
    | fault => intro hr; exact ⟨by rw [hx5, fltW, show W4 28 = 2 from hr]; rfl, hzs, hm5⟩
  · -- The decoding.
    have hkD : 2 * Hl.D + 2 ≤ L.k.toNat := by
      by_contra hc; rw [x11, ifn (by omega)] at hb; exact absurd hb (by decide)
    refine WP.mono (decMain_ok hH hG hHh hHl hHv hGh hGl hGv Ly4 R4 hk4 hkD hk1024 (hc4.labAt hL hP16 hS4) O4 hres)
      fun u5 ⟨_, S5, hw5⟩ => ⟨hc4.step hL hP16 S5 hws, ?_⟩
    have hlab := hc4.bytes_ro hL (ro_LAB L)
    simp only at hlab
    rw [hlab] at hw5
    exact hw5

/-! ## The whole function -/

/-- The stack the contract gives. -/
theorem spec_sp {Hs Gs : Spec.Mgf1.Hash} {P : Nat} {s : State} (h : (decSpec Hs Gs P).pre s) :
    P + 288 ≤ s.sp.toNat := by
  sig_pre [Spec.RsaOaep.decryptContract, Spec.RsaOaep.decryptSig, AArch64.abi, AArch64.argRegs,
    _root_.List.range, _root_.List.range.loop, List.append_eq] at h
  exact h.1

/-- The postcondition, from what the body wrote. -/
theorem result_ok {Hs Gs : Spec.Mgf1.Hash} {P : Nat} {s : State} {t : State}
    (hw : Spec.RsaOaep.writtenDecrypt t.mem (lay P s).out (lay P s).ml (lay P s).k.toNat ((t.gpr .x0).setWidth 32)
      (decOut Hs Gs (Spec.Rsa.bytesAt s.mem (lay P s).lab (lay P s).labl.toNat) (privOut (lay P s) s.mem))) :
    (decSpec Hs Gs P).post s t := by
  sig_post [Spec.RsaOaep.decryptContract, Spec.RsaOaep.decryptSig, AArch64.abi, AArch64.argRegs,
    _root_.List.range, _root_.List.range.loop, List.append_eq]
  rw [decrypt_eq (by simp [Spec.Rsa.bytesAt])]
  exact hw

include hH hG in
/-- `vg_rsa_oaep_<H>_mgf1_<G>_decrypt` meets the shared contract and the calling convention. -/
theorem dec_ok {Hs Gs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = Hl.D)
    (hHv : Proof.Mgf1.Valid Hs) (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = Gm.D)
    (hGv : Proof.Mgf1.Valid Gs) (pv : PrivImpl) {s : State} (h : (decSpec Hs Gs (pv.S + 1)).pre s) :
    WP isa (decrypt Hl Gm pv.name pv.code) s fun s' =>
      abiPreserved s s' ∧ (decSpec Hs Gs (pv.S + 1)).post s s' := by
  have hL := lay_ok h
  have hnQ := hL.nQ
  have hpQ := hL.pQ
  have hS := pv.S15
  have hsp := spec_sp h
  refine WP.frame (by omega) (WP.alloc (by decide) ?_ ?_)
  · show 272 ≤ (s.sp - 16).toNat
    rw [BitVec.toNat_sub_of_le (by show 16 ≤ s.sp.toNat; omega)]
    show 272 ≤ s.sp.toNat - 16
    omega
  · show WP isa (decBody Hl Gm pv.name pv.code) (entered s) _
    rw [decBody_eq]
    refine WP.seq ?_
    rw [WP.block_append_iff]
    refine WP.mono (prologue_ok h) fun t ⟨hc, h9, hpw⟩ => ?_
    refine WP.mono (rest_ok hH hG hHh hHl hHv hGh hGl hGv pv hL rfl hc h9 hpw) fun u hu => ?_
    refine WP.mono hu fun u' ⟨hc', hw'⟩ => ?_
    have hsp' : (freed frameBytes u').sp = (lay (pv.S + 1) s).Q + BitVec.ofNat 64 272 := by
      rw [freed_sp, hc'.sp]; rfl
    refine ⟨⟨fun r hr => ?_, ?_, fun r hr => ?_⟩, ?_⟩
    · by_cases h30 : r = .x30
      · subst r
        rw [popped_gpr_self, freed_mem, hsp']; exact hc'.lr
      · rw [popped_gpr_ne _ h30, freed_gpr]
        exact hc'.cs r hr h30
    · rw [popped_sp, hsp']
      show (lay (pv.S + 1) s).Q + BitVec.ofNat 64 272 + BitVec.ofNat 64 16 = s.sp
      rw [add_add]; exact lay_Q _ s
    · rw [popped_v, freed_v]
      exact hc'.vs r hr
    · refine result_ok ?_
      rw [popped_mem, freed_mem, popped_gpr_ne _ (by decide), freed_gpr]
      exact hw'

end VG.Proof.RsaOaep.AArch64.Dec
