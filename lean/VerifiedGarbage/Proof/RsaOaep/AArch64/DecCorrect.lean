module

public import VerifiedGarbage.Proof.RsaOaep.AArch64.DecPriv
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs

/-!
# RSAES-OAEP decryption on AArch64: correctness

The frames' pushes, the prologue (`prologue_ok`), the private-key operation
(`privW_ok`, `privR_ok`, `priv_call`), its result to its slot and the check
of `k` (`resK_ok`): zeros to `out` and `*msg_len` if `k` is too small
(`decFail_ok`), the decoding otherwise (`decMain_ok`); and the pops:
`dec_ok`, for every implementation of the hash functions and of
`vg_rsa_private_checked`, against the shared contract.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.AArch64.Dec

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Proof.Mgf1 (ifp ifn)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (StreamOK)
open VG.Proof.Pbkdf2.Md.AArch64 (Tier)
open VG.Proof.RsaPkcs1Enc.AArch64 (PrivImpl)
open VG.Proof.RsaPkcs1Enc.AArch64.Enc (popped_mem popped_sp popped_v popped_gpr_self popped_gpr_ne freed_mem freed_sp
  freed_v freed_gpr add_add)

/-- The private-key operation's result to its slot, zero-extended. -/
theorem resSlot_ok {u : State} {F S : Addr} (Ly : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) :
    WP isa (.block [.logic .orr .w .x0 .x0 .x0, .addSp .x9 0, .str .x .x0 .x9 sR]) u
      fun u' => Lay u' F S ∧ Step F S [] u u' ∧
        Rep u'.mem F S V (upd W 28 (((u.gpr .x0).setWidth 32).setWidth 64)) := by
  have G' := Ly.geo
  have w224 : InRegions u.wr (F + BitVec.ofNat 64 224) 8 := Ly.st (d := 224) (by decide)
  have R1 : Rep (u.mem.write (off F 224) 8 (((u.gpr .x0).setWidth 32).setWidth 64)) F S V
      (upd W 28 (((u.gpr .x0).setWidth 32).setWidth 64)) := R.wq G' (k := 28) (by decide) _
  refine WP.mono (Q := fun (u' : State) => u'.mem = u.mem.write (off F 224) 8 (((u.gpr .x0).setWidth 32).setWidth 64) ∧
      u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧ u'.v = u.v ∧ (∀ r ∈ preserved, r ≠ .x30 → u'.gpr r = u.gpr r))
    ?_ fun u' ⟨hm, hrd, hwr, hsp, hv, hcs⟩ => ?_
  · oaep_run [sR, w224, Ly.sp, BitVec.add_zero, BitVec.or_self]
    oaep_fin
  have R' : Rep u'.mem F S V (upd W 28 (((u.gpr .x0).setWidth 32).setWidth 64)) := by rw [hm]; exact R1
  have S' : Step F S [] u u' := ⟨hrd, hwr, hsp, hcs, fun r _ => by rw [hv], by
    rw [hm]; exact Frame.write (Frame.refl _ _) (List.mem_cons_self ..) _ (cF F (by decide))⟩
  refine ⟨Ly.congr hsp hwr ?_, S', R'⟩
  rw [show sScr = 8 * 12 from rfl, R'.fr 12 (by decide), R.fr 12 (by decide)]
  rfl

/-- The frame's words after the hash functions' slots are set: `W` but in
words 2 to 5. -/
def setW (W : Nat → BitVec 64) (kH DH kG DG : Nat) : Nat → BitVec 64 :=
  upd (upd (upd (upd W 2 (BitVec.ofNat 64 kH)) 4 (BitVec.ofNat 64 DH)) 3 (BitVec.ofNat 64 kG)) 5
    (BitVec.ofNat 64 DG)

theorem setW_slots (W : Nat → BitVec 64) (kH DH kG DG : Nat) : HSlots (setW W kH DH kG DG) kH DH kG DG :=
  ⟨by simp [setW, upd], by simp [setW, upd], by simp [setW, upd], by simp [setW, upd]⟩

theorem setW_eq (W : Nat → BitVec 64) (kH DH kG DG : Nat) {j : Nat} (hj : j < 2 ∨ 5 < j) :
    setW W kH DH kG DG j = W j := by
  simp only [setW, upd]; rw [ifn (by omega), ifn (by omega), ifn (by omega), ifn (by omega)]

/-- Our stack argument `j` (`hash` or `mgf1_hash`), from the frame's base. -/
theorem Ctx.argAt {L : DLay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
    (hc : Ctx L g vv m₀ t) {j : Nat} (hj : j < 17) :
    InRegions (t.rd ++ t.wr) (L.Q + BitVec.ofNat 64 (arg j)) 8 ∧
      t.mem.read (L.Q + BitVec.ofNat 64 (arg j)) 8 = BitVec.ofNat 64 (ourArg L j).toNat :=
  ⟨⟨L.ARGS, List.mem_append_left _ (by rw [hc.rd]; simp),
      Offset.contains _ (show 288 ≤ arg j by unfold arg frameBytes; omega)
        (by unfold arg frameBytes; omega) (by omega)⟩,
    by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; exact hc.args j hj⟩

/-- The hash functions' numbers and lengths to their slots. -/
theorem setup_ok {hs : List Hash} {Hl Gm : Hash} {L : DLay} (hnH : Num hs L.hh.toNat Hl)
    (hnG : Num hs L.gh.toNat Gm) (hDH : Hl.D < 65536) (hDG : Gm.D < 65536) (hL : L.Ok) (hP16 : 16 ≤ L.P)
    {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {u : State} (hc : Ctx L g vv m₀ u)
    {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep u.mem L.Q L.scr V W) (hS : Slots L W) :
    WP isa (hashSetup hs 15 16) u fun u' => Ctx L g vv m₀ u' ∧
      Rep u'.mem L.Q L.scr V (setW W L.hh.toNat Hl.D L.gh.toNat Gm.D) := by
  have Ly := hc.lay hL hP16 R hS.scr
  obtain ⟨ld15, v15⟩ := hc.argAt (j := 15) (by decide)
  refine WP.seq (WP.mono (selArg_ok hnH hDH Ly R (j := 15) (a := 2) (b := 4) (by decide) (by decide) (by decide)
    (by decide) (by decide) ld15 v15 []) fun u1 ⟨L1, S1, R1⟩ => ?_)
  have hc1 := hc.step hL hP16 S1 (fun r h => absurd h List.not_mem_nil)
  obtain ⟨ld16, v16⟩ := hc1.argAt (j := 16) (by decide)
  refine WP.mono (selArg_ok hnG hDG L1 R1 (j := 16) (a := 3) (b := 5) (by decide) (by decide) (by decide)
    (by decide) (by decide) ld16 v16 []) fun u2 ⟨_, S2, R2⟩ =>
      ⟨hc1.step hL hP16 S2 (fun r h => absurd h List.not_mem_nil), R2⟩

/-! ## After the prologue -/

/-- What the body leaves: `Ctx`, and `out`, `*msg_len` and the result as
decryption with the private-key operation's outcome says, with the hash
functions the layout's numbers name. -/
def Fin (L : DLay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (u : State) : Prop :=
  Ctx L g vv m₀ u ∧ ∃ Hs Gs, Spec.HashId.mgf1 L.hh.toNat = some Hs ∧ Spec.HashId.mgf1 L.gh.toNat = some Gs ∧
    Spec.RsaOaep.writtenDecrypt u.mem L.out L.ml L.k.toNat ((u.gpr .x0).setWidth 32)
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

theorem decBody_eq (hs : List Hash) (privN : String) (privC : Prog isa) :
    decBody hs privN privC = .seq (.block (decPrologue ++ privArgs)) (.seq (.call privN privC)
      (.seq (.block [.logic .orr .w .x0 .x0 .x0, .addSp .x9 0, .str .x .x0 .x9 sR]) (.seq (hashSetup hs 15 16)
        (.seq (.block chkK) (.ite (.nonzero .x .x11) decFail (decMain hs)))))) := rfl

theorem rest_ok (t : Tier) (pv : PrivImpl) {L : DLay} (hL : L.Ok) (hP : L.P = pv.S + 1)
    {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {u : State} (hc : Ctx L g vv m₀ u)
    (h9 : u.gpr .x9 = L.Q) (hpw : Prologued L (fun j => word u.mem L.Q (8 * j))) :
    WP isa (.block privArgs) u fun u => WP isa (.seq (.call pv.name pv.code)
      (.seq (.block [.logic .orr .w .x0 .x0 .x0, .addSp .x9 0, .str .x .x0 .x9 sR]) (.seq (hashSetup (tierHs t) 15 16)
        (.seq (.block chkK) (.ite (.nonzero .x .x11) decFail (decMain (tierHs t))))))) u (Fin L g vv m₀) := by
  have hS15 := pv.S15
  have hP16 : 16 ≤ L.P := by omega
  obtain ⟨vH, hnH, hmH⟩ := tier_num t hL.hhk
  obtain ⟨vG, hnG, hmG⟩ := tier_num t hL.ghk
  obtain ⟨-, hzF, -, hzDF, hD0⟩ := sizes vH.ok.stream
  have hD64 : vH.H.D ≤ 64 := Nat.le_trans hzDF hzF
  obtain ⟨-, gzF, -, gzDF, -⟩ := sizes vG.ok.stream
  have gD64 : vG.H.D ≤ 64 := Nat.le_trans gzDF gzF
  have hk64 := hL.k64
  have hk1024 := hL.k1024
  rw [privArgs_eq, WP.block_append_iff]
  have R₀ : Rep u.mem L.Q L.scr (fun o => u.mem (off L.scr o)) (fun j => word u.mem L.Q (8 * j)) :=
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  refine WP.mono (privW_ok hL hP16 hc h9 R₀ hpw.slots) fun u1 ⟨hc1, _, R1⟩ => ?_
  have hS1 : Slots L (privW L fun j => word u.mem L.Q (8 * j)) :=
    hpw.slots.of fun j _ _ h3 => by simp only [privW, upd]; rw [ifn (by omega), ifn (by omega)]
  refine WP.mono (privR_ok hL hP16 hc1 R1 hS1) fun u2 ⟨hc2, hm2, hr2⟩ => ?_
  have R2 : Rep u2.mem L.Q L.scr (fun o => u.mem (off L.scr o)) (privW L fun j => word u.mem L.Q (8 * j)) :=
    hm2 ▸ R1
  have hA : CallArgs L (privW L fun j => word u.mem L.Q (8 * j)) :=
    ⟨by simp only [privW, upd]; exact hpw.p, fun j hj => by
      simp only [privW, upd]; rw [ifn (by omega), ifn (by omega)]; exact hpw.args j hj,
      by simp [privW, upd], by simp [privW, upd]⟩
  refine WP.seq (WP.mono (priv_call pv hL hP hc2 hr2 R2 hA) fun u3 hcl => ?_)
  have Ly3 := hcl.ctx.lay hL hP16 hcl.rep hS1.scr
  -- The result to its slot.
  refine WP.seq (WP.mono (resSlot_ok Ly3 hcl.rep) fun u4 ⟨Ly4, S4, R4⟩ => ?_)
  have hc4 := hcl.ctx.step hL hP16 S4 fun r h => absurd h List.not_mem_nil
  generalize hW4 : upd (privW L fun j => word u.mem L.Q (8 * j)) 28 (((u3.gpr .x0).setWidth 32).setWidth 64) = W4
    at R4
  have hres := resD_of (W := privW L fun j => word u.mem L.Q (8 * j)) hcl.out
  rw [hW4] at hres
  have hS4 : Slots L W4 := hW4 ▸ hS1.of fun j _ _ h3 => by simp only [upd]; rw [ifn (by omega)]
  -- The hash functions' slots.
  refine WP.seq (WP.mono (setup_ok hnH hnG (by omega) (by omega) hL hP16 hc4 R4 hS4) fun u5 ⟨hc5, R5⟩ => ?_)
  have hS5 : Slots L (setW W4 L.hh.toNat vH.H.D L.gh.toNat vG.H.D) :=
    hS4.of fun j h1 _ _ => setW_eq _ _ _ _ _ (by omega)
  have hres5 : ResD (fun o => u3.mem (off L.scr o)) (setW W4 L.hh.toNat vH.H.D L.gh.toNat vG.H.D) L.k.toNat
      (privOut L m₀) := by
    have e : setW W4 L.hh.toNat vH.H.D L.gh.toNat vG.H.D 28 = W4 28 := setW_eq _ _ _ _ _ (by omega)
    revert hres; cases privOut L m₀ <;> exact fun h => by simpa only [ResD, e] using h
  have Ly5 := hc5.lay hL hP16 R5 hS5.scr
  have hk5 : setW W4 L.hh.toNat vH.H.D L.gh.toNat vG.H.D 21 = BitVec.ofNat 64 L.k.toNat := by
    rw [hS5.k, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have Hk := setW_slots W4 L.hh.toNat vH.H.D L.gh.toNat vG.H.D
  -- The check of `k`.
  refine WP.seq (WP.mono (chkK_ok Ly5 R5 hk5 Hk.hlen hk1024 hD64) fun u6 ⟨Ly6, S6, hm6, x11⟩ => ?_)
  have hc6 := hc5.step hL hP16 S6 fun r h => absurd h List.not_mem_nil
  have R6 := hm6 ▸ R5
  have O6 := hc6.outAt hL hP16 hS5
  have hws : ∀ r ∈ [L.OUT, L.ML], r = L.OUT ∨ r = L.ML := fun r hr => by simpa using hr
  refine WP.ite _ (eval_nonzero u6 .x11) (fun hb => ?_) (fun hb => ?_)
  · -- `k < 2 hLen + 2`: zeros.
    have hkD : L.k.toNat < 2 * vH.H.D + 2 := by
      by_contra hc; rw [x11, ifp (by omega)] at hb; exact absurd hb (by decide)
    refine WP.mono (decFail_ok Ly6 R6 O6.ho O6.hml hk5 (by omega) hk1024 O6.hw O6.hnw O6.ha O6.hwm O6.ham O6.hom)
      fun u7 ⟨_, S7, hz7, hm7, hx7⟩ => ⟨hc6.step hL hP16 S7 hws, vH.mgf.G, vG.mgf.G, hmH, hmG, ?_⟩
    rw [decOut_short (resD_len hres5) (by rw [vH.mgf.len]; exact hkD)]
    have hzs := out_zero (m := u7.mem) (o := L.out) (k := L.k.toNat) hz7
    revert hres5
    cases privOut L m₀ with
    | ok em => intro hr; exact ⟨by rw [hx7, fltW, hr.1]; rfl, hzs, hm7⟩
    | invalid => intro hr; exact ⟨by rw [hx7, fltW, show setW W4 L.hh.toNat vH.H.D L.gh.toNat vG.H.D 28 = 0 from hr]; rfl, hzs, hm7⟩
    | fault => intro hr; exact ⟨by rw [hx7, fltW, show setW W4 L.hh.toNat vH.H.D L.gh.toNat vG.H.D 28 = 2 from hr]; rfl, hzs, hm7⟩
  · -- The decoding.
    have hkD : 2 * vH.H.D + 2 ≤ L.k.toNat := by
      by_contra hc; rw [x11, ifn (by omega)] at hb; exact absurd hb (by decide)
    refine WP.mono (decMain_ok hnH hnG vH.ok.stream vG.ok.stream vH.mgf.hash vH.mgf.len (mgf_valid vH.mgf)
      vG.mgf.hash vG.mgf.len (mgf_valid vG.mgf) Ly6 R6 hk5 hkD hk1024 (hc6.labAt hL hP16 hS5) O6 hres5 Hk)
      fun u7 ⟨_, S7, hw7⟩ => ⟨hc6.step hL hP16 S7 hws, vH.mgf.G, vG.mgf.G, hmH, hmG, ?_⟩
    have hlab := hc6.bytes_ro hL (ro_LAB L)
    simp only at hlab
    rw [hlab] at hw7
    exact hw7

/-! ## The whole function -/

/-- The stack the contract gives. -/
theorem spec_sp {P : Nat} {s : State} (h : (decSpec P).pre s) :
    P + 288 ≤ s.sp.toNat := by
  sig_pre [Spec.RsaOaep.decryptAnyContract, Spec.RsaOaep.decryptAnySig, AArch64.abi, AArch64.argRegs,
    _root_.List.range, _root_.List.range.loop, List.append_eq] at h
  exact h.1

/-- The postcondition, from what the body wrote. -/
theorem result_ok {P : Nat} {s : State} {t : State} {Hs Gs : Spec.Mgf1.Hash}
    (hH : Spec.HashId.mgf1 (lay P s).hh.toNat = some Hs) (hG : Spec.HashId.mgf1 (lay P s).gh.toNat = some Gs)
    (hw : Spec.RsaOaep.writtenDecrypt t.mem (lay P s).out (lay P s).ml (lay P s).k.toNat ((t.gpr .x0).setWidth 32)
      (decOut Hs Gs (Spec.Rsa.bytesAt s.mem (lay P s).lab (lay P s).labl.toNat) (privOut (lay P s) s.mem))) :
    (decSpec P).post s t := by
  sig_post [Spec.RsaOaep.decryptAnyContract, Spec.RsaOaep.decryptAnySig, AArch64.abi, AArch64.argRegs,
    _root_.List.range, _root_.List.range.loop, List.append_eq]
  intro H G hH' hG'
  change Spec.HashId.mgf1 (stackArg s 15).toNat = some Hs at hH
  change Spec.HashId.mgf1 (stackArg s 16).toNat = some Gs at hG
  rw [hH] at hH'; rw [hG] at hG'
  cases hH'; cases hG'
  rw [decrypt_eq (by simp [Spec.Rsa.bytesAt])]
  exact hw

/-- `vg_rsa_oaep_decrypt` meets the shared contract and the calling convention. -/
theorem dec_ok (t : Tier) (pv : PrivImpl) {s : State} (h : (decSpec (pv.S + 1)).pre s) :
    WP isa (decrypt (tierHs t) pv.name pv.code) s fun s' =>
      abiPreserved s s' ∧ (decSpec (pv.S + 1)).post s s' := by
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
  · show WP isa (decBody (tierHs t) pv.name pv.code) (entered s) _
    rw [decBody_eq]
    refine WP.seq ?_
    rw [WP.block_append_iff]
    refine WP.mono (prologue_ok h) fun t' ⟨hc, h9, hpw⟩ => ?_
    refine WP.mono (rest_ok t pv hL rfl hc h9 hpw) fun u hu => ?_
    refine WP.mono hu fun u' ⟨hc', Hs, Gs, hmH, hmG, hw'⟩ => ?_
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
    · refine result_ok hmH hmG ?_
      rw [popped_mem, freed_mem, popped_gpr_ne _ (by decide), freed_gpr]
      exact hw'

end VG.Proof.RsaOaep.AArch64.Dec
