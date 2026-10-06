import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.DecOut
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncCorrect
import VerifiedGarbage.Proof.RsaPkcs1Enc.Decrypt

/-!
# RSAES-PKCS1-v1_5 decryption on AArch64: correctness

The frames' pushes, the setup (`entry_ok`), the private-key operation
(`priv_call`), `D`, `DH`, `KDK`, `CL`, `AM`, the alternative length, the scan
and the output (`dBuild_ok` … `selPart_ok`), and the pops: `dec_ok`, for
every implementation of SHA-256's compression function and of
`vg_rsa_private_checked`, against the shared contract (`result_ok`).
-/

namespace VG.Proof.RsaPkcs1Enc.AArch64.Dec

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Decrypt
open VG.Proof.Sha256.AArch64 (Compress)
open VG.Proof.RsaPkcs1Enc (outByte)
open VG.Proof.RsaPkcs1Enc.AArch64.Enc (popped_mem popped_sp popped_v popped_gpr_self popped_gpr_ne freed_mem freed_sp
  freed_v freed_gpr add_add bytesAt_length)

theorem body_eq (privN : String) (priv : Prog isa) (v : Compress) :
    body (HH v) privN priv = .seq (.block setup) (.seq (.call privN priv) (.seq dBuild (.seq (hashD (HH v))
      (.seq (kdkMac (HH v)) (.seq (clLoop (HH v)) (.seq (amLoop (HH v)) (.seq maskPart (.seq alPart
        (.seq scanPart selPart))))))))) := rfl

theorem rOf_setWidth (x : BitVec 64) : (rOf x).setWidth 32 = x.setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  simp only [rOf, BitVec.toNat_setWidth]
  omega

theorem rOf_one (x : BitVec 64) : decide (rOf x = 1) = decide (x.setWidth 32 = 1) := by
  have : rOf x = 1 ↔ x.setWidth 32 = 1 := by
    constructor
    · intro h; rw [← rOf_setWidth, h]; rfl
    · intro h; simp only [rOf, h]; rfl
  simp only [this]

/-- RSADP, as the specification calls the private-key operation. -/
def rsadpOf (L : Lay) (m : Mem) (C : List Byte) : Spec.Rsa.Outcome :=
  Spec.Rsa.privateChecked (Spec.Rsa.bytesAt m L.n L.k.toNat) (Spec.Rsa.bytesAt m L.e L.el.toNat) C
    (Spec.Rsa.bytesAt m L.p L.pl.toNat) (Spec.Rsa.bytesAt m L.q L.ql.toNat) (Spec.Rsa.bytesAt m L.dp L.pl.toNat)
    (Spec.Rsa.bytesAt m L.dq L.ql.toNat) (Spec.Rsa.bytesAt m L.qi L.pl.toNat)

/-- The stack the contract gives. -/
theorem spec_sp {P : Nat} {s : State} (h : (decSpec P).pre s) : P + 224 ≤ s.sp.toNat := by
  sig_pre [Spec.RsaPkcs1Enc.decryptContract, Spec.RsaPkcs1Enc.decryptSig, AArch64.abi, AArch64.argRegs,
    _root_.List.range, _root_.List.range.loop, List.append_eq] at h
  exact h.1

/-- The postcondition, from what the private-key operation gave and the end. -/
theorem result_ok {P : Nat} {s : State} (h : (decSpec P).pre s) {x0c : BitVec 64} {mc : Mem} {t : State}
    {kd : List Byte} (hkd : kd = Spec.RsaPkcs1Enc.kdk (lay P s).k.toNat (dOf (lay P s) s.mem) (cOf (lay P s) s.mem))
    (hres : Spec.Rsa.writtenOutcome mc (lay P s).out (lay P s).k.toNat (x0c.setWidth 32) (privOut (lay P s) s.mem))
    (hx0 : t.gpr .x0 = rOf x0c)
    (hout : ∀ i < (lay P s).k.toNat, t.mem ((lay P s).out + BitVec.ofNat 64 i) =
      outByte (vOfEM (lay P s) (Spec.Rsa.bytesAt mc (lay P s).out (lay P s).k.toNat)) (decide (rOf x0c = 1))
        ((lay P s).k.toNat - lenOf (lay P s) (Spec.Rsa.bytesAt mc (lay P s).out (lay P s).k.toNat) kd) i
        ((Spec.Rsa.bytesAt mc (lay P s).out (lay P s).k.toNat).getD i 1) ((amOf (lay P s) kd).getD i 0))
    (hml : t.mem.readW (lay P s).ml 64 =
      BitVec.ofNat 64 (lenOf (lay P s) (Spec.Rsa.bytesAt mc (lay P s).out (lay P s).k.toNat) kd) &&&
        bm (decide (rOf x0c = 1)))
    (hAM : (amOf (lay P s) kd).length = (lay P s).k.toNat) :
    (decSpec P).post s t := by
  have hL := lay_ok h
  have hk64 := hL.k64
  sig_post [Spec.RsaPkcs1Enc.decryptContract, Spec.RsaPkcs1Enc.decryptSig, AArch64.abi, AArch64.argRegs,
    _root_.List.range, _root_.List.range.loop, List.append_eq]
  -- The buffers, as the layout names them.
  show Spec.RsaPkcs1Enc.writtenMsg t.mem (lay P s).out (lay P s).ml (lay P s).k.toNat ((t.gpr .x0).setWidth 32)
    (Spec.RsaPkcs1Enc.decrypt (Spec.Rsa.bytesAt s.mem (lay P s).n (lay P s).k.toNat)
      (Spec.Rsa.bytesAt s.mem (lay P s).e (lay P s).el.toNat) (dOf (lay P s) s.mem)
      (Spec.Rsa.bytesAt s.mem (lay P s).p (lay P s).pl.toNat) (Spec.Rsa.bytesAt s.mem (lay P s).q (lay P s).ql.toNat)
      (Spec.Rsa.bytesAt s.mem (lay P s).dp (lay P s).pl.toNat) (Spec.Rsa.bytesAt s.mem (lay P s).dq (lay P s).ql.toNat)
      (Spec.Rsa.bytesAt s.mem (lay P s).qi (lay P s).pl.toNat) (cOf (lay P s) s.mem))
  have hn : (Spec.Rsa.bytesAt s.mem (lay P s).n (lay P s).k.toNat).length = (lay P s).k.toNat := bytesAt_length _ _ _
  have hC : (cOf (lay P s) s.mem).length = (Spec.Rsa.bytesAt s.mem (lay P s).n (lay P s).k.toNat).length := by
    rw [hn]; exact bytesAt_length _ _ _
  have hbytes : Spec.Rsa.bytesAt t.mem (lay P s).out (lay P s).k.toNat =
      (List.range (lay P s).k.toNat).map fun i => t.mem ((lay P s).out + BitVec.ofNat 64 i) := rfl
  have hw : Spec.Rsa.wordsAt t.mem (lay P s).ml 1 = [t.mem.readW (lay P s).ml 64] := by
    simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero]
  simp only [Spec.RsaPkcs1Enc.decrypt]
  have eO : rsadpOf (lay P s) s.mem (cOf (lay P s) s.mem) = privOut (lay P s) s.mem := rfl
  show Spec.RsaPkcs1Enc.writtenMsg _ _ _ _ _ (Spec.RsaPkcs1Enc.decryptWith (rsadpOf (lay P s) s.mem)
    (Spec.Rsa.bytesAt s.mem (lay P s).n (lay P s).k.toNat).length (dOf (lay P s) s.mem) (cOf (lay P s) s.mem))
  cases hO : privOut (lay P s) s.mem with
  | ok EM' =>
    rw [hO] at hres
    obtain ⟨hr, hb⟩ := hres
    have hok : decide (rOf x0c = 1) = true := by rw [rOf_one, hr]; rfl
    rw [Proof.RsaPkcs1Enc.decryptWith_of_ok hC (by rw [hn]; omega) (eO.trans hO)]
    subst hb
    have hEMl := bytesAt_length mc (lay P s).out (lay P s).k.toNat
    have hal := Proof.RsaPkcs1Enc.altLength_le (lay P s).k.toNat (clOf kd)
    obtain ⟨hL1, hmap⟩ := Proof.RsaPkcs1Enc.sel_eq hEMl hAM (by omega) hal
    have hM : Spec.RsaPkcs1Enc.implicitDecode (dOf (lay P s) s.mem) (cOf (lay P s) s.mem)
        (Spec.Rsa.bytesAt mc (lay P s).out (lay P s).k.toNat) =
        (if Spec.RsaPkcs1Enc.valid (Spec.Rsa.bytesAt mc (lay P s).out (lay P s).k.toNat) then
          Spec.RsaPkcs1Enc.lastN (Spec.RsaPkcs1Enc.msgLength (Spec.Rsa.bytesAt mc (lay P s).out (lay P s).k.toNat))
            (Spec.Rsa.bytesAt mc (lay P s).out (lay P s).k.toNat)
        else Spec.RsaPkcs1Enc.lastN (Spec.RsaPkcs1Enc.altLength (lay P s).k.toNat (clOf kd)) (amOf (lay P s) kd)) := by
      simp only [Spec.RsaPkcs1Enc.implicitDecode, Spec.RsaPkcs1Enc.alternative, hEMl, hkd]
    rw [hM]
    refine ⟨by rw [hx0, rOf_setWidth, hr], ?_, ?_⟩
    · rw [hbytes, ← hmap]
      exact List.map_congr_left fun i hi => by rw [hout i (List.mem_range.mp hi), hok]
    · rw [hw, hml, hok, show bm true = BitVec.allOnes 64 from rfl, BitVec.and_allOnes, ← hL1]
  | invalid =>
    rw [hO] at hres
    obtain ⟨hr, -⟩ := hres
    have hok : decide (rOf x0c = 1) = false := by rw [rOf_one, hr]; rfl
    rw [Proof.RsaPkcs1Enc.decryptWith_of_invalid (eO.trans hO)]
    refine ⟨by rw [hx0, rOf_setWidth, hr], ?_, ?_⟩
    · rw [hbytes, List.map_congr_left (g := fun _ => (0 : Byte)) fun i hi => by
        rw [hout i (List.mem_range.mp hi), hok, Proof.RsaPkcs1Enc.outByte_false]]
      simp
    · rw [hw, hml, hok]; simp [bm]
  | fault =>
    rw [hO] at hres
    obtain ⟨hr, -⟩ := hres
    have hok : decide (rOf x0c = 1) = false := by rw [rOf_one, hr]; rfl
    rw [Proof.RsaPkcs1Enc.decryptWith_of_fault hC (by rw [hn]; omega) (eO.trans hO)]
    refine ⟨by rw [hx0, rOf_setWidth, hr], ?_, ?_⟩
    · rw [hbytes, List.map_congr_left (g := fun _ => (0 : Byte)) fun i hi => by
        rw [hout i (List.mem_range.mp hi), hok, Proof.RsaPkcs1Enc.outByte_false]]
      simp
    · rw [hw, hml, hok]; simp [bm]

/-- `vg_rsa_pkcs1_decrypt` meets the shared contract and the calling convention. -/
theorem dec_ok (v : Compress) (pv : PrivImpl) {s : State} (h : (decSpec (pv.S + 1)).pre s) :
    WP isa (code (HH v) pv.name pv.code) s fun s' => abiPreserved s s' ∧ (decSpec (pv.S + 1)).post s s' := by
  have hL := lay_ok h
  have hnQ := hL.nQ
  have hpQ := hL.pQ
  have hS := pv.S15
  have hsp := spec_sp h
  have hP16 : 16 ≤ (lay (pv.S + 1) s).P := by show 16 ≤ pv.S + 1; omega
  refine WP.frame (by omega) (WP.alloc (by decide) ?_ ?_)
  · show 208 ≤ (s.sp - 16).toNat
    rw [BitVec.toNat_sub_of_le (by show 16 ≤ s.sp.toNat; omega)]
    show 208 ≤ s.sp.toNat - 16
    omega
  · show WP isa (body (HH v) pv.name pv.code) (entered s) _
    rw [body_eq]
    refine WP.seq (WP.mono (entry_ok h) fun t ⟨hc, hr⟩ => ?_)
    refine WP.seq (WP.mono (priv_call pv hL rfl hc hr) fun t₁ h₁ => ?_)
    refine WP.seq (WP.mono (dBuild_ok hL h₁) fun t₂ h₂ => ?_)
    refine WP.seq (WP.mono (hashD_ok hL hP16 h₂) fun t₃ h₃ => ?_)
    refine WP.seq (WP.mono (kdkMac_ok hL hP16 h₃) fun t₄ h₄ => ?_)
    refine WP.seq (WP.mono (clLoop_ok hL hP16 h₄.post h₄.kdk) fun t₅ h₅ => ?_)
    refine WP.seq (WP.mono (amLoop_ok hL hP16 h₅) fun t₆ h₆ => ?_)
    have hAM : Spec.Rsa.bytesAt t₆.mem (scA (lay (pv.S + 1) s) sAM) (lay (pv.S + 1) s).k.toNat =
        amOf (lay (pv.S + 1) s) (Spec.RsaPkcs1Enc.kdk (lay (pv.S + 1) s).k.toNat (dOf (lay (pv.S + 1) s) s.mem)
          (cOf (lay (pv.S + 1) s) s.mem)) := h₆.am
    refine WP.seq (WP.mono (maskPart_ok hL h₆) fun t₇ h₇ => ?_)
    refine WP.seq (WP.mono (alPart_ok hL h₇) fun t₈ h₈ => ?_)
    refine WP.seq (WP.mono (scanPart_ok hL h₈) fun t₉ h₉ => ?_)
    refine WP.mono (selPart_ok hL h₉) fun u hu => ?_
    have hc := hu.ctx
    have hsp' : (freed frameBytes u).sp = (lay (pv.S + 1) s).Q + BitVec.ofNat 64 208 := by
      rw [freed_sp, hc.sp]; rfl
    refine ⟨⟨fun r hr => ?_, ?_, fun r hr => ?_⟩, ?_⟩
    · by_cases h30 : r = .x30
      · subst r
        rw [popped_gpr_self, freed_mem, hsp']; exact hc.kept.lr
      · rw [popped_gpr_ne _ h30, freed_gpr]
        exact hc.cs r hr h30
    · rw [popped_sp, hsp']
      show (lay (pv.S + 1) s).Q + BitVec.ofNat 64 208 + BitVec.ofNat 64 16 = s.sp
      rw [add_add]; exact lay_Q _ s
    · rw [popped_v, freed_v]
      exact hc.vs r hr
    · refine result_ok h rfl h₁.out ?_ (fun i hi => ?_) ?_ (by rw [← hAM, bytesAt_length])
      · rw [popped_gpr_ne _ (by decide), freed_gpr]; exact hu.x0
      · rw [popped_mem, freed_mem]; exact hu.out i hi
      · rw [popped_mem, freed_mem]; exact hu.ml

end VG.Proof.RsaPkcs1Enc.AArch64.Dec
