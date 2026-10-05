import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecResult
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncCorrect

/-!
# RSAES-PKCS1-v1_5 decryption on x86-64: correctness

The frame's push, the first block (`setup_run`), the private-key operation
(`priv_call`), what follows it (`rest_ok`) and the frame's pop: `dec_correct`,
for every implementation of SHA-256's compression function and of
`vg_rsa_private_checked`.
-/

namespace VG.Proof.RsaPkcs1Enc.X86_64.Dec

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Decrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Enc.X86_64
open VG.Proof.Sha256.X86_64 (Compress)

/-- Everything after the private-key operation. -/
def rest (H : Impl.Pbkdf2.Md.X86_64.Hash) : Prog isa :=
  .seq dBuild (.seq (hashD H) (.seq (kdkMac H) (.seq (clLoop H) (.seq (amLoop H) (.seq maskPart (.seq alPart
    (.seq scanPart selPart)))))))

theorem body_eq (H : Impl.Pbkdf2.Md.X86_64.Hash) (privN : String) (priv : Prog isa) :
    body H privN priv = .seq (.block setup) (.seq (.call privN priv) (rest H)) := rfl

theorem rest_ok (v : Compress) {s t : State} (hp : DPre s) (h : PostPriv s t)
    (hcs : ∀ r ∈ calleeSaved, r ≠ .rsp → t.gpr r = s.gpr r) :
    WP isa (rest (HH v)) t (Fin s (t.gpr .rax) (Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (kOf s)) (amOf s)
      (vEM (Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (kOf s)) (kOf s)) (okOf (t.gpr .rax))
      (lEM s (Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (kOf s)))) := by
  refine WP.seq (WP.mono (dBuild_step hp h hcs) fun _ h₁ => ?_)
  refine WP.seq (WP.mono (hashD_step hp h₁) fun _ h₂ => ?_)
  refine WP.seq (WP.mono (kdkMac_step hp h₂) fun _ h₃ => ?_)
  refine WP.seq (WP.mono (clLoop_step hp h₃) fun _ h₄ => ?_)
  refine WP.seq (WP.mono (amLoop_step hp h₄) fun _ h₅ => ?_)
  refine WP.seq (WP.mono (maskPart_step hp h₅) fun _ h₆ => ?_)
  refine WP.seq (WP.mono (alPart_step hp h₆) fun _ h₇ => ?_)
  refine WP.seq (WP.mono (scanPart_step hp h₇) fun _ h₈ => ?_)
  exact selPart_step hp h₈


/-- The bytes of a buffer, from each one. -/
theorem bytes_of {m : Mem} {p : Addr} {k : Nat} {g : Nat → Byte} (h : ∀ i < k, m (off p i) = g i) :
    Spec.Rsa.bytesAt m p k = (List.range k).map g :=
  List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

theorem outByte_false (v : Bool) (kl i : Nat) (e a : Byte) : outByte v false kl i e a = 0 := by
  simp [outByte]

/-- The postcondition, from what the private-key operation gave and the end. -/
theorem result_ok {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {m : Mem} {t : State}
    (hres : Spec.Rsa.writtenOutcome m (s.gpr .rdi) (kOf s) (R.setWidth 32) (privOut s))
    (hEM : Spec.Rsa.bytesAt m (s.gpr .rdi) (kOf s) = EM)
    (hF : Fin s R EM (amOf s) (vEM EM (kOf s)) (okOf R) (lEM s EM) t) (hAM : (amOf s).length = kOf s) :
    Spec.RsaPkcs1Enc.writtenMsg t.mem (s.gpr .rdi) (s.gpr .rdx) (kOf s) ((t.gpr .rax).setWidth 32)
      (Spec.RsaPkcs1Enc.decrypt (nB s) (eB s) (dB s) (pB s) (qB s) (dpB s) (dqB s) (qiB s) (cB s)) := by
  have hk1 := hp.k1
  have hk2 := hp.k2
  have hkk1 : 64 ≤ kOf s := hk1
  have hn : (nB s).length = kOf s := blen _ _ _
  have hC : (cB s).length = kOf s := blen _ _ _
  rw [hF.rax]
  have hml : Spec.Rsa.wordsAt t.mem (s.gpr .rdx) 1 = [BitVec.ofNat 64 (lEM s EM) &&& bmask (okOf R)] := by
    simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero, hF.ml]
  have hout := bytes_of hF.out
  simp only [Spec.RsaPkcs1Enc.decrypt]
  cases hO : privOut s with
  | ok EM' =>
    rw [hO] at hres
    obtain ⟨hr, hb⟩ := hres
    rw [hEM] at hb; subst hb
    have hok : okOf R = true := by simp [okOf, hr]
    rw [decryptWith_of_ok (rsadp := fun C => Spec.Rsa.privateChecked (nB s) (eB s) C (pB s) (qB s) (dpB s) (dqB s) (qiB s)) (C := cB s) (dB := dB s) (k := (nB s).length) (by rw [hn]; exact hC) (by rw [hn]; omega) hO]
    have hEMl : EM.length = kOf s := by rw [← hEM, blen]
    have hal := altFold_le (kOf s) (clOf s) 128
    rw [← altLength_eq] at hal
    obtain ⟨hL, hmap⟩ := sel_eq hEMl hAM (by omega) hal
    have hM : Spec.RsaPkcs1Enc.implicitDecode (dB s) (cB s) EM = (if Spec.RsaPkcs1Enc.valid EM then
        Spec.RsaPkcs1Enc.lastN (Spec.RsaPkcs1Enc.msgLength EM) EM
        else Spec.RsaPkcs1Enc.lastN (Spec.RsaPkcs1Enc.altLength (kOf s) (clOf s)) (amOf s)) := by
      simp only [Spec.RsaPkcs1Enc.implicitDecode, Spec.RsaPkcs1Enc.alternative, hEMl]
    rw [hM]
    refine ⟨hr, ?_, ?_⟩
    · rw [hout, hok]; exact hmap
    · rw [hml, hok, ← hL, show bmask true = BitVec.allOnes 64 from rfl, BitVec.and_allOnes]
  | invalid =>
    rw [hO] at hres
    obtain ⟨hr, -⟩ := hres
    have hok : okOf R = false := by simp [okOf, hr]
    rw [decryptWith_of_invalid (rsadp := fun C => Spec.Rsa.privateChecked (nB s) (eB s) C (pB s) (qB s) (dpB s) (dqB s) (qiB s)) (C := cB s) (dB := dB s) (k := (nB s).length) hO]
    refine ⟨hr, ?_, ?_⟩
    · rw [hout]; simp [hok, outByte_false]
    · rw [hml, hok]; simp [bmask]
  | fault =>
    rw [hO] at hres
    obtain ⟨hr, -⟩ := hres
    have hok : okOf R = false := by simp [okOf, hr]
    rw [decryptWith_of_fault (rsadp := fun C => Spec.Rsa.privateChecked (nB s) (eB s) C (pB s) (qB s) (dpB s) (dqB s) (qiB s)) (C := cB s) (dB := dB s) (k := (nB s).length) (by rw [hn]; exact hC) (by rw [hn]; omega) hO]
    refine ⟨hr, ?_, ?_⟩
    · rw [hout]; simp [hok, outByte_false]
    · rw [hml, hok]; simp [bmask]


open VG.Proof.Pbkdf2.Md.X86_64 (core_hmacInit core_hmacFin core_updC core_finC)

/-- No instruction after the private-key operation loads MXCSR: not those of
SHA-256's and HMAC's functions, by what is proven of them, nor its own. -/
theorem rest_mx (v : Compress) : (rest (HH v)).allInstrs (fun i => !loadsMxcsr i) = true := by
  have K := Proof.Pbkdf2.Md.X86_64.Sha256.callees v
  have C := Proof.Pbkdf2.Md.X86_64.Sha256.coreOK
  have hI : (HH v).hmacInit.allInstrs (fun i => !loadsMxcsr i) = true := core_hmacInit K.cMx K.iMx C.hinitMx
  have hU : (HH v).updC.allInstrs (fun i => !loadsMxcsr i) = true := core_updC K.cMx C.updMx
  have hFi : (HH v).finC.allInstrs (fun i => !loadsMxcsr i) = true := core_finC K.cMx C.finMx
  have hF : (HH v).hmacFin.allInstrs (fun i => !loadsMxcsr i) = true := core_hmacFin K.cMx C.hfinMx
  simp only [rest, dBuild, zeroLoop, copyLoop, hashD, kdkMac, clLoop, amLoop, prfBody, maskPart, maskLoop,
    alPart, alLoop, scanPart, scanLoop, selPart, selLoop, Code.allInstrs, hI, hU, hFi, hF, K.iMx, Bool.and_true,
    Bool.true_and]
  decide +kernel

/-- The return address is outside everything the function writes. -/
theorem ret_frame {s : State} (hp : DPre s) {m : Mem} (h : Frame (wrs s) s.mem m) :
    m.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64 := by
  have hsp2 := hp.sp2
  refine h.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · have := Offset.disjoint_below (s.gpr .rsp) (n := decStack) (d := 0) (k := 8)
      (by unfold decStack frameBytes privStack; omega)
    simpa only [stkR, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this
  · exact hp.dRo
  · exact hp.dRm
  · exact hp.dRs

theorem dec_correct (v : Compress) (pv : PrivImpl) (s : State) (h : decK.pre s) :
    ∃ t s', Exec isa (code (HH v) pv.name pv.code) s t s' ∧ abiPreserved s s' ∧ decK.post s s' := by
  have hp := dPre_of h
  suffices hw : WP isa (code (HH v) pv.name pv.code) s fun s' => abiPreserved s s' ∧ decK.post s s' by
    obtain ⟨t, s', he, hq⟩ := hw
    exact ⟨t, s', he, hq⟩
  refine wp_alloc (by decide) (by decide) (by decide) (by have := hp.sp1; unfold decStack at this; omega) ?_
  rw [body_eq]
  refine WP.seq (WP.mono_mx (by decide +kernel)
    (WP.keep [.rax, .rsi, .rdx, .rcx, .r8, .r9] (setup_run hp) (by decide +kernel))
    fun t₁ ⟨h₁, k₁⟩ hmx₁ => ?_)
  refine WP.seq (WP.mono (priv_call pv hp h₁) fun t₂ ⟨hpost, hcs₂, hmx₂⟩ => ?_)
  have hcs : ∀ r ∈ calleeSaved, r ≠ .rsp → t₂.gpr r = s.gpr r := fun r hr hr' => by
    rw [hcs₂ r hr, k₁.cs (by decide) r hr]
    simp only [allocState_gpr, hr', ↓reduceIte]
  refine WP.mono_mx (rest_mx v) (rest_ok v hp hpost hcs) fun t₃ hF hmx₃ => ?_
  refine ⟨hF.rsp, by rw [hF.wr]; rfl, ⟨fun r hr => ?_, ret_frame hp hF.mem, ?_⟩, ?_⟩
  · by_cases hr' : r = .rsp
    · subst hr'
      show t₃.gpr .rsp + BitVec.ofNat 64 frameBytes = s.gpr .rsp
      rw [hF.rsp, BitVec.sub_add_cancel]
    · show (if r = .rsp then _ else t₃.gpr r) = s.gpr r
      simp only [hr', ↓reduceIte]
      exact hF.cs r hr hr'
  · show t₃.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10
    rw [hmx₃, hmx₂, hmx₁]; rfl
  · have hAM : (amOf s).length = kOf s := hF.amLen
    have := result_ok hp hpost.res rfl hF hAM
    simp only [decK]
    rw [freed_mem, freed_rax]
    exact this

end VG.Proof.RsaPkcs1Enc.X86_64.Dec
