import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecCT4
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecCorrect
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.Alloc

/-!
# RSAES-PKCS1-v1_5 decryption on x86-64: constant time

The output: the validity mask, the selected length and the mask of the
private-key operation's result are computed without branches from `EM`'s
first bytes, the scan and the result's slot; `msg_len`'s store and the
selection's loads and stores are at addresses from the pointers alone, and
the loop runs `k` times. With the earlier phases, `dec_constantTime`, and
`dec_verified`.
-/

namespace VG.Proof.RsaPkcs1Enc.X86_64.Dec

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Decrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Enc.X86_64
open VG.Proof.Sha256.X86_64 (Compress)

variable {v : Compress}

/-- After the checks: `EM` in `rdi` and `k` in `r9`. -/
def JV (s t : State) : Prop := Cx s t ∧ t.gpr .rdi = s.gpr .rdi ∧ t.gpr .r9 = BitVec.ofNat 64 (kOf s)

theorem valid_step {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (h : SC s R EM t) :
    WP isa (.block validBlock) t (JV s) := by
  have hk1 := hp.k1
  have hk2 := hp.k2
  have hkk : kOf s ≤ 1024 := hk2
  have hkk1 : 64 ≤ kOf s := hk1
  have hc := h.ctx
  have hs := hc.frm hp
  have hsep : (firstZero EM (kOf s)).getD 0 < kOf s := by
    cases hf : firstZero EM (kOf s) with
    | none => simp; omega
    | some i => have := firstZero_some hf; simpa using this.2.1
  have hR : t.mem.readW (fb s + BitVec.ofNat 64 oR) 64 = R := hc.sR
  have hio : ∀ i n, i + n ≤ kOf s → InRegions (t.rd ++ t.wr) (off (s.gpr .rdi) i) n := fun i n h' =>
    let ⟨r, hr, hcr⟩ := hc.outIn hp h'; ⟨r, List.mem_append_right _ hr, hcr⟩
  exact WP.mono (validBlock_run (p := s.gpr .rdi) (F := fb s) (b0 := EM.getD 0 1) (b1 := EM.getD 1 1)
    h.rdi (by rw [← hc.em (i := 0) (by omega)]; exact (congrArg t.mem (off_zero _)).symm)
    (hc.em (by omega)) (by have := hio 0 1 (by omega); rwa [off_zero] at this) (hio 1 1 (by omega)) h.rdx h.r10 h.r11
    h.r9 hc.rsp hR (hs.ld (d := oR) (by decide)) hsep (by omega))
    fun _ ⟨⟨hm₁, _⟩, k₁⟩ => ⟨⟨R, EM, hc.regs hp hm₁ k₁ (by decide)⟩, (k₁.gpr (by decide)).trans h.rdi,
      (k₁.gpr (by decide)).trans h.r9⟩

/-- After `outPtrs`: `msg_len` in `r8` and `AM` in `rcx`. -/
def JO (s t : State) : Prop :=
  Cx s t ∧ (t.gpr .rdi = s.gpr .rdi ∧ t.gpr .r9 = BitVec.ofNat 64 (kOf s) ∧ t.gpr .r8 = s.gpr .rdx ∧
    t.gpr .rcx = scA s sAM)

theorem outPtrs_run {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t) :
    WP isa (.block outPtrs) t fun t' => Ctx s R EM t' ∧ t'.mem = t.mem ∧ t'.gpr .rdi = t.gpr .rdi ∧
      t'.gpr .r9 = t.gpr .r9 ∧ t'.gpr .r8 = s.gpr .rdx ∧ t'.gpr .rcx = scA s sAM := by
  have hs := hc.frm hp
  refine (WP.keep [.r8, .rcx] (c := .block outPtrs) (Q := fun t' => t'.mem = t.mem ∧
    t'.gpr .r8 = s.gpr .rdx ∧ t'.gpr .rcx = scA s sAM) ?_ rfl).mono
    fun t' ⟨h, k⟩ => ⟨hc.regs hp h.1 k (by decide), h.1, k.gpr (by decide), k.gpr (by decide), h.2⟩
  xrun [outPtrs, scr, List.cons_append, List.nil_append, ea_sp, hc.rsp, hs.ld (d := oML) (by decide),
    hs.ld (d := oScr) (by decide), hc.slots.sML, hc.slots.sScr, sx (d := sAM) (by decide)]

/-- After `outInit`: the selection's pointers, index and count. -/
def JI (s t : State) : Prop :=
  t.gpr .rdi = s.gpr .rdi ∧ t.gpr .rsi = scA s sAM ∧ t.gpr .rcx = BitVec.ofNat 64 0 ∧
    t.gpr .r9 = BitVec.ofNat 64 (kOf s) ∧ t.gpr .rsp = fb s

theorem outInit_run {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t)
    (h8 : t.gpr .r8 = s.gpr .rdx) (hcx : t.gpr .rcx = scA s sAM) :
    WP isa (.block outInit) t fun t' => t'.gpr .rdi = t.gpr .rdi ∧ t'.gpr .r9 = t.gpr .r9 ∧
      t'.gpr .rsp = t.gpr .rsp ∧ t'.gpr .rsi = scA s sAM ∧ t'.gpr .rcx = BitVec.ofNat 64 0 := by
  have hml : InRegions t.wr (s.gpr .rdx) 8 :=
    ⟨mlR s, by rw [hc.wr, hp.hwr]; simp [mlR], Region.contains_self _ _⟩
  refine (WP.keep [.rdx, .rsi, .rcx] (c := .block outInit) (Q := fun t' =>
    t'.gpr .rsi = scA s sAM ∧ t'.gpr .rcx = BitVec.ofNat 64 0) ?_ rfl).mono
    fun t' ⟨h, k⟩ => ⟨k.gpr (by decide), k.gpr (by decide), k.gpr (by decide), h⟩
  xrun [outInit, ea_atd (p := s.gpr .rdx), h8, hml, hcx]

theorem selPart_ct : RelCT isa (Two (At JSC)) selPart fun _ _ => True := by
  refine RelCT.seq (two_blk (J' := JV) [.rdi, .rsp] (pins (J := JSC) [(.rdi, fun s => s.gpr .rdi), (.rsp, fb)]
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl) s t ⟨_, _, h⟩
      · exact h.rdi
      · exact h.ctx.rsp)
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl)
      · exact gpr_pin (by decide)
      · exact fb_pin)) (by taint_decide) fun _ _ hp ⟨_, _, h⟩ => valid_step hp h) ?_
  refine RelCT.seq (cx_blk (F := fun s t => t.gpr .rdi = s.gpr .rdi ∧ t.gpr .r9 = BitVec.ofNat 64 (kOf s))
    (F' := fun s t => t.gpr .rdi = s.gpr .rdi ∧ t.gpr .r9 = BitVec.ofNat 64 (kOf s) ∧ t.gpr .r8 = s.gpr .rdx ∧
      t.gpr .rcx = scA s sAM) (by taint_decide)
    fun s t R EM hp hc ⟨hdi, h9⟩ => WP.mono (outPtrs_run hp hc) fun _ ⟨hc', _, hdi', h9', h8', hcx'⟩ =>
      ⟨hc', hdi'.trans hdi, h9'.trans h9, h8', hcx'⟩) ?_
  refine RelCT.seq (two_blk (J' := JI) [.r8, .rcx] (pins (J := JO) [(.r8, fun s => s.gpr .rdx), (.rcx, fun s => scA s sAM)]
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl) s t h
      · exact h.2.2.2.1
      · exact h.2.2.2.2)
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl)
      · exact gpr_pin (by decide)
      · exact scA_pin _)) (by taint_decide)
    fun s t hp ⟨⟨R, EM, hc⟩, hdi, h9, h8, hcx⟩ => WP.mono (outInit_run hp hc h8 hcx)
      fun _ ⟨hdi', h9', hsp', hsi', hcx'⟩ => ⟨hdi'.trans hdi, hsi', hcx', h9'.trans h9, hsp'.trans hc.rsp⟩) ?_
  exact two_taint [.rdi, .rsi, .rcx, .r9, .rsp] (pins (J := JI) [(.rdi, fun s => s.gpr .rdi),
      (.rsi, fun s => scA s sAM), (.rcx, fun _ => BitVec.ofNat 64 0), (.r9, fun s => BitVec.ofNat 64 (kOf s)),
      (.rsp, fb)]
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl | rfl | rfl | rfl) s t h
      · exact h.1
      · exact h.2.1
      · exact h.2.2.1
      · exact h.2.2.2.1
      · exact h.2.2.2.2)
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl | rfl | rfl | rfl)
      · exact gpr_pin (by decide)
      · exact scA_pin _
      · exact const_pin _
      · intro a s S; dsimp only; rw [S.k]
      · exact fb_pin)) (by taint_decide)

/-! ## The function -/

theorem body_ct (v : Compress) (pv : PrivImpl) :
    RelCT isa (Two (At J0)) (body (HH v) pv.name pv.code) fun _ _ => True := by
  rw [body_eq]
  exact RelCT.seq setup_two (RelCT.seq (priv_two pv) (RelCT.seq dBuild_two (RelCT.seq hashD_two
    (RelCT.seq kdkMac_two (RelCT.seq clLoop_two (RelCT.seq amLoop_two (RelCT.seq maskPart_two
    (RelCT.seq alPart_two (RelCT.seq scanPart_two selPart_ct)))))))))

theorem dec_constantTime (v : Compress) (pv : PrivImpl) :
    ConstantTime isa decK.pre decK.pub (code (HH v) pv.name pv.code) :=
  RelCT.constantTime (relCT_alloc ((body_ct v pv).mono
    (fun _ _ ⟨s₁, s₂, ⟨h₁, h₂, hpub⟩, e₁, e₂⟩ => ⟨s₁, ⟨s₁, ⟨h₁, pub_refl s₁⟩, e₁⟩, ⟨s₂, ⟨h₂, hpub⟩, e₂⟩⟩)
    fun _ _ h => h))

theorem dec_verified (v : Compress) (pv : PrivImpl) :
    Verified target (code (HH v) pv.name pv.code) (Spec.RsaPkcs1Enc.decryptContract abi decStack) :=
  Verified.of_correct (k := decK) (dec_correct v pv) (dec_constantTime v pv) decrypt_implies

/-- It writes `rsp` only in its frame's push and pop, and its callees' own. -/
theorem dec_spSafe (v : Compress) (pv : PrivImpl) :
    (code (HH v) pv.name pv.code).all (fun i => !isa.writesSp i) = true := by
  have K := Proof.Pbkdf2.Md.X86_64.Sha256.callees v
  have hI : (HH v).hmacInit.all (fun i => !isa.writesSp i) = true := (Proof.Pbkdf2.Md.X86_64.Sha256.variant v).hmacInitSp
  have hF : (HH v).hmacFin.all (fun i => !isa.writesSp i) = true := (Proof.Pbkdf2.Md.X86_64.Sha256.variant v).hmacFinSp
  have hU : (HH v).updC.all (fun i => !isa.writesSp i) = true := Code.all_of_allInstrs
    (Proof.Pbkdf2.Md.X86_64.core_updC K.cSp
      (show Proof.Pbkdf2.Md.X86_64.Sha256.coreH.updC.allInstrs _ = true by decide +kernel))
  have hFi : (HH v).finC.all (fun i => !isa.writesSp i) = true := Code.all_of_allInstrs
    (Proof.Pbkdf2.Md.X86_64.core_finC K.cSp
      (show Proof.Pbkdf2.Md.X86_64.Sha256.coreH.finC.allInstrs _ = true by decide +kernel))
  have hIn : (HH v).initC.all (fun i => !isa.writesSp i) = true := Code.all_of_allInstrs K.iSp
  simp only [code, body, dBuild, hashD, kdkMac, clLoop, VG.Impl.RsaPkcs1Enc.X86_64.Decrypt.amLoop, prfBody, maskPart, alPart, scanPart, selPart,
    Code.all, hI, hF, hU, hFi, hIn, pv.spSafe, Bool.and_true, Bool.true_and]
  decide +kernel

end VG.Proof.RsaPkcs1Enc.X86_64.Dec
