module

public import VerifiedGarbage.Proof.Dsa.X86_64.GenerateKeyState
import VerifiedGarbage.Proof.Dsa.X86_64.GenerateKeySampled
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignFinish
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignPublishValue
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Derive
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Dsa.X86_64.GenerateKeyCheckStep
import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-! ### `Dsa.X86_64.GenerateKeyFinish`, which only this module used -/

section

/-! # Key generation's finish: the status, the key or zeros, and the draws used -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

structure KeygenBodyPost (s : State) (result : Spec.Dsa.GenerateKeyResult) (t : State) : Prop where
  sp : t.gpr .rsp = randomBase s
  rd : t.rd = s.rd
  wr : t.wr = ⟨randomBase s, Random.frameBytes⟩ :: s.wr
  status : t.gpr .rax = BitVec.ofNat 64 result.status
  output : Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (s.gpr .rsi).toNat =
    result.key.getD (List.replicate (s.gpr .rsi).toNat 0)
  used : t.mem.readW (s.gpr .rdx) 64 = BitVec.ofNat 64 result.used
  callee : ∀ r ∈ calleeSaved, r ≠ .rsp → t.gpr r = s.gpr r
  mxcsr : t.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10
  nonce : ∀ i < 32, t.mem (off (randomBase s) (200 + i)) = 0

theorem keygen_bytes_zero {m : Mem} {p : Addr} {n : Nat}
    (h : ∀ i < n, m (p + BitVec.ofNat 64 i) = 0) :
    Spec.Rsa.bytesAt m p n = List.replicate n 0 := by
  apply List.ext_getElem (by simp [Spec.Rsa.bytesAt])
  intro i hi _
  simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
  exact h i (by simpa only [bytesAt_length] using hi)

theorem keygen_finish_result {extra : Nat} {s t : State} {h : GenerateKeyABI extra s}
    {result : Spec.Dsa.GenerateKeyResult} (hr : KeygenState h result.used t)
    (hstatus : word t.mem (randomBase s) Random.oStatus = BitVec.ofNat 64 result.status)
    (houtput : result.status = 1 → Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (s.gpr .rsi).toNat =
      result.key.getD (List.replicate (s.gpr .rsi).toNat 0))
    (hbound : result.status ≤ 2) (hkey : result.status ≠ 1 → result.key = none) :
    WP isa RandomSign.finish t (KeygenBodyPost s result) := by
  have houtlen : 0 < (s.gpr .rsi).toNat := by
    have hl := h.lengths
    have ho := h.outLength
    unfold Spec.Dsa.lengthsValid at hl
    omega_using [hl, ho]
  have hptr : word t.mem (randomBase s) Random.oUsedPtr = s.gpr .rdx :=
    hr.saved (56, s.gpr .rdx) (by simp [keygenSavedValues])
  have hframeOut := h.stackOut.sub_left (keygen_frame_sub h)
  have hframeUsed := h.stackUsed.sub_left (keygen_frame_sub h)
  have hsep (d : Nat) (hd : d + 8 ≤ Random.frameBytes) :
      Mem.Sep (off (randomBase s) d) 8 (s.gpr .rdi) (s.gpr .rsi).toNat :=
    (hframeOut.sub_left (Offset.sub_base _ hd)).sep (Region.contains_self _ _) (Region.contains_self _ _)
  have hused : InRegions t.wr (word t.mem (randomBase s) Random.oUsedPtr) 8 := by
    rw [hptr]
    exact ⟨⟨s.gpr .rdx, 8⟩, by rw [hr.wr, h.wr]; simp, Region.contains_self _ _⟩
  have hsepUsed : Mem.Sep (off (randomBase s) Random.oStatus) 8 (word t.mem (randomBase s) Random.oUsedPtr) 8 := by
    rw [hptr]
    exact (hframeUsed.sub_left (Offset.sub_base _ (by decide))).sep (Region.contains_self _ _) (Region.contains_self _ _)
  refine WP.mono_mx (by decide) (random_finish_ok (B := randomBase s) (op := s.gpr .rdi) (k := (s.gpr .rsi).toNat)
    hr.scr hr.sp
    (hr.saved (40, s.gpr .rdi) (by simp [keygenSavedValues]))
    (by simpa only [Random.oOutLen, ofNat_toNat64] using hr.saved (48, s.gpr .rsi) (by simp [keygenSavedValues]))
    houtlen (s.gpr .rsi).isLt
    (fun j hj => ⟨⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, by rw [hr.wr, h.wr]; simp,
      contains_byte _ hj (Nat.le_of_lt (s.gpr .rsi).isLt)⟩)
    hsep hused hsepUsed)
    fun u ⟨hret, ⟨m, hgood, hbad, hwords, hum⟩, hk⟩ hmx => ?_
  have hpM : word m (randomBase s) Random.oUsedPtr = s.gpr .rdx := (hwords _ (by decide)).trans hptr
  have huM : word m (randomBase s) Random.oUsed = BitVec.ofNat 64 result.used := by
    rw [hwords _ (by decide)]
    exact hr.usedWord
  have hkv : Keep randomVolatile t u := hk.mono (by decide)
  refine ⟨(hk.gpr (by decide)).trans hr.sp, hk.2.1.trans hr.rd, hk.2.2.trans hr.wr,
    hret.trans hstatus, ?_, ?_,
    fun r hc hn => (hkv.gpr (random_saved_not_volatile hc)).trans (hr.callee r hc hn),
    by rw [hmx]; exact hr.mxcsr, ?_⟩
  · rw [hum, random_publish_output hframeOut.symm (by
      rw [hpM]; exact h.outUsed.sep (Region.contains_self _ _) (Region.contains_self _ _)) (s.gpr .rsi).isLt]
    by_cases hs : result.status = 1
    · have hw : word t.mem (randomBase s) Random.oStatus = 1 := by rw [hstatus, hs]; rfl
      rw [hgood hw]
      exact houtput hs
    · have hw : word t.mem (randomBase s) Random.oStatus ≠ 1 := by
        intro he
        rw [hstatus] at he
        have hn := congrArg BitVec.toNat he
        change result.status % 2 ^ 64 = 1 at hn
        omega_using [hbound, hs, hn]
      rw [hkey hs]
      exact keygen_bytes_zero (hbad hw)
  · rw [hum, ← hpM, random_publish_used, huM]
  · intro i hi
    rw [hum]
    apply random_publish_nonce_zero _ i hi
    rw [hpM]
    exact (hframeUsed.sub_left (Offset.sub_base _ (by decide))).sep (Region.contains_self _ _) (Region.contains_self _ _)

/-- Key generation's status is at most 2, and only success returns a key. -/
theorem keygen_result_bounds {extra : Nat} {s : State} (h : GenerateKeyABI extra s) :
    (keygenResult s).status ≤ 2 ∧ ((keygenResult s).status ≠ 1 → (keygenResult s).key = none) := by
  by_cases hc : keygenChecked s = true
  · rw [keygen_result_checked h hc]
    cases hx : (keygenDraw s).scalar with
    | none => exact ⟨keygen_sampleStatus_le _, fun _ => rfl⟩
    | some k =>
      dsimp only
      unfold Spec.Dsa.signStatus
      cases hd : Spec.Dsa.deriveKeyBytes (keygenInput s).pLen (keygenInput s).qLen (keygenInput s).params
        (Spec.Dsa.encodeBE (keygenInput s).qLen k) with
      | none => exact ⟨by decide, fun _ => rfl⟩
      | some key => exact ⟨by simp, fun hn => absurd (by simp) hn⟩
  · have hpl : (keygenInput s).params.length = 2 * (keygenInput s).pLen + (keygenInput s).qLen := by
      simp only [keygenInput, bytesAt_length]; exact h.paramsLength
    unfold keygenResult
    rw [VG.Proof.Dsa.generateKeyBytes_eq (pLen := (keygenInput s).pLen) (qLen := (keygenInput s).qLen)
      h.lengths hpl]
    simp only [show Spec.Dsa.checkParametersBytes (keygenInput s).pLen (keygenInput s).qLen (keygenInput s).params
      = false from Bool.eq_false_iff.mpr hc, Bool.false_eq_true, ↓reduceIte]
    exact ⟨by decide, fun _ => trivial⟩

end VG.Proof.Dsa.X86_64

end

end


/-! # Key generation's body: entry, the domain check, generation, the finish -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

theorem keygen_result_unchecked {extra : Nat} {s : State} (h : GenerateKeyABI extra s)
    (hc : keygenChecked s = false) : keygenResult s = ⟨none, 0, 0, [4]⟩ := by
  have hpl : (keygenInput s).params.length = 2 * (keygenInput s).pLen + (keygenInput s).qLen := by
    simp only [keygenInput, bytesAt_length]; exact h.paramsLength
  unfold keygenResult
  rw [VG.Proof.Dsa.generateKeyBytes_eq (pLen := (keygenInput s).pLen) (qLen := (keygenInput s).qLen)
    h.lengths hpl]
  simp only [show Spec.Dsa.checkParametersBytes (keygenInput s).pLen (keygenInput s).qLen (keygenInput s).params
    = false from hc, Bool.false_eq_true, ↓reduceIte]

theorem keygen_test_check {t : State} :
    WP isa (.block [.mov32 .rax (.reg .rax), .alu .cmp .rax (.imm 0)]) t fun u =>
      (u.mem = t.mem ∧ u.zf = some (((t.gpr .rax).setWidth 32).toNat == 0)) ∧ Keep [.rax] t u := by
  refine WP.keep [.rax] ?_ rfl
  xrun []
  rw [sub_beq_zero]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  have hz : BitVec.signExtend 64 (0 : BitVec 32) = 0 := by decide
  rw [hz]
  constructor
  · intro he
    have hn := congrArg BitVec.toNat he
    simp only [BitVec.toNat_setWidth] at hn ⊢
    rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide : 2 ^ 32 ≤ 2 ^ 64))] at hn
    exact hn
  · intro he
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, he, Nat.zero_mod]
    rfl

theorem keygen_body (v : Backend) {s : State} (h : GenerateKeyABI v.stack s) :
    WP isa (GenerateKey.body (keygenCheckName v) (keygenDeriveName v)
      (Generate.checkParameters v.sq v.mul) (Generate.deriveChecked v.sq v.mul))
      (allocState Random.frameBytes s) (KeygenBodyPost s (keygenResult s)) := by
  have hb := keygen_result_bounds h
  unfold GenerateKey.body
  refine WP.seq (WP.mono (keygen_head h) fun t ⟨ht, hst, hQ, hdi, hsi, hdx, hcx, h8, h9⟩ => ?_)
  refine WP.seq (WP.mono (keygen_check_step v ht hdi hsi hdx hcx h8 h9) fun u ⟨hu, hw, hax⟩ => ?_)
  refine WP.seq (WP.mono_mx (by decide) (keygen_test_check (t := u)) fun w ⟨⟨hwm, hwz⟩, hkw⟩ hmxw => ?_)
  have hsw : KeygenState h 0 w :=
    hu.of_frame (by rw [hwm]; exact InScr.refl _ _ _) (fun d _ _ => by rw [hwm]) (hkw.mono (by decide))
      (by rw [hmxw])
  have hword (d : Nat) (hd : d + 8 ≤ Random.frameBytes) : word w.mem (randomBase s) d = word t.mem (randomBase s) d := by
    rw [hwm]; exact hw d hd
  refine WP.seq ?_
  cases hc : keygenChecked s with
  | false =>
    rw [hc] at hax
    refine WP.ite true (by simp only [eval, hwz, hax]; rfl) (fun _ => WP.block_nil ?_)
      (fun he => Bool.noConfusion he)
    have hr := keygen_result_unchecked h hc
    rw [hr] at hb ⊢
    exact keygen_finish_result hsw (by rw [hword _ (by decide), hst]; rfl) (fun he => absurd he (by decide))
      hb.1 hb.2
  | true =>
    rw [hc] at hax
    refine WP.ite false (by simp only [eval, hwz, hax]; rfl) (fun he => Bool.noConfusion he) fun _ => ?_
    refine WP.mono (keygen_generate v hsw (by rw [hword _ (by decide)]; exact hQ) hc)
      fun x ⟨hx, hxs, hxo⟩ => keygen_finish_result hx hxs hxo hb.1 hb.2

end VG.Proof.Dsa.X86_64
