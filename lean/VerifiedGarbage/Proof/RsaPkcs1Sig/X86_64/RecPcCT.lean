module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.RecoverCT
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCT
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCorrect
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.Compare
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.RecoverCT
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCT
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCorrect
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.Compare
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncTail
import VerifiedGarbage.Proof.Rsa.BytesFrame
import Mathlib.Data.Int.GCD
public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86_64.RecoverPrecomputed
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.RecoverCorrect
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaPkcs1Sig.Verify
public import VerifiedGarbage.Spec.RsaPkcs1Sig.Precomputed
public import VerifiedGarbage.Proof.Rsa.X86_64.PublicImpl
import Mathlib.Basic.IsEmpty.Defs
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncTail
meta import VerifiedGarbage.Proof.Rsa.BytesFrame
meta import Mathlib.Data.Int.GCD
meta import VerifiedGarbage.Impl.RsaPkcs1Sig.X86_64.RecoverPrecomputed
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.RecoverCorrect
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.Verify
meta import VerifiedGarbage.Spec.RsaPkcs1Sig.Precomputed
meta import VerifiedGarbage.Proof.Rsa.X86_64.PublicImpl
meta import Mathlib.Basic.IsEmpty.Defs

/-! ### `RsaPkcs1Sig.X86_64.RecPcContract`, which only this module used -/

section

/-! ### `RsaPkcs1Sig.X86_64.RecPcCorrect`, which only this module used -/

section

/-! ### `RsaPkcs1Sig.X86_64.RecPcTail`, which only this module used -/

section

/-!
# `vg_rsa_pkcs1_recover_precomputed` on x86-64: after the call

Whatever the call left in `EM₁` and returned: the encoding of the last
`out_len` bytes of `EM₁`, its comparison with `EM₁`, and the masked release
(`afterPub_ok`), whose result is `relOut` of the call's status and `EM₁`.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.X86_64.RecPc

open VG VG.X86_64 VG.Impl.RsaPkcs1Sig.X86_64 VG.Impl.RsaPkcs1Sig.X86_64.Recover
open VG.Impl.RsaPkcs1Sig.X86_64.RecoverPrecomputed (maskM maskArgs fin)
open VG.Impl.RsaPkcs1Sig.X86_64.Verify (frameBytes oEM1 oEM2 sp arg arg0 lea test0 cmpArgs)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Sig.X86_64 Rec
open VG.Proof.RsaPkcs1Sig.X86_64.Ver (fb kb stkR scrR fb_eq frame_sub ea_sp sub_refl slot_keep test0_ok
  word_wo word_wo0 word_self0 bytesAt_eq_iff setWidth_byte_eq_zero)
open VG.WriteBytes
open VG.Proof.RsaPkcs1Enc.X86_64 (pmask maskLoop_ok contains_of_byte)

/-- The mask of `maskM`: whether the comparison found no difference and the
call's status is not 0. -/
def okOf (d st : BitVec 64) : Bool := (d == 0) && (st.setWidth 32 != 0)

theorem lt1_eq {n : Nat} (x : BitVec n) : decide (x.toNat < 1) = (x == 0) := by
  by_cases h : x = 0
  · subst h; simp
  · have : x.toNat ≠ 0 := fun h' => h (BitVec.eq_of_toNat_eq (by simp [h']))
    rw [show (x == 0) = false from beq_eq_false_iff_ne.mpr h]
    exact decide_eq_false (by omega_arith)

theorem maskM_val (d st : BitVec 64) :
    (0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide (d.toNat < 1)))) &&&
      ((0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide ((st.setWidth 32).toNat < 1)))) ^^^
        BitVec.signExtend 64 (BitVec.ofInt 32 (-1))) = pmask (okOf d st) := by
  rw [lt1_eq, lt1_eq]
  unfold okOf pmask
  rw [bne]
  cases (d == 0) <;> cases (st.setWidth 32 == 0) <;> decide

theorem maskM_ok {s t : State} (hp : PreR s) (he : Env s t) :
    WP isa (.block maskM) t fun u => Keep [.rdx, .rax] t u ∧
      u.mem = t.mem.writeW (off (fb s) 8) (pmask (okOf (t.gpr .rdx) (word t.mem (fb s) 0))) ∧
      u.gpr .rdx = pmask (okOf (t.gpr .rdx) (word t.mem (fb s) 0)) := by
  obtain hs := he.scr hp
  refine WP.mono (WP.keep [.rdx, .rax] (Q := fun u =>
      u.mem = t.mem.writeW (off (fb s) 8) (pmask (okOf (t.gpr .rdx) (word t.mem (fb s) 0))) ∧
      u.gpr .rdx = pmask (okOf (t.gpr .rdx) (word t.mem (fb s) 0))) ?_ rfl) fun u ⟨h, k⟩ => ⟨k, h⟩
  obtain h0 : InRegions (t.rd ++ t.wr) (fb s) 8 := by
    simpa only [off, BitVec.add_zero] using hs.ld (d := 0) (by decide)
  xrun [maskM, ea_sp, he.rsp, h0, hs.st (d := 8) (by decide)]
  obtain hw : Bignum.word t.mem (fb s) 0 = t.mem.readW (fb s) 64 := by simp only [Bignum.word, off, BitVec.add_zero]
  rw [hw, show (1 : BitVec 64).toNat = 1 from rfl, show (1 : BitVec 32).toNat = 1 from rfl, maskM_val]
  exact ⟨rfl, rfl⟩

/-- `Env` past a store to the frame's word at `d < 32`, under the slots. -/
theorem Env.low {s t u : State} (he : Env s t) {d : Nat} (hd : d + 8 ≤ 32) {v : BitVec 64}
    (hsp : u.gpr .rsp = t.gpr .rsp) (hrd : u.rd = t.rd) (hwr : u.wr = t.wr)
    (hm : u.mem = t.mem.writeW (off (fb s) d) v) : Env s u := by
  obtain hf : Frame [⟨off (fb s) d, 8⟩] t.mem u.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain hw : ∀ {d'}, 32 ≤ d' → d' + 8 ≤ 4096 → Bignum.word u.mem (fb s) d' = Bignum.word t.mem (fb s) d' :=
    fun h₁ h₂ => by rw [hm]; exact word_wo _ _ _ (.inl (by omega_arith)) (by omega_arith) h₂
  exact ⟨hsp.trans he.rsp, hrd.trans he.rd, hwr.trans he.wr,
    frame_call he.mem hf fun r hr => by
      rw [List.mem_singleton.mp hr]; exact .inl (frame_sub s (by unfold frameBytes; omega_arith)),
    (hw (by decide) (by decide)).trans he.sOut, (hw (by decide) (by decide)).trans he.sOl,
    (hw (by decide) (by decide)).trans he.sN, (hw (by decide) (by decide)).trans he.sK,
    (hw (by decide) (by decide)).trans he.sE, (hw (by decide) (by decide)).trans he.sEl⟩

/-- Bytes of the frame from `EM₁` on, past a store to a word below `32`. -/
theorem bytes_low {s : State} {m : Mem} {d : Nat} (hd : d + 8 ≤ 32) (v : BitVec 64) {e n : Nat}
    (he : oEM1 ≤ e) (hn : e + n ≤ frameBytes) :
    Spec.Rsa.bytesAt (m.writeW (off (fb s) d) v) (off (fb s) e) n = Spec.Rsa.bytesAt m (off (fb s) e) n := by
  obtain hf : Frame [⟨off (fb s) d, 8⟩] m (m.writeW (off (fb s) d) v) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => hf.bytes (R := ⟨off (fb s) e, n⟩) (fun r hr => ?_)
    (by show n ≤ 2 ^ 64; unfold frameBytes at hn; omega_arith) (List.mem_range.mp hi)
  rw [List.mem_singleton.mp hr]
  exact Offset.disjoint _ (.inr (by unfold oEM1 at he; omega_arith)) (by unfold frameBytes at hn; omega_arith) (by omega_arith)

theorem maskArgs_ok {s t : State} (hp : PreR s) (he : Env s t) :
    WP isa (.block maskArgs) t fun u => Keep [.rdi, .rcx, .rdx, .r10] t u ∧ u.mem = t.mem ∧
      u.gpr .rdi = s.gpr .rdi ∧ u.gpr .rcx = s.gpr .rsi ∧ u.gpr .rdx = Bignum.word t.mem (fb s) 8 ∧
      u.gpr .r10 = BitVec.ofNat 64 0 := by
  obtain hs := he.scr hp
  refine WP.mono (WP.keep [.rdi, .rcx, .rdx, .r10] (Q := fun u => u.mem = t.mem ∧
      u.gpr .rdi = s.gpr .rdi ∧ u.gpr .rcx = s.gpr .rsi ∧ u.gpr .rdx = Bignum.word t.mem (fb s) 8 ∧
      u.gpr .r10 = BitVec.ofNat 64 0) (by
    xrun [maskArgs, ea_sp, he.rsp, hs.ld (d := oOut) (by decide), hs.ld (d := oOl) (by decide),
      hs.ld (d := 8) (by decide), he.sOut, he.sOl]) rfl) fun u ⟨h, k⟩ => ⟨k, h⟩

theorem pmask_and1 (ok : Bool) : ((pmask ok &&& 1#64).setWidth 32 : BitVec 32) = if ok then 1 else 0 := by
  cases ok <;> decide

/-- The release: the value to `out`, then `out` and the result masked by
`okOf` of the comparison's difference and the saved status. -/
theorem release_ok {s t : State} (hp : PreR s) (he : Env s t) (hcx : t.gpr .rcx = s.gpr .rcx) :
    WP isa RecoverPrecomputed.release t fun u => Env s u ∧
      Spec.Rsa.written u.mem (s.gpr .rdi) (s.gpr .rsi).toNat ((u.gpr .rax).setWidth 32)
        (if okOf (t.gpr .rdx) (Bignum.word t.mem (fb s) 0) then
          some (Spec.Rsa.bytesAt t.mem (valA s) (s.gpr .rsi).toNat) else none) := by
  have hk1 := hp.k1
  have hk2 := hp.k2
  have ol := hp.ol
  obtain hF := fb_toNat hp
  have e1 : oEM1 = 80 := rfl
  have e2 : frameBytes = 2136 := rfl
  have e3 : Impl.RsaPkcs1Enc.X86_64.Encrypt.oEM = 80 := rfl
  set ok := okOf (t.gpr .rdx) (Bignum.word t.mem (fb s) 0)
  set n := (s.gpr .rsi).toNat with hn
  unfold RecoverPrecomputed.release
  refine WP.seq (WP.mono (maskM_ok hp he) fun t₁ ⟨k₁, hm₁, _⟩ => ?_)
  obtain he₁ : Env s t₁ := Env.low he (d := 8) (by decide) (k₁.gpr (by decide)) k₁.2.1 k₁.2.2 hm₁
  obtain hv₁ : Spec.Rsa.bytesAt t₁.mem (valA s) n = Spec.Rsa.bytesAt t.mem (valA s) n := by
    rw [hm₁]
    exact bytes_low (s := s) (d := 8) (by decide) _ (e := oEM1 + ((s.gpr .rcx).toNat - n)) (by omega_arith) (by omega_arith)
  refine WP.seq (WP.mono (copyOut_ok hp he₁ (by rw [k₁.gpr (by decide), hcx])) fun t₂ ⟨he₂, _, hout₂, hm₂⟩ => ?_)
  obtain hw8 : Bignum.word t₂.mem (fb s) 8 = pmask ok := by
    rw [hm₂, slot_keep (frame_writeBytes _ _ _) (fun r hr => ?_), hm₁, word_writeW_self]
    rw [List.mem_singleton.mp hr, bytesAt_length]
    exact (hp.dKo.sub_left (frame_sub s (by unfold frameBytes; omega_arith)))
  refine WP.seq (WP.mono (maskArgs_ok hp he₂) fun t₃ ⟨k₃, hm₃, hdi₃, hcx₃, hdx₃, h10₃⟩ => ?_)
  obtain he₃ : Env s t₃ := he₂.regs (k₃.gpr (by decide)) hm₃ k₃.2.1 k₃.2.2
  obtain hwr : outR s ∈ t₃.wr := by rw [he₃.wr, hp.hwr]; simp [outR]
  obtain hdK : (⟨off (fb s) Impl.RsaPkcs1Enc.X86_64.Encrypt.oEM, n⟩ : Region).Disjoint (outR s) :=
    hp.dKo.sub_left (frame_sub s (by unfold frameBytes; omega_arith))
  refine WP.seq (WP.mono (maskLoop_ok (k := n) (S := fb s) (op := s.gpr .rdi) (ok := ok) (by omega_arith)
    (by omega_arith) he₃.rsp hdi₃ (by rw [hdx₃, hw8]) (by rw [hcx₃, hn]; simp) h10₃ (out_wr hwr)
    (fun i hi => by rw [he₃.wr]; exact frame_bytes' hp (by unfold frameBytes; omega_arith) i hi)
    (fun i hi i' hi' => ne_of_disjoint hdK.symm (by omega_arith) (by omega_arith) hi hi')) fun t₄ hR => ?_)
  refine WP.mono (WP.keep [.rax] (Q := fun u => u.mem = t₄.mem ∧ u.gpr .rax = t₄.gpr .rdx &&& 1#64) (by
    xrun [fin]; rfl) rfl) fun u ⟨⟨hm, hax⟩, k⟩ => ⟨?_, ?_⟩
  · have hrdx : t₄.gpr .rdx = pmask ok := by rw [hR.keep.gpr (by decide), hdx₃, hw8]
    refine Env.of he₂ hp ((k.gpr (by decide)).trans ((hR.keep.gpr (by decide)).trans (k₃.gpr (by decide))))
      (k.2.1.trans (hR.keep.2.1.trans k₃.2.1)) (k.2.2.trans (hR.keep.2.2.trans k₃.2.2))
      (rs := [outR s, ⟨off (fb s) 80, n⟩]) (fun x hx => ?_) fun r hr => ?_
    · rw [hm, hR.frame x (fun i hi he' => hx _ (List.mem_cons_self ..) (by
          rw [he']; exact contains_of_byte rfl (by omega_arith) hi))
        (fun i hi he' => hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) (by
          rw [he']; exact contains_of_byte rfl (by omega_arith) hi)), hm₃]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inr rfl
      · exact .inl ⟨80, n, rfl, le_refl _, by omega_arith⟩
  · have hrdx : t₄.gpr .rdx = pmask ok := by rw [hR.keep.gpr (by decide), hdx₃, hw8]
    rw [hax, hrdx, pmask_and1]
    obtain hb : Spec.Rsa.bytesAt u.mem (s.gpr .rdi) n =
        if ok then Spec.Rsa.bytesAt t.mem (valA s) n else List.replicate n 0 := by
      split
      · rename_i hok
        rw [← hv₁, ← hout₂]
        simp only [Spec.Rsa.bytesAt, hm]
        exact List.map_congr_left fun i hi => by
          rw [hR.out i (List.mem_range.mp hi), hm₃]; simp only [hok, ↓reduceIte]
      · rename_i hok
        simp only [Spec.Rsa.bytesAt, hm]
        refine List.ext_getElem (by simp) fun i h₁ _ => ?_
        simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
        rw [hR.out i (by simpa using h₁)]; simp only [hok, Bool.false_eq_true, ↓reduceIte]
    cases hok : ok
    · simp only [hok, Bool.false_eq_true, ↓reduceIte] at hb ⊢; exact ⟨rfl, hb⟩
    · simp only [hok, ↓reduceIte] at hb ⊢; exact ⟨rfl, hb⟩

/-- After the encoding into `EM₂`, whose result is `o`, with the call's
status `st` in slot 0: the comparison with `EM₁` and the masked release. -/
theorem tail_ok {s t₂ t₃ : State} (hp : PreR s) (he₂ : Env s t₂) (hK₃ : Keep clob t₂ t₃) {h : Spec.RsaPkcs1Sig.Hash}
    {em : List Byte} {st : BitVec 64} (hcx₂ : t₂.gpr .rcx = s.gpr .rcx) (h8₂ : t₂.gpr .r8 = off (fb s) oEM2)
    (hem : Spec.Rsa.bytesAt t₂.mem (off (fb s) oEM1) (s.gpr .rcx).toNat = em)
    (hval : Spec.Rsa.bytesAt t₂.mem (valA s) (s.gpr .rsi).toNat = em.drop ((s.gpr .rcx).toNat - (s.gpr .rsi).toNat))
    (hst : Bignum.word t₂.mem (fb s) 0 = st)
    {o : Option (List Byte)} (ho : Spec.RsaPkcs1Sig.encode h (em.drop ((s.gpr .rcx).toNat - h.len))
      (s.gpr .rcx).toNat = o)
    (hpost : EOut t₂ t₃ o) :
    WP isa RecoverPrecomputed.tail t₃ fun u => Env s u ∧ Spec.Rsa.written u.mem (s.gpr .rdi) (s.gpr .rsi).toNat
      ((u.gpr .rax).setWidth 32)
      (if st.setWidth 32 ≠ 0 ∧ o = some em then some (em.drop ((s.gpr .rcx).toNat - (s.gpr .rsi).toNat))
        else none) := by
  have hk1 := hp.k1
  have hk2 := hp.k2
  have ol := hp.ol
  obtain hF := fb_toNat hp
  set k := (s.gpr .rcx).toNat with hkdef
  obtain dVE : (⟨valA s, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨off (fb s) oEM2, k⟩ :=
    Offset.disjoint _ (.inl (by unfold oEM1 oEM2; omega_arith)) (by unfold oEM1 frameBytes at *; omega_arith)
      (by unfold oEM2 frameBytes at *; omega_arith)
  unfold RecoverPrecomputed.tail
  refine WP.seq (WP.mono (test0_ok t₃) fun t₄ ⟨hs₄, hz₄⟩ => ?_)
  cases o with
  | none =>
    obtain ⟨hax, hm₃⟩ := hpost
    obtain he₄ : Env s t₄ := he₂.regs (by rw [hs₄.1, hK₃.gpr (by decide)]) (hs₄.2.1.trans hm₃)
      (hs₄.2.2.1.trans hK₃.2.1) (hs₄.2.2.2.trans hK₃.2.2)
    refine WP.ite true (by simp [eval, hz₄, hax]) (fun _ => ?_) (by simp)
    simp only [reduceCtorEq, and_false, ↓reduceIte]
    exact zeroSlots_ok hp he₄
  | some em' =>
    obtain ⟨hax, hm₃⟩ := hpost
    obtain hl' : em'.length = k := VG.Proof.RsaPkcs1Sig.encode_length ho
    obtain he₃ : Env s t₃ := Env.of he₂ hp (hK₃.gpr (by decide)) hK₃.2.1 hK₃.2.2 (hm₃ ▸ frame_writeBytes _ _ _)
      fun r hr => .inl ⟨oEM2, k, by rw [List.mem_singleton.mp hr, h8₂, hl'], by decide,
        by unfold oEM2 frameBytes; omega_arith⟩
    obtain he₄ : Env s t₄ := he₃.regs (by rw [hs₄.1]) hs₄.2.1 hs₄.2.2.1 hs₄.2.2.2
    refine WP.ite false (by simp [eval, hz₄, hax]) (by simp) (fun _ => ?_)
    refine WP.seq (WP.mono (cmpArgs_ok he₄) fun t₅ ⟨hK₅, hm₅, hdi₅, hsi₅⟩ => ?_)
    obtain hcx₅ : t₅.gpr .rcx = s.gpr .rcx := by
      rw [hK₅.gpr (by decide), hs₄.1, hK₃.gpr (by decide), hcx₂]
    obtain he₅ : Env s t₅ := he₄.regs (hK₅.gpr (by decide)) hm₅ hK₅.2.1 hK₅.2.2
    obtain hr5 : InRegions (t₅.rd ++ t₅.wr) (t₅.gpr .rdi) k ∧ InRegions (t₅.rd ++ t₅.wr) (t₅.gpr .rsi) k := by
      rw [hdi₅, hsi₅, he₅.wr]
      obtain ⟨r₁, h₁, c₁⟩ := frame_span' hp (d := oEM1) (n := k) (by unfold oEM1 frameBytes; omega_arith)
      obtain ⟨r₂, h₂, c₂⟩ := frame_span' hp (d := oEM2) (n := k) (by unfold oEM2 frameBytes; omega_arith)
      exact ⟨⟨r₁, List.mem_append_right _ h₁, c₁⟩, ⟨r₂, List.mem_append_right _ h₂, c₂⟩⟩
    refine WP.seq (WP.mono (compare_ok (by rw [hcx₅]) (by omega_arith) hr5) fun t₆ ⟨hK₆, hm₆, hdx₆⟩ => ?_)
    obtain he₆ : Env s t₆ := he₅.regs (hK₆.gpr (by decide)) hm₆ hK₆.2.1 hK₆.2.2
    obtain hmem : ∀ {p : Addr} {n : Nat}, (⟨p, n⟩ : Region).Disjoint ⟨off (fb s) oEM2, em'.length⟩ → n ≤ 2 ^ 64 →
        Spec.Rsa.bytesAt t₃.mem p n = Spec.Rsa.bytesAt t₂.mem p n := fun {p n} hd hn => by
      rw [hm₃, h8₂]
      simp only [Spec.Rsa.bytesAt]
      exact List.map_congr_left fun i hi =>
        (frame_writeBytes t₂.mem _ em').bytes (R := ⟨p, n⟩) (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd)
          hn (List.mem_range.mp hi)
    obtain d12 : (⟨off (fb s) oEM1, k⟩ : Region).Disjoint ⟨off (fb s) oEM2, em'.length⟩ := by
      rw [hl']
      exact Offset.disjoint _ (.inl (by unfold oEM1 oEM2; omega_arith)) (by unfold oEM1 frameBytes at *; omega_arith)
        (by unfold oEM2 frameBytes at *; omega_arith)
    obtain h1 : Spec.Rsa.bytesAt t₃.mem (off (fb s) oEM1) k = em := by
      rw [hmem d12 (by omega_arith), hem]
    obtain h2 : Spec.Rsa.bytesAt t₃.mem (off (fb s) oEM2) k = em' := by
      have := bytesAt_writeBytes t₂.mem (off (fb s) oEM2) em' (by omega_arith)
      rw [hl'] at this
      rw [hm₃, h8₂]; exact this
    obtain hdiff : (t₆.gpr .rdx = 0) ↔ em = em' := by
      rw [hdx₆, hdi₅, hsi₅, EqBytes, ← bytesAt_eq_iff, hm₅, hs₄.2.1, h1, h2]
    obtain hw0 : Bignum.word t₆.mem (fb s) 0 = st := by
      rw [hm₆, hm₅, hs₄.2.1, hm₃, h8₂, slot_keep (frame_writeBytes _ _ _) (fun r hr => ?_), hst]
      rw [List.mem_singleton.mp hr, hl']
      exact Offset.disjoint _ (.inl (by unfold oEM2; omega_arith)) (by decide)
        (by unfold oEM2 frameBytes at *; omega_arith)
    obtain hv : Spec.Rsa.bytesAt t₆.mem (valA s) (s.gpr .rsi).toNat = em.drop (k - (s.gpr .rsi).toNat) := by
      rw [hm₆, hm₅, hs₄.2.1, hmem (by rw [hl']; exact dVE) (by omega_arith), hval]
    refine WP.mono (release_ok hp he₆ (by rw [hK₆.gpr (by decide), hcx₅])) fun u ⟨heu, hwu⟩ => ⟨heu, ?_⟩
    rw [hw0, hv] at hwu
    by_cases hq : st.setWidth 32 ≠ 0 ∧ em = em'
    · have hok : okOf (t₆.gpr .rdx) st = true := by
        simp only [okOf, hdiff.2 hq.2, beq_self_eq_true, Bool.true_and, bne_iff_ne, ne_eq]; exact hq.1
      rw [hok] at hwu
      rw [ite_eq_left ⟨hq.1, by rw [hq.2]⟩]; exact hwu
    · have hok : okOf (t₆.gpr .rdx) st = false := by
        simp only [okOf, Bool.and_eq_false_iff, beq_eq_false_iff_ne, bne_eq_false_iff_eq]
        by_cases hz : st.setWidth 32 = 0
        · exact .inr hz
        · exact .inl fun h' => hq ⟨hz, hdiff.1 h'⟩
      rw [hok] at hwu
      rw [ite_eq_right (fun ⟨h₁, h₂⟩ => hq ⟨h₁, (Option.some.inj h₂).symm⟩)]; exact hwu

/-- Recovery's result from the call's status `st` and `EM₁` = `em`. -/
def relOut (k : Nat) (h : Spec.RsaPkcs1Sig.Hash) (st : BitVec 64) (em : List Byte) : Option (List Byte) :=
  if st.setWidth 32 ≠ 0 ∧ Spec.RsaPkcs1Sig.encode h (em.drop (k - h.len)) k = some em then
    some (em.drop (k - h.len)) else none

theorem save_ok {s t : State} (hp : PreR s) (he : Env s t) :
    WP isa (.block [.store (sp 0) .rax]) t fun u => Keep [] t u ∧
      u.mem = t.mem.writeW (off (fb s) 0) (t.gpr .rax) := by
  obtain hs := he.scr hp
  obtain h0 : InRegions t.wr (fb s) 8 := by simpa only [off, BitVec.add_zero] using hs.st (d := 0) (by decide)
  refine WP.mono (WP.keep [] (Q := fun u => u.mem = t.mem.writeW (off (fb s) 0) (t.gpr .rax)) (by
    xrun [ea_sp, he.rsp, h0]) rfl) fun u ⟨h, k⟩ => ⟨k, h⟩

/-- After the call, whatever it left: the status to slot 0, the encoding,
the comparison and the masked release. -/
theorem afterPub_ok {s t : State} (hp : PreR s) (he : Env s t) {h : Spec.RsaPkcs1Sig.Hash}
    (hid : Spec.RsaPkcs1Sig.Hash.ofId ((stackArg s 0).setWidth 32).toNat = some h) :
    WP isa RecoverPrecomputed.afterPub t fun u => Env s u ∧ Spec.Rsa.written u.mem (s.gpr .rdi)
      (s.gpr .rsi).toNat ((u.gpr .rax).setWidth 32)
      (relOut (s.gpr .rcx).toNat h (t.gpr .rax) (Spec.Rsa.bytesAt t.mem (off (fb s) oEM1) (s.gpr .rcx).toNat)) := by
  have hk1 := hp.k1
  have hk2 := hp.k2
  have ol := hp.ol
  obtain hF := fb_toNat hp
  obtain hol : (s.gpr .rsi).toNat = h.len := by
    obtain ⟨h', hid', hl⟩ := hp.hash; rw [hid] at hid'; cases hid'; exact hl
  set k := (s.gpr .rcx).toNat with hkdef
  set em := Spec.Rsa.bytesAt t.mem (off (fb s) oEM1) k
  unfold RecoverPrecomputed.afterPub
  rw [WP.seq_iff, WP.block_append_iff]
  refine WP.mono (save_ok hp he) fun t₁ ⟨k₁, hm₁⟩ => ?_
  obtain he₁ : Env s t₁ := Env.low he (d := 0) (by decide) (k₁.gpr (by decide)) k₁.2.1 k₁.2.2 hm₁
  refine WP.mono (encArgs_ok hp he₁) fun t₂ ⟨hK₂, hm₂, h8₂, hcx₂, hdx₂, h9₂, hsi₂⟩ => ?_
  obtain he₂ : Env s t₂ := he₁.regs (hK₂.gpr (by decide)) hm₂ hK₂.2.1 hK₂.2.2
  obtain hem : Spec.Rsa.bytesAt t₂.mem (off (fb s) oEM1) k = em := by
    rw [hm₂, hm₁]; exact bytes_low (by decide) _ (le_refl _) (by unfold oEM1 frameBytes; omega_arith)
  obtain hst : Bignum.word t₂.mem (fb s) 0 = t.gpr .rax := by
    rw [hm₂, hm₁]; exact word_writeW_self _ _ _ _
  obtain hval : Spec.Rsa.bytesAt t₂.mem (valA s) (s.gpr .rsi).toNat = em.drop (k - (s.gpr .rsi).toNat) := by
    rw [valBytes hp, hem]
  obtain hE : ∀ H, encodeId ((stackArg s 0).setWidth 32) H k = Spec.RsaPkcs1Sig.encode h H k := fun H => by
    simp only [encodeId, hid]
  refine WP.seq (WP.mono (encode_ok (encPre hp he₂ h8₂ hcx₂ hdx₂ h9₂ hsi₂)) fun t₃ ⟨hK₃, hpost⟩ => ?_)
  rw [hsi₂, h9₂, hval, hE, hol] at hpost
  refine WP.mono (tail_ok (h := h) hp he₂ hK₃ hcx₂ h8₂ hem hval hst rfl hpost) fun u ⟨heu, hwu⟩ => ⟨heu, ?_⟩
  simp only [relOut, hol] at hwu ⊢
  exact hwu

end VG.Proof.RsaPkcs1Sig.X86_64.RecPc

end

end

/-! ### `RsaPkcs1Sig.X86_64.RecPcCall`, which only this module used -/

section

/-! ### `RsaPkcs1Sig.X86_64.RecPcCtx`, which only this module used -/

section

/-!
# `vg_rsa_pkcs1_recover_precomputed` on x86-64: the precondition

The shared contract's precondition, by name (`PPreR`): `PreR` for the
original arguments, which the code reads as `vg_rsa_pkcs1_recover` does, and
the precomputed values `pre` (`pre_len` words), the stack arguments 5 and 6,
which only the call reads.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.X86_64.RecPc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Sig.X86_64 Rec
open VG.Proof.RsaPkcs1Sig.X86_64.Ver (fb kb stkR scrR)

/-- The precomputed values, in bytes. -/
def preR (s : State) : Region := ⟨stackArg s 5, (stackArg s 6).toNat * 8⟩

/-- All seven stack arguments. -/
def argsR (s : State) : Region := ⟨stackArgAddr s 0, 56⟩

/-- The precondition of the original function, and the cache. -/
structure PPreR (s : State) : Prop extends PreR s where
  sp3 : (s.gpr .rsp).toNat + 64 ≤ 2 ^ 64
  args : InRegions s.rd (stackArgAddr s 0) 56
  pre : InRegions s.rd (stackArg s 5) ((stackArg s 6).toNat * 8)
  argsOut : (argsR s).Disjoint (outR s)
  argsScr : (argsR s).Disjoint (scrR s)
  argsStack : (argsR s).Disjoint (stkR s)
  preOut : (preR s).Disjoint (outR s)
  preScr : (preR s).Disjoint (scrR s)
  preStack : (preR s).Disjoint (stkR s)
  preWrap : (stackArg s 5).toNat + (stackArg s 6).toNat * 8 ≤ 2 ^ 64
  preLen : (stackArg s 6).toNat = Spec.Rsa.precomputedWords (s.gpr .rcx).toNat

theorem stackArgs_seven (s : State) :
    (List.range 7).map (stackArg s) = [stackArg s 0, stackArg s 1, stackArg s 2,
      stackArg s 3, stackArg s 4, stackArg s 5, stackArg s 6] := rfl

theorem pre_of {s : State}
    (h : (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi verStack).pre s) : PPreR s := by
  sig_pre [Spec.RsaPkcs1Sig.recoverPrecomputedContract, Spec.RsaPkcs1Sig.recoverPrecomputedSig,
    abi, argRegs, verStack, stackArgs_seven, List.append_eq, List.range, List.range.loop] at h
  obtain ⟨sp1, sp3, hrd, hwr, dOn, dOe, dOg, dOs, dOq, dOa, dns, des, dgs, dsq, dsa,
    dRo, -, -, -, dRs, -, -, dKo, dKn, dKe, dKg, dKs, dKq, dKa,
    wO, wN, wE, wG, wS, wQ, ⟨k1, k2⟩, L1, L2, hash, hsl, pl⟩ := h
  obtain ha : Region.Sub ⟨stackArgAddr s 0, 40⟩ ⟨stackArgAddr s 0, 56⟩ := Region.sub_prefix (by decide)
  refine ⟨⟨sp1, by omega_using [sp3], ?_, hwr, dOn, dOe, dOg, dOs, dOa.sub_right ha, dns, des, dgs, dsa.sub_right ha, dRo,
    dRs, dKo, dKn, dKe, dKg, dKs, dKa.sub_right ha, wO, wN, wE, wG, wS, k1, k2, L1, L2, hash,
    hsl⟩,
    sp3, ?_, ?_, dOa.symm, dsa.symm, dKa.symm, dOq.symm, dsq.symm, dKq.symm, wQ, pl⟩
  · rw [hrd]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨_, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨_, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨⟨stackArgAddr s 0, 56⟩, by simp, 0, (BitVec.add_zero _).symm, by dsimp only; decide⟩
  · exact ⟨_, by rw [hrd]; simp, Region.contains_self _ _⟩
  · exact ⟨_, by rw [hrd]; simp, Region.contains_self _ _⟩

end VG.Proof.RsaPkcs1Sig.X86_64.RecPc

end

end


/-!
# `vg_rsa_pkcs1_recover_precomputed` on x86-64: the call

The original arguments of the public operation, then `pre` and `pre_len`
from the stack arguments 5 and 6 (`pubArgs_ok`); the precondition of
`vg_rsa_public_precomputed_checked` (`call_pre`), and what the call leaves
(`call_ok`): `Env`, and, if `pre` holds the values for `n`, RSAVP1 of the
signature in `EM₁`.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.X86_64.RecPc

open VG VG.X86_64 VG.Impl.RsaPkcs1Sig.X86_64.Recover
open VG.Impl.RsaPkcs1Sig.X86_64.Verify (frameBytes oEM1 oEM2 sp arg arg0 lea)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Sig.X86_64 Rec
open VG.Proof.RsaPkcs1Sig.X86_64.Ver (fb kb stkR scrR fb_eq fb_sub8 toNat_off frame_sub below_sub
  arg_ea stackArg_entry stackArgAddr_entry callEntry_frame sub_refl slot_keep)
open VG.Proof.Rsa.X86_64 (PublicImpl pdChkContract)

/-! ## The arguments -/

theorem arg_keep {s t : State} (hp : PPreR s) (he : Env s t) {j : Nat} (hj : j < 7) :
    t.mem.readW (stackArgAddr s j) 64 = stackArg s j := by
  refine he.mem.readW (r := argsR s) ?_ (fun r hr => ?_) (by decide)
  · rw [Ver.stackArgAddr_eq s j]
    exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.argsStack
    · exact hp.argsOut
    · exact hp.argsScr

theorem arg_read {s t : State} (hp : PPreR s) (he : Env s t) {j : Nat} (hj : j < 7) :
    InRegions (t.rd ++ t.wr) (stackArgAddr s j) 8 := by
  rw [he.rd]
  apply (Covers.one hp.args).left
  refine ⟨_, List.mem_singleton_self _, ?_⟩
  rw [Ver.stackArgAddr_eq s j]
  exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])

/-- `pre` and `pre_len` in place of `n` and `n_len`. -/
theorem load_pre {s t : State} (hp : PPreR s) (he : Env s t) :
    WP isa (.block [.mov .rdx (.mem (arg 5)), .mov .rcx (.mem (arg 6))]) t fun u =>
      Keep [.rdx, .rcx] t u ∧ u.mem = t.mem ∧ u.gpr .rdx = stackArg s 5 ∧ u.gpr .rcx = stackArg s 6 := by
  refine WP.keep [.rdx, .rcx] ?_ rfl |> WP.mono <| fun u ⟨h, k⟩ => ⟨k, h⟩
  xrun [@arg_ea s, he.rsp, arg_read hp he (show 5 < 7 by decide), arg_read hp he (show 6 < 7 by decide),
    arg_keep hp he (show 5 < 7 by decide), arg_keep hp he (show 6 < 7 by decide)]

/-- Before the call, with its arguments in registers and on the stack. -/
def J1 (s t : State) : Prop :=
  Env s t ∧ word t.mem (fb s) 0 = stackArg s 1 ∧ word t.mem (fb s) 8 = s.gpr .rcx ∧
    word t.mem (fb s) 16 = stackArg s 3 ∧ word t.mem (fb s) 24 = stackArg s 4 ∧
    t.gpr .rdi = off (fb s) oEM1 ∧ t.gpr .rsi = s.gpr .rcx ∧ t.gpr .rdx = stackArg s 5 ∧
    t.gpr .rcx = stackArg s 6 ∧ t.gpr .r8 = s.gpr .r8 ∧ t.gpr .r9 = s.gpr .r9 ∧ stackArg s 2 = s.gpr .rcx

theorem pubArgs_ok {s A : State} (hp : PPreR s) (hsig : stackArg s 2 = s.gpr .rcx)
    (hA : Keep [.rax] (allocState frameBytes s) A) (hAm : A.mem = s.mem) :
    WP isa (.block Impl.RsaPkcs1Sig.X86_64.RecoverPrecomputed.pubArgs) A fun t => J1 s t ∧
      (∀ r ∈ calleeSaved, r ≠ .rsp → t.gpr r = s.gpr r) := by
  unfold Impl.RsaPkcs1Sig.X86_64.RecoverPrecomputed.pubArgs
  rw [WP.block_append_iff]
  refine WP.mono (Rec.pubArgs_ok hp.toPreR hA hAm)
    fun t ⟨he, hw0, hw1, hw2, hw3, hdi, hsi, _, _, h8, h9, hcs⟩ => ?_
  refine WP.mono (load_pre hp he) fun u ⟨hk, hm, hdx', hcx'⟩ => ?_
  refine ⟨⟨he.regs (hk.gpr (by decide)) hm hk.2.1 hk.2.2, by rw [hm]; exact hw0,
    by rw [hm]; exact hw1, by rw [hm]; exact hw2, by rw [hm]; exact hw3,
    (hk.gpr (by decide)).trans hdi, (hk.gpr (by decide)).trans hsi, hdx', hcx',
    (hk.gpr (by decide)).trans h8, (hk.gpr (by decide)).trans h9, hsig⟩, fun r hr hr' => ?_⟩
  rw [hk.gpr (by simp [calleeSaved] at hr ⊢; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)]
  exact hcs r hr hr'

/-! ## The call -/

/-- What `vg_rsa_public_precomputed_checked` reads: `pre`, `e`, `sig` and its
stack arguments. -/
def callRd (s : State) : List Region :=
  [preR s, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩, ⟨stackArg s 1, (s.gpr .rcx).toNat⟩, ⟨fb s, 32⟩]

theorem call_pre {s t : State} (hp : PPreR s) (h : J1 s t) :
    pdContract.pre (t.callEntry.withRegions (callRd s) (pubWr s)) := by
  obtain ⟨he, hw0, hw1, hw2, hw3, hdi, hsi, hdx, hcx, h8, h9, hsig⟩ := h
  have hsp := he.rsp
  obtain hE : ∀ i, i < 4 → stackArg (t.callEntry.withRegions (callRd s) (pubWr s)) i = word t.mem (fb s) (8 * i) :=
    fun i hi => stackArg_entry hsp _ _ (by omega_using [hi])
  simp only [pdContract, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_rsp, State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide), hdi, hsi, hdx, hcx, h8, h9, hsp,
    stackArgAddr_entry hsp, hE 0 (by decide), hE 1 (by decide), hE 2 (by decide), hE 3 (by decide),
    Nat.reduceMul, hw0, hw1, hw2, hw3, fb_sub8]
  have ⟨hK1, hK2⟩ := kb_toNat hp.toPreR
  have e1 : verStack = 2144 := rfl
  have e2 : oEM1 = 80 := rfl
  have e3 : frameBytes = 2136 := rfl
  have hk1 := hp.k1
  have hk2 := hp.k2
  obtain sM : Region.Sub (em1R s) (stkR s) := frame_sub s (by unfold oEM1 frameBytes; omega_using [hk2])
  obtain sA : Region.Sub ⟨fb s, 32⟩ (stkR s) := by
    have := frame_sub s (d := 0) (n := 32) (by decide); simpa only [off, BitVec.add_zero] using this
  obtain sR : Region.Sub ⟨kb s, 8⟩ (stkR s) := Region.sub_prefix (by decide)
  obtain hfb : fb s = kb s + BitVec.ofNat 64 8 := fb_eq s
  obtain dMA : (em1R s).Disjoint ⟨fb s, 32⟩ := Offset.disjoint_base _ (by decide) (by omega_using [e2, hk2])
  obtain dRM : (⟨kb s, 8⟩ : Region).Disjoint (em1R s) := by
    simp only [em1R]; rw [hfb, off, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact Offset.base_disjoint _ (by decide) (by omega_using [e2, hk2])
  obtain dRA : (⟨kb s, 8⟩ : Region).Disjoint ⟨fb s, 32⟩ := by
    rw [hfb]; exact Offset.base_disjoint _ (by decide) (by omega_using [])
  obtain wM : (off (fb s) oEM1).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 := by
    rw [toNat_off (by rw [hfb, ← off, toNat_off (by omega_using [hK1])]; unfold oEM1; omega_using [hK1, e1]), hfb, ← off,
      toNat_off (by omega_using [hK1])]; unfold oEM1; omega_using [hK1, e1, hk2]
  obtain dKg : (stkR s).Disjoint ⟨stackArg s 1, (s.gpr .rcx).toNat⟩ := by rw [← hsig]; exact hp.dKg
  obtain dgs : (⟨stackArg s 1, (s.gpr .rcx).toNat⟩ : Region).Disjoint (scrR s) := by rw [← hsig]; exact hp.dgs
  obtain wG : (stackArg s 1).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 := by rw [← hsig]; exact hp.wG
  refine ⟨by omega_using [hK1], rfl, rfl, hp.preStack.symm.sub_left sM, hp.dKe.sub_left sM, dKg.sub_left sM,
    hp.dKs.sub_left sM, dMA, hp.preScr, hp.des, dgs, (hp.dKs.sub_left sA).symm, dRM,
    hp.preStack.symm.sub_left sR, hp.dKe.sub_left sR, dKg.sub_left sR, hp.dKs.sub_left sR, dRA, wM,
    hp.preWrap, hp.wE, wG, hp.wS, ⟨hk1, hk2⟩, hp.preLen, trivial, hp.L1, hp.L2,
    hp.hsl⟩

theorem call_covers {s t : State} (hp : PPreR s) (hsig : stackArg s 2 = s.gpr .rcx) (he : Env s t) :
    Covers (callRd s ++ pubWr s) (t.rd ++ t.wr) ∧ Covers (pubWr s) t.wr := by
  obtain ⟨-, cw⟩ := pub_covers hp.toPreR hsig he
  have hk2 := hp.k2
  obtain hfr : (⟨fb s, frameBytes⟩ : Region) ∈ t.wr := by rw [he.wr]; exact List.mem_cons_self ..
  obtain z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  refine ⟨Covers.append_left ?_ cw.right, cw⟩
  obtain cr : Covers [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩,
      ⟨stackArg s 1, (stackArg s 2).toNat⟩, ⟨stackArgAddr s 0, 40⟩] (t.rd ++ t.wr) := by
    rw [he.rd]; exact hp.hrd.left
  apply Covers.of_forall
  intro r hr
  simp only [callRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [he.rd]; exact (Covers.one hp.pre).left
  · exact (Covers.of_mem (by intro r hr; rw [List.mem_singleton.mp hr]; simp)).trans cr
  · rw [← hsig]
    exact (Covers.of_mem (by intro r hr; rw [List.mem_singleton.mp hr]; simp)).trans cr
  · exact Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨_, List.mem_append_right _ hfr, 0, z _, by dsimp only; unfold frameBytes; omega_using []⟩

/-- `pre`, unchanged where the function writes. -/
theorem pre_words {s : State} {m : Mem} (hp : PPreR s) (hf : Frame [stkR s, outR s, scrR s] s.mem m) :
    Spec.Rsa.wordsAt m (stackArg s 5) (stackArg s 6).toNat =
      Spec.Rsa.wordsAt s.mem (stackArg s 5) (stackArg s 6).toNat := by
  unfold Spec.Rsa.wordsAt
  apply List.map_congr_left
  intro i hi
  apply hf.readW (r := preR s) ?_ ?_ (by decide)
  · exact Offset.contains_base _ (by have := List.mem_range.mp hi; omega_using [this])
      (by have := hp.preWrap; have := List.mem_range.mp hi; omega_arith)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.preStack
    · exact hp.preOut
    · exact hp.preScr

/-- Whether `pre` holds the values for `n`. -/
def Consistent (s : State) : Prop :=
  Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) =
    some (Spec.Rsa.wordsAt s.mem (stackArg s 5) (stackArg s 6).toNat)

theorem call_ok (v : PublicImpl) {s t : State} (hp : PPreR s) (h : J1 s t) :
    WP isa (.call v.name v.code) t fun t' => Env s t' ∧
      (Consistent s → Spec.Rsa.written t'.mem (off (fb s) oEM1) (s.gpr .rcx).toNat ((t'.gpr .rax).setWidth 32)
        (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
          (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 1) (s.gpr .rcx).toNat))) ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧ t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 := by
  obtain hpre := call_pre hp h
  obtain ⟨he, hw0, hw1, hw2, hw3, hdi, hsi, hdx, hcx, h8, h9, hsig⟩ := h
  obtain ⟨hc, hw⟩ := call_covers hp hsig he
  refine WP.call_mx (s := t) (k := ⟨pdContract.pre, pdChkContract.post, pdContract.pub⟩) (rd := callRd s)
    (wr := pubWr s) v.ok v.nosp (by rw [v.depth]; decide) hpre hc hw ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost⟩ hmx
  rw [v.depth, he.rsp] at hf
  obtain hE : stackArg (t.callEntry.withRegions (callRd s) (pubWr s)) 0 = stackArg s 1 :=
    (stackArg_entry he.rsp _ _ (by omega_using [])).trans hw0
  obtain hfE : Frame [stkR s, outR s, scrR s] s.mem t.callEntry.mem :=
    frame_call he.mem (callEntry_frame he.rsp) fun r hr => by
      rw [List.mem_singleton.mp hr]; exact .inl (below_sub s)
  have hk2 := hp.k2
  obtain b : ∀ {p : Addr} {len : Nat}, (stkR s).Disjoint ⟨p, len⟩ → (outR s).Disjoint ⟨p, len⟩ →
      (scrR s).Disjoint ⟨p, len⟩ → len ≤ 2 ^ 64 →
      Spec.Rsa.bytesAt t.callEntry.mem p len = Spec.Rsa.bytesAt s.mem p len := fun hk ho hs hl =>
    bytes_of_frame hfE hk ho hs hl
  simp only [pdChkContract, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide),
    hdi, hsi, hdx, hcx, h8, h9, hE, hm₂, hg₂ .rax (by decide)] at hpost
  rw [pre_words hp hfE, b hp.dKe hp.dOe hp.des.symm (by have := hp.wE; omega_using []),
    b (by rw [← hsig]; exact hp.dKg) (by rw [← hsig]; exact hp.dOg) (by rw [← hsig]; exact hp.dgs.symm)
      (by omega_using [])] at hpost
  refine ⟨⟨(hcs .rsp (by decide)).trans he.rsp, hrd.trans he.rd, hwr.trans he.wr,
    frame_call he.mem hf fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun hq => hpost _ (bytesAt_length ..) hq,
    hcs, hmx⟩
  · simp only [pubWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl (frame_sub s (by unfold oEM1 frameBytes; omega_using [hk2]))
    · exact .inr (.inr (sub_refl _))
    · exact .inl (below_sub s)
  · rw [slot_keep hf (slot_apart hp.toPreR (by decide) (by decide))]; exact he.sOut
  · rw [slot_keep hf (slot_apart hp.toPreR (by decide) (by decide))]; exact he.sOl
  · rw [slot_keep hf (slot_apart hp.toPreR (by decide) (by decide))]; exact he.sN
  · rw [slot_keep hf (slot_apart hp.toPreR (by decide) (by decide))]; exact he.sK
  · rw [slot_keep hf (slot_apart hp.toPreR (by decide) (by decide))]; exact he.sE
  · rw [slot_keep hf (slot_apart hp.toPreR (by decide) (by decide))]; exact he.sEl

end VG.Proof.RsaPkcs1Sig.X86_64.RecPc

end

end


/-!
# `vg_rsa_pkcs1_recover_precomputed` on x86-64: correctness

The length check, the frame's push, the call with `pre` (`pubArgs_ok`,
`call_ok`), what follows it whatever it left (`afterPub_ok`) and the pop:
memory safety and the registers the ABI keeps whatever `pre` holds, and, if
`pre` holds the values for `n`, `recContract`'s postcondition, since `relOut`
of what the call then leaves is `recOut` (`code_correct`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.X86_64.RecPc

open VG VG.X86_64 VG.Impl.RsaPkcs1Sig.X86_64 VG.Impl.RsaPkcs1Sig.X86_64.Recover
open VG.Impl.RsaPkcs1Sig.X86_64.Verify (frameBytes oEM1 oEM2 sp arg arg0 lea test0 cmpArgs)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Sig.X86_64 Rec
open VG.Proof.RsaPkcs1Sig.X86_64.Ver (fb kb stkR scrR allocState_gpr freed wp_alloc)
open VG.Proof.Rsa.X86_64 (PublicImpl)
open VG.WriteBytes

/-- `recContract`'s postcondition, if `pre` holds the values for `n`. -/
def post (s u : State) : Prop := Consistent s → recContract.post s u

/-- Recovery's result from the public operation's result `o`. -/
def recOf (k : Nat) (h : Spec.RsaPkcs1Sig.Hash) : Option (List Byte) → Option (List Byte)
  | some em => if Spec.RsaPkcs1Sig.encode h (em.drop (k - h.len)) k = some em then some (em.drop (k - h.len))
      else none
  | none => none

theorem relOut_written {m : Mem} {p : Addr} {k : Nat} {h : Spec.RsaPkcs1Sig.Hash} {st : BitVec 64}
    {o : Option (List Byte)} (hw : Spec.Rsa.written m p k (st.setWidth 32) o) :
    relOut k h st (Spec.Rsa.bytesAt m p k) = recOf k h o := by
  cases o with
  | none => simp only [relOut, hw.1, ne_eq, not_true_eq_false, false_and, ↓reduceIte, recOf]
  | some em =>
    obtain ⟨h1, h2⟩ := hw
    rw [relOut, h1, h2, recOf]
    exact if_congr ⟨fun h => h.2, fun h => ⟨by decide, h⟩⟩ rfl rfl

theorem recOut_eq (nB eB sig : List Byte) (h : Spec.RsaPkcs1Sig.Hash) :
    recOut nB eB h sig = recOf nB.length h (Spec.Rsa.publicOpChecked nB eB sig) := by
  unfold recOut; cases Spec.Rsa.publicOpChecked nB eB sig <;> rfl

theorem code_correct (v : PublicImpl) (s : State)
    (h : (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi verStack).pre s) :
    ∃ t s', Exec isa (Impl.RsaPkcs1Sig.X86_64.RecoverPrecomputed.code v.name v.code) s t s' ∧
      abiPreserved s s' ∧ post s s' := by
  obtain hp := pre_of h
  have hk2 := hp.k2
  have ol := hp.ol
  obtain ⟨hh, hid, hol⟩ := hp.hash
  suffices hw : WP isa (Impl.RsaPkcs1Sig.X86_64.RecoverPrecomputed.code v.name v.code) s fun s' =>
      abiPreserved s s' ∧ post s s' by
    obtain ⟨t, s', he, hq⟩ := hw
    exact ⟨t, s', he, hq⟩
  obtain hpost : ∀ (u : State) (o : Option (List Byte)), Spec.Rsa.written u.mem (s.gpr .rdi) (s.gpr .rsi).toNat
      ((u.gpr .rax).setWidth 32) o →
      (o = Spec.RsaPkcs1Sig.recover (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) hh
        (Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat)) → recContract.post s u := by
    intro u o hw ho h' hid'
    rw [hid] at hid'; cases hid'
    rw [← ho]; exact hw
  unfold Impl.RsaPkcs1Sig.X86_64.RecoverPrecomputed.code
  refine WP.seq (WP.mono_mx (by decide) (lenCheck_ok hp.toPreR) fun t₀ ⟨k₀, hm₀, hz₀⟩ hmx₀ => ?_)
  obtain g₀ : ∀ r, r ≠ .rax → t₀.gpr r = s.gpr r := fun r h => k₀.gpr (by simpa using h)
  by_cases hsig : stackArg s 2 = s.gpr .rcx
  · refine WP.ite false (by simp [eval, hz₀, hsig]) (by simp) (fun _ => ?_)
    obtain hsp₀ : t₀.gpr .rsp = s.gpr .rsp := g₀ _ (by decide)
    obtain hA : Keep [.rax] (allocState frameBytes s) (allocState frameBytes t₀) :=
      ⟨fun r hr => by
        simp only [allocState_gpr, fb, hsp₀]
        split
        · rfl
        · exact g₀ r (by simpa using hr), k₀.2.1, by simp only [allocState, hsp₀, k₀.2.2]⟩
    obtain hfb : fb t₀ = fb s := by simp only [fb, hsp₀]
    refine wp_alloc (s := t₀) (by rw [hsp₀]; have := hp.sp1; unfold verStack at this; unfold frameBytes; omega_arith) ?_
    unfold Impl.RsaPkcs1Sig.X86_64.RecoverPrecomputed.body
    refine WP.seq (WP.mono_mx (by decide) (pubArgs_ok hp hsig hA hm₀) fun t₁ ⟨hj, hcs₁⟩ hmx₁ => ?_)
    refine WP.seq (WP.mono (call_ok v hp hj) fun t₂ ⟨he₂, hw, hcs₂, hmx₂⟩ => ?_)
    refine WP.mono_mx (by decide +kernel) (WP.keep [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11]
      (afterPub_ok hp.toPreR he₂ hid) (by decide +kernel)) fun t₃ ⟨⟨he₃, hwu⟩, k₃⟩ hmx₃ => ?_
    refine ⟨he₃.rsp.trans hfb.symm, by rw [he₃.wr]; simp only [allocState, hsp₀, k₀.2.2], fun m uu fm => ?_⟩
    rw [hfb] at fm
    have hs := VG.Proof.RsaPkcs1Sig.X86_64.Ver.frame_sub s (d := 0) (n := frameBytes) (by omega_using [])
    simp only [off, BitVec.add_zero] at hs
    have hwu' := Proof.Rsa.written_frame fm (s.gpr .rsi).isLt (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact (hp.toPreR.dKo.sub_left hs).symm) hwu
    refine ⟨⟨fun r hr => ?_, ret_frame hp.toPreR (he₃.mem.trans (fm.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., hs⟩)), ?_⟩,
      fun hq => hpost { freed frameBytes t₃ with mem := m, unknowns := uu } _ hwu' ?_⟩
    · by_cases hr' : r = .rsp
      · subst hr'
        show t₃.gpr .rsp + BitVec.ofNat 64 frameBytes = s.gpr .rsp
        rw [he₃.rsp, BitVec.sub_add_cancel]
      · show (if r = .rsp then _ else t₃.gpr r) = s.gpr r
        simp only [hr', ↓reduceIte]
        obtain hr'' : r ∉ [Reg.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11] := by
          simp [calleeSaved] at hr ⊢; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | decide | simp_all
        rw [k₃.gpr hr'', hcs₂ r hr, hcs₁ r hr hr']
    · show t₃.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10
      rw [hmx₃, hmx₂, hmx₁]; exact congrArg _ hmx₀
    · rw [relOut_written (hw hq), hsig, recover_eq_recOut _ (by simp only [bytesAt_length])]
      rw [recOut_eq, bytesAt_length]
  · refine WP.ite true (by simp [eval, hz₀, hsig]) (fun _ => ?_) (by simp)
    obtain hwr : outR s ∈ t₀.wr := by rw [k₀.2.2, hp.hwr]; simp [outR]
    refine WP.mono_mx (by decide) (zeroOut_ok (n := (s.gpr .rsi).toNat) (by omega_arith) (by omega_arith)
      (by rw [g₀ _ (by decide), Rec.ofNat_toNat64]) (by rw [g₀ _ (by decide)]; exact out_wr hwr))
      fun u ⟨hK, hm, hax⟩ hmx => ⟨⟨fun r hr => ?_, ?_, by rw [hmx, hmx₀]⟩, fun _ => hpost u none ⟨by rw [hax]; rfl, ?_⟩ ?_⟩
    · rw [hK.gpr (by simp [calleeSaved] at hr ⊢; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp),
        k₀.gpr (by simp [calleeSaved] at hr ⊢; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)]
    · rw [hm, g₀ _ (by decide)]
      refine ((frame_writeBytes t₀.mem _ _).readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _)
        (fun r hr => ?_) (by decide)).trans (by rw [hm₀])
      rw [List.mem_singleton.mp hr, List.length_replicate]; exact hp.dRo
    · rw [hm, g₀ _ (by decide)]
      have := bytesAt_writeBytes t₀.mem (s.gpr .rdi) (List.replicate (s.gpr .rsi).toNat 0) (by simp; omega_arith)
      rwa [List.length_replicate] at this
    · rw [recover_len _ (by simp only [bytesAt_length]; intro h'; exact hsig (BitVec.eq_of_toNat_eq h'))]

end VG.Proof.RsaPkcs1Sig.X86_64.RecPc

end

end


/-!
# `vg_rsa_pkcs1_recover_precomputed` on x86-64: the contract

`contract` is the shared contract's precondition, `post`, and
`recContract`'s public data with `pre` and its words; it implies the shared
contract (`implies`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.X86_64.RecPc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Sig.X86_64

def contract : Contract isa where
  pre := (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi verStack).pre
  post := post
  pub a s := recContract.pub a s ∧ stackArg a 5 = stackArg s 5 ∧ stackArg a 6 = stackArg s 6 ∧
    Spec.Rsa.wordsAt a.mem (stackArg a 5) (stackArg a 6).toNat =
      Spec.Rsa.wordsAt s.mem (stackArg s 5) (stackArg s 6).toNat

/-- `recSatState`, with 16 words of `pre` at `0x6000`. -/
def satState : State := { recSatState with
  mem := fun a => if a = 0x10031 then 0x60 else if a = 0x10038 then 16 else recSatState.mem a
  rd := [⟨0x1000, 64⟩, ⟨0x2000, 1⟩, ⟨0x4000, 1⟩, ⟨0x6000, 128⟩, ⟨0x10008, 56⟩] }

theorem implies : contract.Implies (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi verStack) where
  pre := fun _ h => h
  post := by sig_implies_post [Spec.RsaPkcs1Sig.recoverPrecomputedContract,
    Spec.RsaPkcs1Sig.recoverPrecomputedSig, abi, argRegs, contract, post, Consistent, recContract, verStack,
    stackArgs_seven, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.RsaPkcs1Sig.recoverPrecomputedContract, Spec.RsaPkcs1Sig.recoverPrecomputedSig,
      abi, argRegs, contract, verStack, stackArgs_seven, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5, a6⟩ := h
    obtain ⟨hb, hq⟩ := List.append_inj hl (by simp [Spec.Rsa.bytesAt, hcx, h9, a2])
    obtain hq' := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hq
    obtain ⟨hn, he, hs⟩ := leak_eq3 (by simp [Spec.Rsa.bytesAt, hcx]) (by simp [Spec.Rsa.bytesAt, h9]) hb
    refine ⟨⟨?_, a0, by rw [a1, a2, a3, a4], hn, he, hs⟩, a5, a6, hq'⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := by sig_implies_sat [Spec.RsaPkcs1Sig.recoverPrecomputedContract,
    Spec.RsaPkcs1Sig.recoverPrecomputedSig, abi, argRegs, contract, verStack, stackArgs_seven, List.append_eq]
    [satState, recSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using satState

end VG.Proof.RsaPkcs1Sig.X86_64.RecPc

end

end

/-!
# `vg_rsa_pkcs1_recover_precomputed` on x86-64: constant time

Before the call, as for `vg_rsa_pkcs1_recover` (`RecoverCT`), for entry
states related to the anchor by `contract` (`PR`), and the call, constant
time for its contract, which makes `pre`'s words public too. After it,
whatever the call left: the blocks and loops are checked by the taint
analysis from the registers correctness fixes, and the one branch, on
whether `encode` succeeds, depends on `hash`, `n_len` and `out_len` alone
(`encodeId_isSome`), not on `EM₁`.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.X86_64.RecPcCT

open VG VG.X86_64 VG.Impl.RsaPkcs1Sig.X86_64 VG.Impl.RsaPkcs1Sig.X86_64.Recover
open VG.Impl.RsaPkcs1Sig.X86_64.RecoverPrecomputed (maskM maskArgs fin)
open VG.Impl.RsaPkcs1Sig.X86_64.Verify (frameBytes oEM1 oEM2 sp arg arg0 lea test0 ret0 cmpArgs)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Sig.X86_64
open VG.Proof.RsaPkcs1Sig.X86_64.Ver (fb kb stkR scrR frame_sub test0_ok relCT_alloc entry_regs regs_eq
  stackArg_entry callEntry_frame below_sub)
open VG.Proof.Rsa.X86_64 (PublicImpl pdChkContract)
open RecPc

/-! ## Entry states and the anchor -/

/-- An entry state meeting the precondition with the anchor's public data. -/
def PR (a s : State) : Prop := contract.pre s ∧ contract.pub a s

theorem pr_sib : ∀ a s, PR a s → Rec.Sib a s := fun _ _ h => ⟨(pre_of h.1).toPreR, h.2.1⟩

theorem pub_refl (s : State) : contract.pub s s := ⟨Rec.pub_refl s, rfl, rfl, rfl⟩

def At (J : State → State → Prop) (a t : State) : Prop := ∃ s, PR a s ∧ J s t

theorem pin {J : State → State → Prop} {r : Reg} (f : State → BitVec 64) (hf : ∀ s t, J s t → t.gpr r = f s)
    (hs : ∀ a s, Rec.Sib a s → f s = f a) {a t₁ t₂ : State} (h₁ : At J a t₁) (h₂ : At J a t₂) :
    t₁.gpr r = t₂.gpr r := by
  obtain ⟨s₁, S₁, j₁⟩ := h₁
  obtain ⟨s₂, S₂, j₂⟩ := h₂
  rw [hf _ _ j₁, hf _ _ j₂, hs _ _ (pr_sib _ _ S₁), hs _ _ (pr_sib _ _ S₂)]

theorem pinEval {J : State → State → Prop} {c : Cond} (f : State → Option Bool)
    (hf : ∀ s t, J s t → isa.eval c t = f s) (hs : ∀ a s, Rec.Sib a s → f s = f a) :
    ∀ a t₁ t₂, At J a t₁ → At J a t₂ → isa.eval c t₁ = isa.eval c t₂ := by
  rintro a t₁ t₂ ⟨s₁, S₁, j₁⟩ ⟨s₂, S₂, j₂⟩
  rw [hf _ _ j₁, hf _ _ j₂, hs _ _ (pr_sib _ _ S₁), hs _ _ (pr_sib _ _ S₂)]

theorem pins_rsp {J : State → State → Prop} (hJ : ∀ s t, J s t → t.gpr .rsp = fb s) : Pins (At J) [.rsp] :=
  fun _ _ _ h₁ h₂ r hr => by
    rw [List.mem_singleton.mp hr]
    exact pin fb hJ (fun _ _ h => h.fb) h₁ h₂

theorem two_and {J : State → State → Prop} {P : State → Prop} {c : Prog isa} {Q : State → State → Prop}
    (h : RelCT isa (Two (At fun s t => J s t ∧ P t)) c Q) :
    RelCT isa (Two fun a t => At J a t ∧ P t) c Q :=
  h.mono (fun _ _ ⟨a, ⟨⟨s₁, S₁, j₁⟩, p₁⟩, ⟨⟨s₂, S₂, j₂⟩, p₂⟩⟩ => ⟨a, ⟨s₁, S₁, j₁, p₁⟩, ⟨s₂, S₂, j₂, p₂⟩⟩)
    fun _ _ h => h

/-! ## Before the call -/

theorem lenCheck_two : RelCT isa (Two (At Rec.J0)) (.block lenCheck) (Two (At Rec.JL)) :=
  two_piece [.rsp] (fun _ _ _ h₁ h₂ r hr => by
      rw [List.mem_singleton.mp hr]
      exact pin (fun s => s.gpr .rsp) (fun s t h => by rw [show t = s from h]) (fun _ _ S => S.gpr (by decide))
        h₁ h₂)
    (by taint_decide)
    fun _ t ⟨s, S, ht⟩ => by
      rw [show t = s from ht]
      exact WP.mono (Rec.lenCheck_ok (pr_sib _ _ S).1) fun _ h => ⟨s, S, h⟩

theorem zeroOut0_ct : RelCT isa (Two fun a t => At Rec.JL a t ∧ isa.eval .ne t = some true) zeroOut fun _ _ => True :=
  two_and (Rec.zeroOut_taint fun _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact pin (fun s => s.gpr .rdi) (fun _ _ h => h.1.1.gpr (by decide)) (fun _ _ S => S.gpr (by decide)) h₁ h₂
    · exact pin (fun s => s.gpr .rsi) (fun _ _ h => h.1.1.gpr (by decide)) (fun _ _ S => S.gpr (by decide)) h₁ h₂)

theorem pubArgs_two : RelCT isa (Two (At Rec.JA)) (.block Impl.RsaPkcs1Sig.X86_64.RecoverPrecomputed.pubArgs)
    (Two (At RecPc.J1)) :=
  two_piece [.rsp] (pins_rsp fun s t ⟨t₀, ⟨k₀, _, _⟩, _, ht⟩ => by
      subst ht; show t₀.gpr .rsp - _ = _; rw [k₀.gpr (by decide)]) (by taint_decide)
    fun _ t ⟨s, S, t₀, ⟨k₀, hm₀, _⟩, hg, ht⟩ => by
      subst ht
      have g₀ : ∀ r, r ≠ .rax → t₀.gpr r = s.gpr r := fun r h => k₀.gpr (by simpa using h)
      have hsp₀ : t₀.gpr .rsp = s.gpr .rsp := g₀ _ (by decide)
      have hA : Keep [.rax] (allocState frameBytes s) (allocState frameBytes t₀) :=
        ⟨fun r hr => by
          simp only [Ver.allocState_gpr, fb, hsp₀]
          split
          · rfl
          · exact g₀ r (by simpa using hr), k₀.2.1, by simp only [allocState, hsp₀, k₀.2.2]⟩
      exact WP.mono (RecPc.pubArgs_ok (pre_of S.1) hg hA hm₀) fun _ h => ⟨s, S, h.1⟩

/-! ## The call -/

theorem pub_view {a s t : State} (S : PR a s) (h : RecPc.J1 s t) :
    [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp].map (t.callEntry.withRegions (callRd s) (Rec.pubWr s)).gpr =
      [off (fb a) oEM1, a.gpr .rcx, stackArg a 5, stackArg a 6, a.gpr .r8, a.gpr .r9, fb a - 8] ∧
    stackArg (t.callEntry.withRegions (callRd s) (Rec.pubWr s)) 0 = stackArg a 1 ∧
    stackArg (t.callEntry.withRegions (callRd s) (Rec.pubWr s)) 1 = a.gpr .rcx ∧
    stackArg (t.callEntry.withRegions (callRd s) (Rec.pubWr s)) 2 = stackArg a 3 ∧
    stackArg (t.callEntry.withRegions (callRd s) (Rec.pubWr s)) 3 = stackArg a 4 ∧
    Spec.Rsa.wordsAt (t.callEntry.withRegions (callRd s) (Rec.pubWr s)).mem
      ((t.callEntry.withRegions (callRd s) (Rec.pubWr s)).gpr .rdx)
      ((t.callEntry.withRegions (callRd s) (Rec.pubWr s)).gpr .rcx).toNat =
      Spec.Rsa.wordsAt a.mem (stackArg a 5) (stackArg a 6).toNat ∧
    Spec.Rsa.bytesAt (t.callEntry.withRegions (callRd s) (Rec.pubWr s)).mem
      ((t.callEntry.withRegions (callRd s) (Rec.pubWr s)).gpr .r8)
      ((t.callEntry.withRegions (callRd s) (Rec.pubWr s)).gpr .r9).toNat =
      Spec.Rsa.bytesAt a.mem (a.gpr .r8) (a.gpr .r9).toNat := by
  obtain ⟨he, hw0, hw1, hw2, hw3, hdi, hsi, hdx, hcx, h8, h9, -⟩ := h
  have hp := pre_of S.1
  have S' := pr_sib _ _ S
  have hfE : Frame [stkR s, Rec.outR s, scrR s] s.mem t.callEntry.mem :=
    Rec.frame_call he.mem (callEntry_frame he.rsp) fun r hr => by
      rw [List.mem_singleton.mp hr]; exact .inl (below_sub s)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [entry_regs, hdi, hsi, hdx, hcx, h8, h9, he.rsp, S'.fb, S'.gpr (r := .rcx) (by decide),
      S.2.2.1, S.2.2.2.1, S'.gpr (r := .r8) (by decide), S'.gpr (r := .r9) (by decide)]
  · rw [stackArg_entry he.rsp _ _ (by decide), ← S'.arg (by decide) (by decide)]; exact hw0
  · rw [stackArg_entry he.rsp _ _ (by decide), ← S'.gpr (r := .rcx) (by decide)]; exact hw1
  · rw [stackArg_entry he.rsp _ _ (by decide), ← S'.arg (by decide) (by decide)]; exact hw2
  · rw [stackArg_entry he.rsp _ _ (by decide), ← S'.arg (by decide) (by decide)]; exact hw3
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), hdx, hcx]
    rw [State.withRegions_mem, pre_words hp hfE, S.2.2.2.2]
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide), h8, h9]
    rw [Rec.entryBytes he _ _ hp.dKe hp.dOe hp.des.symm (by have := hp.wE; omega_using []), S'.e]

theorem call_ct (v : PublicImpl) : RelCT isa (Two (At RecPc.J1)) (.call v.name v.code) fun _ _ => True := by
  refine RelCT.callEx (k := pdChkContract) v.ok v.ct fun t₁ t₂ ⟨a, ⟨s₁, S₁, j₁⟩, ⟨s₂, S₂, j₂⟩⟩ => ?_
  obtain ⟨r₁, a0₁, a1₁, a2₁, a3₁, n₁, e₁⟩ := pub_view S₁ j₁
  obtain ⟨r₂, a0₂, a1₂, a2₂, a3₂, n₂, e₂⟩ := pub_view S₂ j₂
  obtain ⟨c₁, w₁⟩ := call_covers (pre_of S₁.1) j₁.2.2.2.2.2.2.2.2.2.2.2 j₁.1
  obtain ⟨c₂, w₂⟩ := call_covers (pre_of S₂.1) j₂.2.2.2.2.2.2.2.2.2.2.2 j₂.1
  have p₁ := call_pre (pre_of S₁.1) j₁
  have p₂ := call_pre (pre_of S₂.1) j₂
  have hpub : pdChkContract.pub (t₁.callEntry.withRegions (callRd s₁) (Rec.pubWr s₁))
      (t₂.callEntry.withRegions (callRd s₂) (Rec.pubWr s₂)) :=
    ⟨regs_eq (r₁.trans r₂.symm), a0₁.trans a0₂.symm, a1₁.trans a1₂.symm, a2₁.trans a2₂.symm,
      a3₁.trans a3₂.symm, n₁.trans n₂.symm, e₁.trans e₂.symm⟩
  exact ⟨callRd s₁, Rec.pubWr s₁, callRd s₂, Rec.pubWr s₂, p₁, p₂, hpub, c₁, w₁, c₂, w₂,
    by rw [j₁.1.rsp, j₂.1.rsp, (pr_sib _ _ S₁).fb, (pr_sib _ _ S₂).fb]⟩

/-- In the frame. -/
def JE (s t : State) : Prop := Rec.Env s t

theorem call_two (v : PublicImpl) : RelCT isa (Two (At RecPc.J1)) (.call v.name v.code) (Two (Rec.At JE)) :=
  two_post (call_ct v) fun _ _ ⟨s, S, h⟩ =>
    WP.mono (call_ok v (pre_of S.1) h) fun _ h => ⟨s, pr_sib _ _ S, h.1⟩

/-! ## After the call -/

/-- `encode`'s status depends only on the length of the hash value. -/
theorem encodeId_isSome {x : BitVec 32} {H H' : List Byte} {k : Nat} (hl : H.length = H'.length) :
    (encodeId x H k).isSome = (encodeId x H' k).isSome := by
  unfold encodeId
  split
  · simp only [Spec.RsaPkcs1Sig.encode, Spec.RsaPkcs1Sig.digestInfo, List.length_append, hl]
    split <;> rfl
  · rfl

/-- Whether `encode` succeeds, from the entry state. -/
def stat (s : State) : Bool :=
  (encodeId ((stackArg s 0).setWidth 32) (List.replicate (s.gpr .rsi).toNat 0) (s.gpr .rcx).toNat).isSome

theorem stat_sib {a s : State} (S : Rec.Sib a s) : stat s = stat a := by
  simp only [stat, S.h, S.gpr (r := .rsi) (by decide), S.gpr (r := .rcx) (by decide)]

def JH (s t : State) : Prop :=
  Rec.Env s t ∧ t.gpr .r8 = off (fb s) oEM2 ∧ t.gpr .rcx = s.gpr .rcx ∧
    t.gpr .rdx = ((stackArg s 0).setWidth 32).setWidth 64 ∧ t.gpr .r9 = s.gpr .rsi ∧ t.gpr .rsi = Rec.valA s

theorem head_ok {s t : State} (hp : Rec.PreR s) (he : Rec.Env s t) :
    WP isa (.block (([.store (sp 0) .rax] : List Instr) ++ encArgs)) t (JH s) := by
  rw [WP.block_append_iff]
  refine WP.mono (save_ok hp he) fun t₁ ⟨k₁, hm₁⟩ => ?_
  have he₁ : Rec.Env s t₁ := Env.low he (d := 0) (by decide) (k₁.gpr (by decide)) k₁.2.1 k₁.2.2 hm₁
  refine WP.mono (Rec.encArgs_ok hp he₁) fun u ⟨hK, hm, h8, hcx, hdx, h9, hsi⟩ =>
    ⟨he₁.regs (hK.gpr (by decide)) hm hK.2.1 hK.2.2, h8, hcx, hdx, h9, hsi⟩

theorem head_two : RelCT isa (Two (Rec.At JE)) (.block (([.store (sp 0) .rax] : List Instr) ++ encArgs)) (Two (Rec.At JH)) :=
  two_piece [.rsp] (Rec.pins_rsp fun _ _ h => h.rsp) (by taint_decide)
    fun _ _ ⟨s, S, he⟩ => WP.mono (head_ok S.1 he) fun _ h => ⟨s, S, h⟩

def JS (s t : State) : Prop :=
  ∃ t₄, JH s t₄ ∧ Keep clob t₄ t ∧ ∃ H : List Byte, H.length = (s.gpr .rsi).toNat ∧
    EOut t₄ t (encodeId ((stackArg s 0).setWidth 32) H (s.gpr .rcx).toNat)

theorem encode_two : RelCT isa (Two (Rec.At JH)) encode (Two (Rec.At JS)) :=
  two_piece [.rsp, .r8, .rcx, .rdx, .rsi, .r9] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact Rec.pin fb (fun _ _ h => h.1.rsp) (fun _ _ S => S.fb) h₁ h₂
      · exact Rec.pin (fun s => off (fb s) oEM2) (fun _ _ h => h.2.1) (fun _ _ S => by rw [S.fb]) h₁ h₂
      · exact Rec.pin (fun s => s.gpr .rcx) (fun _ _ h => h.2.2.1) (fun _ _ S => S.gpr (by decide)) h₁ h₂
      · exact Rec.pin (fun s => ((stackArg s 0).setWidth 32).setWidth 64) (fun _ _ h => h.2.2.2.1)
          (fun _ _ S => by rw [S.h]) h₁ h₂
      · exact Rec.pin Rec.valA (fun _ _ h => h.2.2.2.2.2) (fun _ _ S => S.valA) h₁ h₂
      · exact Rec.pin (fun s => s.gpr .rsi) (fun _ _ h => h.2.2.2.2.1) (fun _ _ S => S.gpr (by decide)) h₁ h₂)
    (by taint_decide)
    fun _ t ⟨s, S, j⟩ => by
      obtain ⟨he, h8, hcx, hdx, h9, hsi⟩ := j
      refine WP.mono (encode_ok (Rec.encPre S.1 he h8 hcx hdx h9 hsi)) fun u ⟨hK, hout⟩ =>
        ⟨s, S, t, ⟨he, h8, hcx, hdx, h9, hsi⟩, hK, _, by rw [bytesAt_length, h9], hout⟩

def JT (s t : State) : Prop := ∃ t₅, JS s t₅ ∧ SameF t₅ t ∧ t.zf = some !(stat s)

theorem test0_two : RelCT isa (Two (Rec.At JS)) (.block test0) (Two (Rec.At JT)) :=
  two_piece [] (fun _ _ _ _ _ _ h => absurd h List.not_mem_nil) (by taint_decide)
    fun _ t ⟨s, S, j⟩ => WP.mono (test0_ok t) fun u ⟨hs, hz⟩ => ⟨s, S, t, j, hs, by
      obtain ⟨t₄, -, -, H, hl, hout⟩ := j
      have hst : stat s = (encodeId ((stackArg s 0).setWidth 32) H (s.gpr .rcx).toNat).isSome :=
        encodeId_isSome (by rw [hl, List.length_replicate])
      rw [hz, hst]
      cases h : encodeId ((stackArg s 0).setWidth 32) H (s.gpr .rcx).toNat with
      | none => rw [h] at hout; rw [hout.1]; rfl
      | some em' => rw [h] at hout; rw [hout.1]; rfl⟩

theorem JT_none {s t : State} (h : JT s t) (he : isa.eval .e t = some true) : Rec.Env s t := by
  obtain ⟨t₅, ⟨t₄, j₄, hK, H, hl, hout⟩, hs, hz⟩ := h
  have hn : encodeId ((stackArg s 0).setWidth 32) H (s.gpr .rcx).toNat = none := by
    have : stat s = false := by
      simp only [eval, hz, Option.some.injEq, Bool.not_eq_true'] at he; exact he
    rw [stat, ← encodeId_isSome (by rw [hl, List.length_replicate])] at this
    simpa using this
  rw [hn] at hout
  exact (j₄.1.regs (by rw [hK.gpr (by decide)]) hout.2 hK.2.1 hK.2.2).regs (by rw [hs.1]) hs.2.1 hs.2.2.1
    hs.2.2.2

def JC (s t : State) : Prop :=
  Rec.Env s t ∧ t.gpr .rdi = off (fb s) oEM1 ∧ t.gpr .rsi = off (fb s) oEM2 ∧ t.gpr .rcx = s.gpr .rcx

theorem cmpArgs_two : RelCT isa (Two fun a t => Rec.At JT a t ∧ isa.eval .e t = some false) (.block cmpArgs)
    (Two (Rec.At JC)) :=
  Rec.two_and (two_piece [.rsp] (fun _ _ _ h₁ h₂ r hr => by
      rw [List.mem_singleton.mp hr]
      exact Rec.pin fb (fun s t h => by
        obtain ⟨⟨t₅, ⟨t₄, j₄, hK, _⟩, hs, _⟩, _⟩ := h
        rw [hs.1, hK.gpr (by decide)]; exact j₄.1.rsp) (fun _ _ S => S.fb) h₁ h₂)
    (by taint_decide)
    fun _ t ⟨s, S, ⟨t₅, ⟨t₄, j₄, hK, H, hl, hout⟩, hs, hz⟩, he⟩ => by
      have hp := S.1
      have hsome : (encodeId ((stackArg s 0).setWidth 32) H (s.gpr .rcx).toNat).isSome = true := by
        have : stat s = true := by
          simp only [eval, hz, Option.some.injEq, Bool.not_eq_false'] at he; exact he
        rwa [stat, encodeId_isSome (by rw [hl, List.length_replicate])] at this
      obtain ⟨em', hem'⟩ := Option.isSome_iff_exists.mp hsome
      rw [hem'] at hout
      obtain ⟨he₄, h8₄, hcx₄, -, -, -⟩ := j₄
      obtain ⟨he₅, -, -, -⟩ := Rec.encDone hp he₄ hK h8₄ (Rec.encodeId_length hem') hout
      have he₆ : Rec.Env s t := he₅.regs (by rw [hs.1]) hs.2.1 hs.2.2.1 hs.2.2.2
      refine WP.mono (Rec.cmpArgs_ok he₆) fun u ⟨hK', hm, hdi, hsi⟩ =>
        ⟨s, S, he₆.regs (hK'.gpr (by decide)) hm hK'.2.1 hK'.2.2, hdi, hsi, ?_⟩
      rw [hK'.gpr (by decide), hs.1, hK.gpr (by decide), hcx₄])

def JQ (s t : State) : Prop := Rec.Env s t ∧ t.gpr .rcx = s.gpr .rcx

theorem compare_two : RelCT isa (Two (Rec.At JC)) compare (Two (Rec.At JQ)) :=
  two_piece [.rdi, .rsi, .rcx] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact Rec.pin (fun s => off (fb s) oEM1) (fun _ _ h => h.2.1) (fun _ _ S => by rw [S.fb]) h₁ h₂
      · exact Rec.pin (fun s => off (fb s) oEM2) (fun _ _ h => h.2.2.1) (fun _ _ S => by rw [S.fb]) h₁ h₂
      · exact Rec.pin (fun s => s.gpr .rcx) (fun _ _ h => h.2.2.2) (fun _ _ S => S.gpr (by decide)) h₁ h₂)
    (by taint_decide)
    fun _ t ⟨s, S, he, hdi, hsi, hcx⟩ => by
      have hp := S.1
      have hk1 := hp.k1
      have hk2 := hp.k2
      have hr : InRegions (t.rd ++ t.wr) (t.gpr .rdi) (s.gpr .rcx).toNat ∧
          InRegions (t.rd ++ t.wr) (t.gpr .rsi) (s.gpr .rcx).toNat := by
        rw [hdi, hsi, he.wr]
        obtain ⟨r₁, h₁, c₁⟩ := Rec.frame_span' hp (d := oEM1) (n := (s.gpr .rcx).toNat)
          (by unfold oEM1 frameBytes; omega_using [hk2])
        obtain ⟨r₂, h₂, c₂⟩ := Rec.frame_span' hp (d := oEM2) (n := (s.gpr .rcx).toNat)
          (by unfold oEM2 frameBytes; omega_using [hk2])
        exact ⟨⟨r₁, List.mem_append_right _ h₁, c₁⟩, ⟨r₂, List.mem_append_right _ h₂, c₂⟩⟩
      exact WP.mono (compare_ok (by rw [hcx]) (by omega_using [hk1]) hr) fun u ⟨hK, hm, _⟩ =>
        ⟨s, S, he.regs (hK.gpr (by decide)) hm hK.2.1 hK.2.2, by rw [hK.gpr (by decide), hcx]⟩

theorem maskM_two : RelCT isa (Two (Rec.At JQ)) (.block maskM) (Two (Rec.At JQ)) :=
  two_piece [.rsp] (Rec.pins_rsp fun _ _ h => h.1.rsp) (by taint_decide)
    fun _ _ ⟨s, S, he, hcx⟩ => WP.mono (maskM_ok S.1 he) fun _ ⟨k, hm, _⟩ =>
      ⟨s, S, Env.low he (d := 8) (by decide) (k.gpr (by decide)) k.2.1 k.2.2 hm,
        by rw [k.gpr (by decide), hcx]⟩

theorem copyOut_two : RelCT isa (Two (Rec.At JQ)) copyOut (Two (Rec.At JE)) :=
  two_post (Rec.copyOut_ct fun _ _ h => h) fun _ _ ⟨s, S, he, hcx⟩ =>
    WP.mono (Rec.copyOut_ok S.1 he hcx) fun _ h => ⟨s, S, h.1⟩

def JM (s t : State) : Prop :=
  t.gpr .rsp = fb s ∧ t.gpr .rdi = s.gpr .rdi ∧ t.gpr .rcx = s.gpr .rsi ∧ t.gpr .r10 = BitVec.ofNat 64 0

theorem maskArgs_two : RelCT isa (Two (Rec.At JE)) (.block maskArgs) (Two (Rec.At JM)) :=
  two_piece [.rsp] (Rec.pins_rsp fun _ _ h => h.rsp) (by taint_decide)
    fun _ _ ⟨s, S, he⟩ => WP.mono (maskArgs_ok S.1 he) fun _ ⟨k, _, hdi, hcx, _, h10⟩ =>
      ⟨s, S, (k.gpr (by decide)).trans he.rsp, hdi, hcx, h10⟩

theorem mask_ct : RelCT isa (Two (Rec.At JM))
    (.seq Impl.RsaPkcs1Enc.X86_64.Encrypt.maskLoop (.block fin)) fun _ _ => True :=
  two_taint [.rsp, .rdi, .rcx, .r10] (fun _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Rec.pin fb (fun _ _ h => h.1) (fun _ _ S => S.fb) h₁ h₂
    · exact Rec.pin (fun s => s.gpr .rdi) (fun _ _ h => h.2.1) (fun _ _ S => S.gpr (by decide)) h₁ h₂
    · exact Rec.pin (fun s => s.gpr .rsi) (fun _ _ h => h.2.2.1) (fun _ _ S => S.gpr (by decide)) h₁ h₂
    · exact Rec.pin (fun _ => BitVec.ofNat 64 0) (fun _ _ h => h.2.2.2) (fun _ _ _ => rfl) h₁ h₂)
    (by taint_decide)

theorem release_ct : RelCT isa (Two (Rec.At JQ)) RecoverPrecomputed.release fun _ _ => True := by
  unfold RecoverPrecomputed.release
  exact RelCT.seq maskM_two (RelCT.seq copyOut_two (RelCT.seq maskArgs_two mask_ct))

theorem tail_ct : RelCT isa (Two (Rec.At JS)) RecoverPrecomputed.tail fun _ _ => True := by
  unfold RecoverPrecomputed.tail
  refine RelCT.seq test0_two (two_ite ?_ (Rec.two_and (Rec.zeroSlots_ct fun _ _ h => JT_none h.1 h.2))
    (RelCT.seq cmpArgs_two (RelCT.seq compare_two release_ct)))
  · exact Rec.pinEval (fun s => some !(stat s)) (fun s t h => by
      obtain ⟨_, _, _, hz⟩ := h; simp only [eval, hz]) fun _ _ S => by rw [stat_sib S]

theorem afterPub_ct : RelCT isa (Two (Rec.At JE)) RecoverPrecomputed.afterPub fun _ _ => True := by
  unfold RecoverPrecomputed.afterPub
  exact RelCT.seq head_two (RelCT.seq encode_two tail_ct)

/-! ## The whole function -/

theorem body_ct (v : PublicImpl) : RelCT isa (Two (At Rec.JA))
    (Impl.RsaPkcs1Sig.X86_64.RecoverPrecomputed.body v.name v.code) fun _ _ => True :=
  RelCT.seq pubArgs_two (RelCT.seq (call_two v) afterPub_ct)

theorem code_ct (v : PublicImpl) : RelCT isa (Two (At Rec.J0))
    (Impl.RsaPkcs1Sig.X86_64.RecoverPrecomputed.code v.name v.code) fun _ _ => True := by
  unfold Impl.RsaPkcs1Sig.X86_64.RecoverPrecomputed.code
  refine RelCT.seq lenCheck_two (two_ite ?_ zeroOut0_ct (relCT_alloc ((body_ct v).mono ?_ fun _ _ h => h)))
  · refine pinEval (fun s => some (!(stackArg s 2 == s.gpr .rcx))) (fun s t h => by
      simp only [eval, h.2.2, Option.map_some]) ?_
    intro a s S
    rw [S.arg (by decide) (by decide), S.gpr (by decide)]
  · rintro _ _ ⟨t₁, t₂, ⟨a, ⟨⟨s₁, S₁, j₁⟩, e₁⟩, ⟨⟨s₂, S₂, j₂⟩, e₂⟩⟩, rfl, rfl⟩
    have hg : ∀ {s t}, Rec.JL s t → isa.eval .ne t = some false → stackArg s 2 = s.gpr .rcx := fun j e => by
      simp only [eval, j.2.2, Option.map_some, Option.some.injEq, Bool.not_eq_false', beq_iff_eq] at e
      exact e
    exact ⟨a, ⟨s₁, S₁, t₁, j₁, hg j₁ e₁, rfl⟩, ⟨s₂, S₂, t₂, j₂, hg j₂ e₂, rfl⟩⟩

theorem code_constantTime (v : PublicImpl) :
    ConstantTime isa contract.pre contract.pub (Impl.RsaPkcs1Sig.X86_64.RecoverPrecomputed.code v.name v.code) :=
  RelCT.constantTime ((code_ct v).mono
    (fun s₁ s₂ ⟨h₁, h₂, hpub⟩ => ⟨s₁, ⟨s₁, ⟨h₁, pub_refl s₁⟩, rfl⟩, ⟨s₂, ⟨h₂, hpub⟩, rfl⟩⟩) fun _ _ h => h)

/-! ## `Verified` -/

/-- `vg_rsa_pkcs1_recover_precomputed`, calling the implementation `v` of
`vg_rsa_public_precomputed_checked`, meets the shared contract. -/
theorem code_verified (v : PublicImpl) :
    Verified target (Impl.RsaPkcs1Sig.X86_64.RecoverPrecomputed.code v.name v.code)
      (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi verStack) :=
  Verified.of_correct (k := contract) (code_correct v) (code_constantTime v) implies

/-- It writes `rsp` only in its frame's push and pop. -/
theorem code_spSafe (v : PublicImpl) :
    (Impl.RsaPkcs1Sig.X86_64.RecoverPrecomputed.code v.name v.code).all (fun i => !isa.writesSp i) = true := by
  simp only [Impl.RsaPkcs1Sig.X86_64.RecoverPrecomputed.code, Impl.RsaPkcs1Sig.X86_64.RecoverPrecomputed.body,
    Code.all, v.spSafe, Bool.true_and]
  decide +kernel

end VG.Proof.RsaPkcs1Sig.X86_64.RecPcCT
