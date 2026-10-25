module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncTail
public import Mathlib.Data.Int.GCD
public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86_64.RecoverPrecomputed
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.RecoverCorrect
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCorrect
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.Compare
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.RecoverCall
import VerifiedGarbage.Proof.RsaPkcs1Sig.Verify
import VerifiedGarbage.Proof.Framework.Offset

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
    exact decide_eq_false (by omega)

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
  have hs := he.scr hp
  refine WP.mono (WP.keep [.rdx, .rax] (Q := fun u =>
      u.mem = t.mem.writeW (off (fb s) 8) (pmask (okOf (t.gpr .rdx) (word t.mem (fb s) 0))) ∧
      u.gpr .rdx = pmask (okOf (t.gpr .rdx) (word t.mem (fb s) 0))) ?_ rfl) fun u ⟨h, k⟩ => ⟨k, h⟩
  have h0 : InRegions (t.rd ++ t.wr) (fb s) 8 := by
    simpa only [off, BitVec.add_zero] using hs.ld (d := 0) (by decide)
  xrun [maskM, ea_sp, he.rsp, h0, hs.st (d := 8) (by decide)]
  have hw : Bignum.word t.mem (fb s) 0 = t.mem.readW (fb s) 64 := by simp only [Bignum.word, off, BitVec.add_zero]
  rw [hw, show (1 : BitVec 64).toNat = 1 from rfl, show (1 : BitVec 32).toNat = 1 from rfl, maskM_val]
  exact ⟨rfl, rfl⟩

/-- `Env` past a store to the frame's word at `d < 32`, under the slots. -/
theorem Env.low {s t u : State} (he : Env s t) {d : Nat} (hd : d + 8 ≤ 32) {v : BitVec 64}
    (hsp : u.gpr .rsp = t.gpr .rsp) (hrd : u.rd = t.rd) (hwr : u.wr = t.wr)
    (hm : u.mem = t.mem.writeW (off (fb s) d) v) : Env s u := by
  have hf : Frame [⟨off (fb s) d, 8⟩] t.mem u.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hw : ∀ {d'}, 32 ≤ d' → d' + 8 ≤ 4096 → Bignum.word u.mem (fb s) d' = Bignum.word t.mem (fb s) d' :=
    fun h₁ h₂ => by rw [hm]; exact word_wo _ _ _ (.inl (by omega)) (by omega) h₂
  exact ⟨hsp.trans he.rsp, hrd.trans he.rd, hwr.trans he.wr,
    frame_call he.mem hf fun r hr => by
      rw [List.mem_singleton.mp hr]; exact .inl (frame_sub s (by unfold frameBytes; omega)),
    (hw (by decide) (by decide)).trans he.sOut, (hw (by decide) (by decide)).trans he.sOl,
    (hw (by decide) (by decide)).trans he.sN, (hw (by decide) (by decide)).trans he.sK,
    (hw (by decide) (by decide)).trans he.sE, (hw (by decide) (by decide)).trans he.sEl⟩

/-- Bytes of the frame from `EM₁` on, past a store to a word below `32`. -/
theorem bytes_low {s : State} {m : Mem} {d : Nat} (hd : d + 8 ≤ 32) (v : BitVec 64) {e n : Nat}
    (he : oEM1 ≤ e) (hn : e + n ≤ frameBytes) :
    Spec.Rsa.bytesAt (m.writeW (off (fb s) d) v) (off (fb s) e) n = Spec.Rsa.bytesAt m (off (fb s) e) n := by
  have hf : Frame [⟨off (fb s) d, 8⟩] m (m.writeW (off (fb s) d) v) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => hf.bytes (R := ⟨off (fb s) e, n⟩) (fun r hr => ?_)
    (by show n ≤ 2 ^ 64; unfold frameBytes at hn; omega) (List.mem_range.mp hi)
  rw [List.mem_singleton.mp hr]
  exact Offset.disjoint _ (.inr (by unfold oEM1 at he; omega)) (by unfold frameBytes at hn; omega) (by omega)

theorem maskArgs_ok {s t : State} (hp : PreR s) (he : Env s t) :
    WP isa (.block maskArgs) t fun u => Keep [.rdi, .rcx, .rdx, .r10] t u ∧ u.mem = t.mem ∧
      u.gpr .rdi = s.gpr .rdi ∧ u.gpr .rcx = s.gpr .rsi ∧ u.gpr .rdx = Bignum.word t.mem (fb s) 8 ∧
      u.gpr .r10 = BitVec.ofNat 64 0 := by
  have hs := he.scr hp
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
  have hF := fb_toNat hp
  have e1 : oEM1 = 80 := rfl
  have e2 : frameBytes = 2136 := rfl
  have e3 : Impl.RsaPkcs1Enc.X86_64.Encrypt.oEM = 80 := rfl
  set ok := okOf (t.gpr .rdx) (Bignum.word t.mem (fb s) 0)
  set n := (s.gpr .rsi).toNat with hn
  unfold RecoverPrecomputed.release
  refine WP.seq (WP.mono (maskM_ok hp he) fun t₁ ⟨k₁, hm₁, _⟩ => ?_)
  have he₁ : Env s t₁ := Env.low he (d := 8) (by decide) (k₁.gpr (by decide)) k₁.2.1 k₁.2.2 hm₁
  have hv₁ : Spec.Rsa.bytesAt t₁.mem (valA s) n = Spec.Rsa.bytesAt t.mem (valA s) n := by
    rw [hm₁]
    exact bytes_low (s := s) (d := 8) (by decide) _ (e := oEM1 + ((s.gpr .rcx).toNat - n)) (by omega) (by omega)
  refine WP.seq (WP.mono (copyOut_ok hp he₁ (by rw [k₁.gpr (by decide), hcx])) fun t₂ ⟨he₂, _, hout₂, hm₂⟩ => ?_)
  have hw8 : Bignum.word t₂.mem (fb s) 8 = pmask ok := by
    rw [hm₂, slot_keep (frame_writeBytes _ _ _) (fun r hr => ?_), hm₁, word_writeW_self]
    rw [List.mem_singleton.mp hr, bytesAt_length]
    exact (hp.dKo.sub_left (frame_sub s (by unfold frameBytes; omega)))
  refine WP.seq (WP.mono (maskArgs_ok hp he₂) fun t₃ ⟨k₃, hm₃, hdi₃, hcx₃, hdx₃, h10₃⟩ => ?_)
  have he₃ : Env s t₃ := he₂.regs (k₃.gpr (by decide)) hm₃ k₃.2.1 k₃.2.2
  have hwr : outR s ∈ t₃.wr := by rw [he₃.wr, hp.hwr]; simp [outR]
  have hdK : (⟨off (fb s) Impl.RsaPkcs1Enc.X86_64.Encrypt.oEM, n⟩ : Region).Disjoint (outR s) :=
    hp.dKo.sub_left (frame_sub s (by unfold frameBytes; omega))
  refine WP.seq (WP.mono (maskLoop_ok (k := n) (S := fb s) (op := s.gpr .rdi) (ok := ok) (by omega)
    (by omega) he₃.rsp hdi₃ (by rw [hdx₃, hw8]) (by rw [hcx₃, hn]; simp) h10₃ (out_wr hwr)
    (fun i hi => by rw [he₃.wr]; exact frame_bytes' hp (by unfold frameBytes; omega) i hi)
    (fun i hi i' hi' => ne_of_disjoint hdK.symm (by omega) (by omega) hi hi')) fun t₄ hR => ?_)
  refine WP.mono (WP.keep [.rax] (Q := fun u => u.mem = t₄.mem ∧ u.gpr .rax = t₄.gpr .rdx &&& 1#64) (by
    xrun [fin]; rfl) rfl) fun u ⟨⟨hm, hax⟩, k⟩ => ⟨?_, ?_⟩
  · have hrdx : t₄.gpr .rdx = pmask ok := by rw [hR.keep.gpr (by decide), hdx₃, hw8]
    refine Env.of he₂ hp ((k.gpr (by decide)).trans ((hR.keep.gpr (by decide)).trans (k₃.gpr (by decide))))
      (k.2.1.trans (hR.keep.2.1.trans k₃.2.1)) (k.2.2.trans (hR.keep.2.2.trans k₃.2.2))
      (rs := [outR s, ⟨off (fb s) 80, n⟩]) (fun x hx => ?_) fun r hr => ?_
    · rw [hm, hR.frame x (fun i hi he' => hx _ (List.mem_cons_self ..) (by
          rw [he']; exact contains_of_byte rfl (by omega) hi))
        (fun i hi he' => hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) (by
          rw [he']; exact contains_of_byte rfl (by omega) hi)), hm₃]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inr rfl
      · exact .inl ⟨80, n, rfl, le_refl _, by omega⟩
  · have hrdx : t₄.gpr .rdx = pmask ok := by rw [hR.keep.gpr (by decide), hdx₃, hw8]
    rw [hax, hrdx, pmask_and1]
    have hb : Spec.Rsa.bytesAt u.mem (s.gpr .rdi) n =
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
  have hF := fb_toNat hp
  set k := (s.gpr .rcx).toNat with hkdef
  have dVE : (⟨valA s, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨off (fb s) oEM2, k⟩ :=
    Offset.disjoint _ (.inl (by unfold oEM1 oEM2; omega_arith)) (by unfold oEM1 frameBytes at *; omega_arith)
      (by unfold oEM2 frameBytes at *; omega_arith)
  unfold RecoverPrecomputed.tail
  refine WP.seq (WP.mono (test0_ok t₃) fun t₄ ⟨hs₄, hz₄⟩ => ?_)
  cases o with
  | none =>
    obtain ⟨hax, hm₃⟩ := hpost
    have he₄ : Env s t₄ := he₂.regs (by rw [hs₄.1, hK₃.gpr (by decide)]) (hs₄.2.1.trans hm₃)
      (hs₄.2.2.1.trans hK₃.2.1) (hs₄.2.2.2.trans hK₃.2.2)
    refine WP.ite true (by simp [eval, hz₄, hax]) (fun _ => ?_) (by simp)
    simp only [reduceCtorEq, and_false, ↓reduceIte]
    exact zeroSlots_ok hp he₄
  | some em' =>
    obtain ⟨hax, hm₃⟩ := hpost
    have hl' : em'.length = k := VG.Proof.RsaPkcs1Sig.encode_length ho
    have he₃ : Env s t₃ := Env.of he₂ hp (hK₃.gpr (by decide)) hK₃.2.1 hK₃.2.2 (hm₃ ▸ frame_writeBytes _ _ _)
      fun r hr => .inl ⟨oEM2, k, by rw [List.mem_singleton.mp hr, h8₂, hl'], by decide,
        by unfold oEM2 frameBytes; omega_arith⟩
    have he₄ : Env s t₄ := he₃.regs (by rw [hs₄.1]) hs₄.2.1 hs₄.2.2.1 hs₄.2.2.2
    refine WP.ite false (by simp [eval, hz₄, hax]) (by simp) (fun _ => ?_)
    refine WP.seq (WP.mono (cmpArgs_ok he₄) fun t₅ ⟨hK₅, hm₅, hdi₅, hsi₅⟩ => ?_)
    have hcx₅ : t₅.gpr .rcx = s.gpr .rcx := by
      rw [hK₅.gpr (by decide), hs₄.1, hK₃.gpr (by decide), hcx₂]
    have he₅ : Env s t₅ := he₄.regs (hK₅.gpr (by decide)) hm₅ hK₅.2.1 hK₅.2.2
    have hr5 : InRegions (t₅.rd ++ t₅.wr) (t₅.gpr .rdi) k ∧ InRegions (t₅.rd ++ t₅.wr) (t₅.gpr .rsi) k := by
      rw [hdi₅, hsi₅, he₅.wr]
      obtain ⟨r₁, h₁, c₁⟩ := frame_span' hp (d := oEM1) (n := k) (by unfold oEM1 frameBytes; omega_arith)
      obtain ⟨r₂, h₂, c₂⟩ := frame_span' hp (d := oEM2) (n := k) (by unfold oEM2 frameBytes; omega_arith)
      exact ⟨⟨r₁, List.mem_append_right _ h₁, c₁⟩, ⟨r₂, List.mem_append_right _ h₂, c₂⟩⟩
    refine WP.seq (WP.mono (compare_ok (by rw [hcx₅]) (by omega_arith) hr5) fun t₆ ⟨hK₆, hm₆, hdx₆⟩ => ?_)
    have he₆ : Env s t₆ := he₅.regs (hK₆.gpr (by decide)) hm₆ hK₆.2.1 hK₆.2.2
    have hmem : ∀ {p : Addr} {n : Nat}, (⟨p, n⟩ : Region).Disjoint ⟨off (fb s) oEM2, em'.length⟩ → n ≤ 2 ^ 64 →
        Spec.Rsa.bytesAt t₃.mem p n = Spec.Rsa.bytesAt t₂.mem p n := fun {p n} hd hn => by
      rw [hm₃, h8₂]
      simp only [Spec.Rsa.bytesAt]
      exact List.map_congr_left fun i hi =>
        (frame_writeBytes t₂.mem _ em').bytes (R := ⟨p, n⟩) (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd)
          hn (List.mem_range.mp hi)
    have d12 : (⟨off (fb s) oEM1, k⟩ : Region).Disjoint ⟨off (fb s) oEM2, em'.length⟩ := by
      rw [hl']
      exact Offset.disjoint _ (.inl (by unfold oEM1 oEM2; omega_arith)) (by unfold oEM1 frameBytes at *; omega_arith)
        (by unfold oEM2 frameBytes at *; omega_arith)
    have h1 : Spec.Rsa.bytesAt t₃.mem (off (fb s) oEM1) k = em := by
      rw [hmem d12 (by omega_arith), hem]
    have h2 : Spec.Rsa.bytesAt t₃.mem (off (fb s) oEM2) k = em' := by
      have := bytesAt_writeBytes t₂.mem (off (fb s) oEM2) em' (by omega_arith)
      rw [hl'] at this
      rw [hm₃, h8₂]; exact this
    have hdiff : (t₆.gpr .rdx = 0) ↔ em = em' := by
      rw [hdx₆, hdi₅, hsi₅, EqBytes, ← bytesAt_eq_iff, hm₅, hs₄.2.1, h1, h2]
    have hw0 : Bignum.word t₆.mem (fb s) 0 = st := by
      rw [hm₆, hm₅, hs₄.2.1, hm₃, h8₂, slot_keep (frame_writeBytes _ _ _) (fun r hr => ?_), hst]
      rw [List.mem_singleton.mp hr, hl']
      exact Offset.disjoint _ (.inl (by unfold oEM2; omega_arith)) (by decide)
        (by unfold oEM2 frameBytes at *; omega_arith)
    have hv : Spec.Rsa.bytesAt t₆.mem (valA s) (s.gpr .rsi).toNat = em.drop (k - (s.gpr .rsi).toNat) := by
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
  have hs := he.scr hp
  have h0 : InRegions t.wr (fb s) 8 := by simpa only [off, BitVec.add_zero] using hs.st (d := 0) (by decide)
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
  have hF := fb_toNat hp
  have hol : (s.gpr .rsi).toNat = h.len := by
    obtain ⟨h', hid', hl⟩ := hp.hash; rw [hid] at hid'; cases hid'; exact hl
  set k := (s.gpr .rcx).toNat with hkdef
  set em := Spec.Rsa.bytesAt t.mem (off (fb s) oEM1) k
  unfold RecoverPrecomputed.afterPub
  rw [WP.seq_iff, WP.block_append_iff]
  refine WP.mono (save_ok hp he) fun t₁ ⟨k₁, hm₁⟩ => ?_
  have he₁ : Env s t₁ := Env.low he (d := 0) (by decide) (k₁.gpr (by decide)) k₁.2.1 k₁.2.2 hm₁
  refine WP.mono (encArgs_ok hp he₁) fun t₂ ⟨hK₂, hm₂, h8₂, hcx₂, hdx₂, h9₂, hsi₂⟩ => ?_
  have he₂ : Env s t₂ := he₁.regs (hK₂.gpr (by decide)) hm₂ hK₂.2.1 hK₂.2.2
  have hem : Spec.Rsa.bytesAt t₂.mem (off (fb s) oEM1) k = em := by
    rw [hm₂, hm₁]; exact bytes_low (by decide) _ (le_refl _) (by unfold oEM1 frameBytes; omega)
  have hst : Bignum.word t₂.mem (fb s) 0 = t.gpr .rax := by
    rw [hm₂, hm₁]; exact word_writeW_self _ _ _ _
  have hval : Spec.Rsa.bytesAt t₂.mem (valA s) (s.gpr .rsi).toNat = em.drop (k - (s.gpr .rsi).toNat) := by
    rw [valBytes hp, hem]
  have hE : ∀ H, encodeId ((stackArg s 0).setWidth 32) H k = Spec.RsaPkcs1Sig.encode h H k := fun H => by
    simp only [encodeId, hid]
  refine WP.seq (WP.mono (encode_ok (encPre hp he₂ h8₂ hcx₂ hdx₂ h9₂ hsi₂)) fun t₃ ⟨hK₃, hpost⟩ => ?_)
  rw [hsi₂, h9₂, hval, hE, hol] at hpost
  refine WP.mono (tail_ok (h := h) hp he₂ hK₃ hcx₂ h8₂ hem hval hst rfl hpost) fun u ⟨heu, hwu⟩ => ⟨heu, ?_⟩
  simp only [relOut, hol] at hwu ⊢
  exact hwu

end VG.Proof.RsaPkcs1Sig.X86_64.RecPc
