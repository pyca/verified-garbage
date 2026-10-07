import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.SignCall
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.RecoverCorrect

/-!
# `vg_rsa_pkcs1_sign` on AArch64: correctness

The encoding into `EM` (`enc_ok`), then zeros to `out` if it fails, or the
private operation on `EM` and zeros to `EM` (`afterEnc_ok`), which is
RFC 8017 §8.2.1 (`signId_eq`); the whole function (`code_ok`).
-/

namespace VG.Proof.RsaPkcs1Sig.AArch64.Sgn

open VG VG.AArch64 VG.Impl.RsaPkcs1Sig.AArch64.Sign VG.WriteBytes
open VG.Impl.RsaPkcs1Sig.AArch64 (encode psLoop)
open VG.Impl.RsaPkcs1Sig.AArch64.Recover (zeroOut)
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_movz)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_addSp wp_mov EPre EPost EOut encodeId encode_ok fill_ok clob)
open VG.Proof.RsaPkcs1Sig (bytesAt_length bytesAt_writeBytes frame_writeBytes ne_of_disjoint bytes_apart)
open VG.Proof.RsaPkcs1Sig.AArch64.Ver (eval_zero')

theorem signId_eq (nB eB pB qB dPB dQB qInvB : List Byte) (x : BitVec 32) (H : List Byte) :
    Spec.RsaPkcs1Sig.signId nB eB pB qB dPB dQB qInvB x.toNat H =
      match encodeId x H nB.length with
      | some em => Spec.Rsa.privateChecked nB eB em pB qB dPB dQB qInvB
      | none => .invalid := by
  unfold Spec.RsaPkcs1Sig.signId encodeId Spec.RsaPkcs1Sig.sign
  cases Spec.RsaPkcs1Sig.Hash.ofId x.toNat <;> rfl

theorem encodeId_length {x : BitVec 32} {H : List Byte} {k : Nat} {em : List Byte}
    (h : encodeId x H k = some em) : em.length = k := by
  unfold encodeId at h
  split at h
  · exact VG.Proof.RsaPkcs1Sig.encode_length h
  · cases h

/-- The hash value, as the entry state gives it. -/
abbrev digest (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .x7) (stackArg s 0).toNat

/-- The encoding of the hash value, from the entry state. -/
def encOut (s : State) : Option (List Byte) :=
  encodeId ((s.gpr .x6).setWidth 32) (digest s) (s.gpr .x3).toNat

/-- The result: the private operation on the encoding, or `invalid`. -/
def sigOut (s : State) : Spec.Rsa.Outcome :=
  match encOut s with
  | some em => privOut s em
  | none => .invalid

/-! ## `Mid` -/

theorem Mid.only {s t w : State} {rs : List Reg} (h : Mid s t) (o : Only rs t w)
    (hrs : ∀ r ∈ rs, r ∉ [Reg.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28] := by decide) :
    Mid s w where
  sp := o.sp.trans h.sp
  rd := o.rd.trans h.rd
  wr := o.wr.trans h.wr
  x19 := (o.gpr _ fun h' => hrs _ h' (by decide)).trans h.x19
  hi := fun r hr => (o.gpr _ fun h' => hrs _ h' (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h | h | h | h | h | h | h <;> simp [h])).trans (h.hi r hr)
  v := fun r hr => (o.vcs r hr).trans (h.v r hr)
  sv := by rw [o.mem]; exact h.sv

theorem Mid.frame {s t w : State} {rs : List Reg} {R : Region} (h : Mid s t) (o : Keep rs t w)
    (hm : Frame [R] t.mem w.mem) (hd : Region.Disjoint ⟨fb s + BitVec.ofNat 64 96, 16⟩ R)
    (hrs : ∀ r ∈ rs, r ∉ [Reg.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28] := by decide) :
    Mid s w :=
  have hw : Mid s { t with gpr := w.gpr, v := w.v } :=
    Mid.only (w := { t with gpr := w.gpr, v := w.v }) h ⟨o.gpr, rfl, rfl, rfl, rfl, o.vcs⟩ hrs
  { hw with
    sp := o.sp.trans h.sp
    rd := o.rd.trans h.rd
    wr := o.wr.trans h.wr
    sv := h.sv.frame_in saved_offs hm fun r hr => by rw [List.mem_singleton.mp hr]; exact hd }

theorem AtEnc.mid {s u : State} (h : AtEnc s u) : Mid s u :=
  ⟨h.sp, h.rd, h.wr, h.x19, fun r hr => h.g r (by revert r; decide), h.v, h.sv⟩

/-! ## The steps -/

theorem enc_ok {K : Nat} {s u : State} (hp : PreS K s) (hu : AtEnc s u) :
    WP isa encode u fun w => Keep clob u w ∧ EOut u w (encOut s) := by
  have hk2 := hp.k2
  have hpre : EPre u ((s.gpr .x6).setWidth 32) (s.gpr .x3).toNat := {
    x10 := by rw [hu.x10]; simp
    hk := by rw [hu.x9]
    kle := hk2
    buf := fun i hi => by
      rw [hu.wr, hu.x8, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      exact in_frame _ _ (by unfold oEM frameBytes; omega)
    rd := fun j hj => by
      rw [hu.rd, hu.x11]; rw [hu.x12] at hj
      exact Covers.left (Covers.trans (Covers.of_mem fun x hx => by
        rw [List.mem_singleton.mp hx]; simp) hp.hrd) _ _ ⟨dR s, List.mem_singleton_self _,
        Offset.contains_base _ (by omega) (by have := hp.wd; omega)⟩
    sep := fun j hj i hi => by
      rw [hu.x11, hu.x8]; rw [hu.x12] at hj
      exact ne_of_disjoint (hp.kd.sub_left (em_sub hp)).symm (by have := hp.wd; omega) (by omega) hj hi }
  refine WP.mono (encode_ok hpre) fun w ⟨hK, hout⟩ => ⟨hK, ?_⟩
  have hH : Spec.Rsa.bytesAt u.mem (u.gpr .x11) (u.gpr .x12).toNat = digest s := by
    rw [hu.x11, hu.x12]; exact bytes_frame hu.mem hp.kd (by have := hp.wd; omega)
  rw [hH] at hout
  exact hout

/-- Zeros to `out`. -/
theorem zeroSlots_ok {K : Nat} {s u w : State} (hp : PreS K s) (hu : AtEnc s u) (hK : Keep clob u w)
    (hm : w.mem = u.mem) :
    WP isa zeroSlots w fun w' => Mid s w' ∧
      Spec.Rsa.writtenOutcome w'.mem (s.gpr .x0) (s.gpr .x3).toNat ((w'.gpr .x0).setWidth 32) .invalid := by
  have hk1 := hp.k1; have hk2 := hp.k2; have hol := hp.ol
  unfold zeroSlots
  refine WP.seq (wp_mov fun u₁ o₁ e₁ => wp_mov fun u₂ o₂ e₂ => wp_nil ?_)
  have O₂ : Only [.x14, .x13] w u₂ := (o₁.trans o₂).mono
  have midw : Mid s w := hu.mid.only (Ver.Only.of_keep hK hm)
  refine WP.mono (Rec.zeroOut_ok (p := s.gpr .x0) (n := (s.gpr .x3).toNat) (by omega) (by omega)
    (by rw [o₂.get .x14, e₁, hK.get .x17, hu.x17])
    (by rw [e₂, o₁.get .x19, midw.x19, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (fun i hi => by
      rw [O₂.wr, midw.wr]
      exact ⟨_, List.mem_cons_of_mem _ hp.hwo, Offset.contains_base _ (by omega) (by have := hp.wo; omega)⟩))
    fun w' ⟨k, mw, x0⟩ => ⟨?_, by rw [x0]; rfl, ?_⟩
  · have fw : Frame [⟨s.gpr .x0, (s.gpr .x3).toNat⟩] u₂.mem w'.mem := by
      rw [mw]; have := frame_writeBytes u₂.mem (s.gpr .x0) (List.replicate (s.gpr .x3).toNat 0)
      rwa [List.length_replicate] at this
    have ko' : (kR K s).Disjoint ⟨s.gpr .x0, (s.gpr .x3).toNat⟩ := by rw [← hol]; exact hp.ko
    exact (midw.only O₂).frame k fw (ko'.sub_left (frame_sub K s (d := 96) (n := 16) (by decide)))
  · rw [mw]
    have := bytesAt_writeBytes u₂.mem (s.gpr .x0) (List.replicate (s.gpr .x3).toNat 0) (by simp; omega)
    rwa [List.length_replicate] at this

/-- `EM` overwritten with zeros: `out`, `x0` and `Mid` are kept. -/
theorem wipe_ok {K : Nat} {s t : State} (hp : PreS K s) (hm : Mid s t) :
    WP isa wipe t fun w => Mid s w ∧ w.gpr .x0 = t.gpr .x0 ∧
      Spec.Rsa.bytesAt w.mem (s.gpr .x0) (s.gpr .x3).toNat = Spec.Rsa.bytesAt t.mem (s.gpr .x0) (s.gpr .x3).toNat := by
  have hk1 := hp.k1; have hk2 := hp.k2; have hol := hp.ol
  unfold wipe
  refine WP.seq (wp_addSp (by decide) fun u₁ o₁ e₁ => wp_mov fun u₂ o₂ e₂ => wp_movz fun u₃ o₃ e₃ => wp_nil ?_)
  have O₃ : Only [.x14, .x13, .x15] t u₃ := (o₁.trans (o₂.trans o₃)).mono
  have midu : Mid s u₃ := hm.only O₃
  refine WP.mono (fill_ok (p := fb s + BitVec.ofNat 64 oEM) (n := (s.gpr .x3).toNat) (b := 0) (by omega)
    (by omega) (by rw [o₃.get .x14, o₂.get .x14, e₁, hm.sp]) (by rw [o₃.get .x13, e₂, o₁.get .x19, hm.x19,
      BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by rw [e₃]; rfl) (fun i hi => by
        rw [midu.wr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
        exact in_frame _ _ (by unfold oEM frameBytes; omega))) fun w ⟨k, mw⟩ => ?_
  have fw : Frame [⟨fb s + BitVec.ofNat 64 oEM, (s.gpr .x3).toNat⟩] u₃.mem w.mem := by
    rw [mw]; have := frame_writeBytes u₃.mem (fb s + BitVec.ofNat 64 oEM) (List.replicate (s.gpr .x3).toNat 0)
    rwa [List.length_replicate] at this
  refine ⟨midu.frame k fw (slots_em hp (Nat.le_refl _)), by rw [k.get .x0, O₃.get .x0], ?_⟩
  rw [← O₃.mem]
  have ko' : (kR K s).Disjoint ⟨s.gpr .x0, (s.gpr .x3).toNat⟩ := by rw [← hol]; exact hp.ko
  exact bytes_apart (R := ⟨s.gpr .x0, (s.gpr .x3).toNat⟩) fw (ko'.sub_left (em_sub hp)).symm
    (by have := hp.wo; dsimp only; omega)


theorem writtenOutcome_of {m m' : Mem} {out : Addr} {n : Nat} {r : BitVec 32} {o : Spec.Rsa.Outcome}
    (hb : Spec.Rsa.bytesAt m' out n = Spec.Rsa.bytesAt m out n) (h : Spec.Rsa.writtenOutcome m out n r o) :
    Spec.Rsa.writtenOutcome m' out n r o := by
  cases o <;> exact ⟨h.1, hb.trans h.2⟩

theorem afterEnc_ok (c : PrivChecked) {s u w : State} (hp : PreS c.stack s) (hu : AtEnc s u)
    (hK : Keep clob u w) (hout : EOut u w (encOut s)) :
    WP isa (afterEnc c.name c.code) w fun w' => Mid s w' ∧
      Spec.Rsa.writtenOutcome w'.mem (s.gpr .x0) (s.gpr .x3).toNat ((w'.gpr .x0).setWidth 32) (sigOut s) := by
  unfold afterEnc sigOut
  cases heo : encOut s with
  | none =>
    rw [heo] at hout
    obtain ⟨h0, hm⟩ := hout
    exact WP.ite true ((eval_zero' w .x0).trans (by rw [h0]; rfl)) (fun _ => zeroSlots_ok hp hu hK hm) (by simp)
  | some em =>
    rw [heo] at hout
    obtain ⟨h1, hme⟩ := hout
    refine WP.ite false ((eval_zero' w .x0).trans (by rw [h1]; rfl)) (by simp) fun _ => ?_
    refine WP.seq (WP.mono (callArgs_ok hp hu hK hme (encodeId_length heo)) fun t ht => ?_)
    refine WP.seq (WP.mono (call_ok c hp ht) fun t' ht' => ?_)
    refine WP.mono (wipe_ok hp ht'.toMid) fun w' ⟨m', x0, hb⟩ => ⟨m', ?_⟩
    rw [x0]; exact writtenOutcome_of hb ht'.res

/-- The restores, then the frame's release: the caller's registers are back,
and `x0` and memory are kept. -/
theorem restore_ok {s w : State} (hm : Mid s w) :
    WP isa (.block restore) w fun w' =>
      abiPreserved s (freed frameBytes w') ∧ (freed frameBytes w').gpr .x0 = w.gpr .x0 ∧
        (freed frameBytes w').mem = w.mem := by
  unfold restore
  refine wp_addSp (by decide) fun w₁ o₁ e₁ => ?_
  rw [hm.sp, BitVec.add_zero] at e₁
  refine WP.mono (Spill.restore_wp (b := .x16) (l := saved) (B := fb s) e₁ saved_ho (by decide)
    (fun p hp' => by
      rw [o₁.rd, o₁.wr, hm.wr]
      exact InRegions_append_cons (xs := w.rd) |>.mpr (.inl (Offset.contains_base _
        (by have := saved_offs p hp'; unfold frameBytes; omega) (by have := saved_offs p hp'; omega))))
    (by rw [o₁.mem]; exact hm.sv)) fun w' hr => ⟨⟨fun r hr' => ?_, ?_, fun r hr' => ?_⟩, ?_, ?_⟩
  · simp only [freed]
    by_cases hs : r ∈ saved.map Prod.fst
    · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hs
      exact hr.gpr p hp'
    · have hr'' : r ∈ [Reg.x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28] := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr'
        rcases hr' with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> first | decide | simp_all [saved]
      have h16 : r ∉ [Reg.x16] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'' ⊢
        rcases hr'' with h | h | h | h | h | h | h | h | h <;> subst h <;> decide
      rw [hr.other r hs, o₁.gpr r h16]
      exact hm.hi r hr''
  · simp only [freed]
    rw [hr.sp, o₁.sp, hm.sp, BitVec.sub_add_cancel]
  · simp only [freed]
    rw [hr.v, o₁.vcs r hr', hm.v r hr']
  · simp only [freed]
    rw [hr.other .x0 (by decide), o₁.get .x0]
  · simp only [freed]
    rw [hr.mem, o₁.mem]

/-- `vg_rsa_pkcs1_sign`'s result, and the calling convention. -/
def Post (s s' : State) : Prop :=
  abiPreserved s s' ∧ Spec.Rsa.writtenOutcome s'.mem (s.gpr .x0) (s.gpr .x3).toNat ((s'.gpr .x0).setWidth 32)
    (sigOut s)

theorem code_ok (c : PrivChecked) {s : State} (hp : PreS c.stack s) :
    WP isa (code c.name c.code) s (Post s) := by
  unfold code
  refine WP.alloc (by decide) (by have := hp.sp1; unfold stk at this; omega) ?_
  unfold body
  refine WP.seq (WP.mono (encArgs_ok hp (by simp [allocated]) (by simp [allocated]) (by simp [allocated])
    (by simp [allocated]) (fun r => by simp [allocated]) (fun r _ => by simp [allocated])) fun u hu => ?_)
  refine WP.seq (WP.mono (enc_ok hp hu) fun w ⟨hK, hout⟩ => ?_)
  refine WP.seq (WP.mono (afterEnc_ok c hp hu hK hout) fun t ⟨m, r⟩ => ?_)
  exact WP.mono (restore_ok m) fun w ⟨habi, hx0, hmem⟩ => ⟨habi, by rw [hx0, hmem]; exact r⟩

end VG.Proof.RsaPkcs1Sig.AArch64.Sgn
