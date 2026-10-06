import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.RecoverCall
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.VerifyCorrect
import VerifiedGarbage.Proof.RsaPkcs1Sig.Recover

/-!
# `vg_rsa_pkcs1_recover` on AArch64: correctness

After the call (`AfterCall`): the encoding of the last `out_len` bytes of
`EM₁` into `EM₂` (`encode`), their comparison (`compare`) and the release
of those bytes to `out`, or zeros (`afterPub_ok`), which is BoringSSL's
recovery (`recover_eq_recoverEnc`).
-/

namespace VG.Proof.RsaPkcs1Sig.AArch64.Rec

open VG VG.AArch64 VG.Impl.RsaPkcs1Sig.AArch64.Recover VG.WriteBytes
open VG.Impl.RsaPkcs1Sig.AArch64 (encode compare psLoop copyLoop)
open VG.Impl.RsaPkcs1Sig.AArch64.Verify (frameBytes oEM1 oEM2 saved restore)
open VG.Proof.RsaPkcs1Sig.AArch64.Ver (stk sR aR kR fb kb frame_sub in_frame saved_offs saved_ho eval_zero')
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_movz wp_add wp_sub eval_nonzero ne_zero_iff)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_addSp wp_mov wp_movw EPre EPost EOut encodeId encode_ok compare_ok
  fill_ok copy_ok)
open VG.Proof.RsaPkcs1Sig (bytesAt_length bytesAt_writeBytes frame_writeBytes ne_of_disjoint bytesAt_drop)

/-! ## `Mid` -/

/-- `Mid` is kept by code that writes only registers other than `x19`–`x28`. -/
theorem Mid.only {s t w : State} {rs : List Reg} (h : Mid s t) (o : Only rs t w)
    (hrs : ∀ r ∈ rs, r ∉ [Reg.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28] := by decide) :
    Mid s w where
  sp := o.sp.trans h.sp
  rd := o.rd.trans h.rd
  wr := o.wr.trans h.wr
  x19 := (o.gpr _ fun h' => hrs _ h' (by decide)).trans h.x19
  x20 := (o.gpr _ fun h' => hrs _ h' (by decide)).trans h.x20
  x21 := (o.gpr _ fun h' => hrs _ h' (by decide)).trans h.x21
  x22 := (o.gpr _ fun h' => hrs _ h' (by decide)).trans h.x22
  hi := fun r hr => (o.gpr _ fun h' => hrs _ h' (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h | h | h | h <;> simp [h])).trans (h.hi r hr)
  v := fun r hr => (o.vcs r hr).trans (h.v r hr)
  sv := by rw [o.mem]; exact h.sv

/-- `Mid` is kept by code that writes only registers other than `x19`–`x28`
and memory apart from the saved registers' slots. -/
theorem Mid.frame {s t w : State} {rs : List Reg} {R : Region} (h : Mid s t) (o : Keep rs t w)
    (hm : Frame [R] t.mem w.mem) (hd : Region.Disjoint ⟨fb s + BitVec.ofNat 64 16, 40⟩ R)
    (hrs : ∀ r ∈ rs, r ∉ [Reg.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28] := by decide) :
    Mid s w :=
  have hw : Mid s { t with gpr := w.gpr, v := w.v } :=
    Mid.only (w := { t with gpr := w.gpr, v := w.v }) h ⟨o.gpr, rfl, rfl, rfl, rfl, o.vcs⟩ hrs
  { hw with
    sp := o.sp.trans h.sp
    rd := o.rd.trans h.rd
    wr := o.wr.trans h.wr
    sv := h.sv.frame_in saved_offs hm fun r hr => by rw [List.mem_singleton.mp hr]; exact hd }

/-- The saved registers' slots are apart from `out`. -/
theorem slots_out {K : Nat} {s : State} (hp : PreR K s) :
    Region.Disjoint ⟨fb s + BitVec.ofNat 64 16, 40⟩ (oR s) :=
  hp.ko.sub_left (frame_sub K s (d := 16) (n := 40) (by decide))

/-- `out` is writable. -/
theorem out_wr {K : Nat} {s : State} (hp : PreR K s) (rs : List Region) :
    ∀ i < (s.gpr .x1).toNat, InRegions (rs ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 i) 1 := fun i hi =>
  ⟨_, List.mem_append_right _ hp.hwo, Offset.contains_base _ (by omega) (by have := hp.wo; omega)⟩

/-! ## Zeros to `out` -/

theorem zeroOut_ok {u : State} {p : Addr} {n : Nat} (hn : 0 < n) (hn' : n < 2 ^ 64)
    (h14 : u.gpr .x14 = p) (h13 : u.gpr .x13 = BitVec.ofNat 64 n)
    (hw : ∀ i < n, InRegions u.wr (p + BitVec.ofNat 64 i) 1) :
    WP isa zeroOut u fun w => Keep [.x15, .x13, .x14, .x0] u w ∧
      w.mem = writeBytes u.mem p (List.replicate n 0) ∧ w.gpr .x0 = 0 := by
  unfold zeroOut
  refine WP.seq (wp_movz fun u₁ o₁ e₁ => wp_nil ?_)
  refine WP.seq (WP.mono (fill_ok (p := p) (b := 0) hn hn' (by rw [o₁.get .x14, h14]) (by rw [o₁.get .x13, h13])
    (by rw [e₁]; rfl) (by rw [o₁.wr]; exact hw)) fun u₂ ⟨k₂, m₂⟩ => ?_)
  exact wp_movz fun u₃ o₃ e₃ => wp_nil ⟨(o₁.keep.trans (k₂.trans o₃.keep)).mono, by
    rw [o₃.mem, m₂, o₁.mem], by rw [e₃]; rfl⟩

/-- Zeros to `out`, from `Mid`. -/
theorem zeroKept_ok {K : Nat} {s t : State} (hp : PreR K s) (hm : Mid s t) :
    WP isa zeroKept t fun w => Mid s w ∧
      Spec.Rsa.written w.mem (s.gpr .x0) (s.gpr .x1).toNat ((w.gpr .x0).setWidth 32) none := by
  obtain ⟨hl0, hl1⟩ := hlen hp
  have := hp.k2
  unfold zeroKept
  refine WP.seq (wp_mov fun u₁ o₁ e₁ => wp_mov fun u₂ o₂ e₂ => wp_nil ?_)
  have O₂ : Only [.x14, .x13] t u₂ := (o₁.trans o₂).mono
  refine WP.mono (zeroOut_ok (p := s.gpr .x0) (n := (s.gpr .x1).toNat) hl0 (by omega)
    (by rw [o₂.get .x14, e₁, hm.x19]) (by rw [e₂, o₁.get .x20, hm.x20, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (by rw [O₂.wr, hm.wr]; exact out_wr hp [_])) fun w ⟨k, mw, x0⟩ => ⟨?_, ?_, ?_⟩
  · refine (hm.only O₂).frame k (R := oR s) (by
      rw [mw]; have := frame_writeBytes u₂.mem (s.gpr .x0) (List.replicate (s.gpr .x1).toNat 0)
      rwa [List.length_replicate] at this) (slots_out hp)
  · rw [x0]; rfl
  · rw [mw]
    have := bytesAt_writeBytes u₂.mem (s.gpr .x0) (List.replicate (s.gpr .x1).toNat 0) (by simp; omega)
    rwa [List.length_replicate] at this

/-! ## The hash value's place in `EM₁` -/

/-- The last `out_len` bytes of `EM₁`. -/
abbrev valA (s : State) : Addr := fb s + BitVec.ofNat 64 (oEM1 + ((s.gpr .x3).toNat - (s.gpr .x1).toNat))

theorem addSub_eq (b x y : BitVec 64) {d : Nat} (h : y.toNat ≤ x.toNat) :
    b + BitVec.ofNat 64 d + x - y = b + BitVec.ofNat 64 (d + (x.toNat - y.toNat)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem valPtr_ok {K : Nat} {s u : State} (hp : PreR K s) (hsp : u.sp = fb s) (h21 : u.gpr .x21 = s.gpr .x3)
    (h20 : u.gpr .x20 = s.gpr .x1) :
    WP isa (.block valPtr) u fun u' => Only [.x11] u u' ∧ u'.gpr .x11 = valA s := by
  have := hlen hp; have := hp.k2
  unfold valPtr
  refine wp_addSp (by decide) fun u₁ o₁ e₁ => wp_add fun u₂ o₂ e₂ => wp_sub fun u₃ o₃ e₃ =>
    wp_nil ⟨(o₁.trans (o₂.trans o₃)).mono, ?_⟩
  rw [e₃, e₂, e₁, o₁.get .x21, o₂.get .x20, o₁.get .x20, h21, h20, hsp,
    addSub_eq _ _ _ (by omega)]


theorem valA_eq (s : State) :
    valA s = fb s + BitVec.ofNat 64 oEM1 + BitVec.ofNat 64 ((s.gpr .x3).toNat - (s.gpr .x1).toNat) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem valA_sub {K : Nat} {s : State} (hp : PreR K s) : Region.Sub ⟨valA s, (s.gpr .x1).toNat⟩ (kR K s) :=
  frame_sub K s (by have := hlen hp; have := hp.k2; unfold oEM1 frameBytes; omega)

/-- The last `out_len` bytes of `EM₁`. -/
theorem val_bytes {s : State} {m : Mem} {em : List Byte} (hl : (s.gpr .x1).toNat ≤ (s.gpr .x3).toNat)
    (hem : Spec.Rsa.bytesAt m (fb s + BitVec.ofNat 64 oEM1) (s.gpr .x3).toNat = em) :
    Spec.Rsa.bytesAt m (valA s) (s.gpr .x1).toNat = em.drop ((s.gpr .x3).toNat - (s.gpr .x1).toNat) := by
  rw [← hem, valA_eq, ← bytesAt_drop, Nat.sub_add_cancel hl]

/-- Bytes in the frame are readable. -/
theorem frame_bytes {s u : State} (hwr : u.wr = ⟨fb s, frameBytes⟩ :: s.wr) {d n : Nat}
    (h : d + n ≤ frameBytes) :
    ∀ j < n, InRegions (u.rd ++ u.wr) (fb s + BitVec.ofNat 64 d + BitVec.ofNat 64 j) 1 := fun j hj => by
  rw [hwr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  exact InRegions_append_cons (xs := u.rd) |>.mpr (.inl (Offset.contains_base _ (by omega)
    (by unfold frameBytes at h; omega)))

/-- Bytes apart from those written. -/
theorem bytes_apart {m m' : Mem} {R W : Region} (hf : Frame [W] m m') (hd : R.Disjoint W) (hl : R.len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' R.base R.len = Spec.Rsa.bytesAt m R.base R.len := by
  simp only [Spec.Rsa.bytesAt]
  exact List.map_congr_left fun i hi => hf.bytes (R := R) (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd)
    hl (List.mem_range.mp hi)

/-! ## The release of the hash value -/

theorem copyOut_ok {K : Nat} {s y : State} (hp : PreR K s) (hm : Mid s y) :
    WP isa copyOut y fun w => Mid s w ∧ Spec.Rsa.written w.mem (s.gpr .x0) (s.gpr .x1).toNat
      ((w.gpr .x0).setWidth 32) (some (Spec.Rsa.bytesAt y.mem (valA s) (s.gpr .x1).toNat)) := by
  obtain ⟨hl0, hl1⟩ := hlen hp
  have := hp.k2
  unfold copyOut
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (wp_mov fun u₁ o₁ e₁ => wp_mov fun u₂ o₂ e₂ => ?_)
  have O₂ : Only [.x14, .x12] y u₂ := (o₁.trans o₂).mono
  refine WP.mono (valPtr_ok hp (by rw [O₂.sp, hm.sp]) (by rw [O₂.get .x21, hm.x21])
    (by rw [O₂.get .x20, hm.x20])) fun u₃ ⟨o₃, e₃⟩ => ?_
  have O₃ : Only [.x14, .x12, .x11] y u₃ := (O₂.trans o₃).mono
  have hd : (⟨valA s, (s.gpr .x1).toNat⟩ : Region).Disjoint (oR s) := hp.ko.sub_left (valA_sub hp)
  refine WP.seq (WP.mono (copy_ok (p := s.gpr .x0) (q := valA s) (n := (s.gpr .x1).toNat) hl0 (by omega)
    (by rw [o₃.get .x14, o₂.get .x14, e₁, hm.x19]) e₃
    (by rw [o₃.get .x12, e₂, o₁.get .x20, hm.x20, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (fun j hj => frame_bytes (by rw [O₃.wr, hm.wr]) (by unfold oEM1 frameBytes; omega) j hj)
    (by rw [O₃.wr, hm.wr]; exact out_wr hp [_])
    (fun j hj i hi => ne_of_disjoint hd (by omega) (by omega) hj hi)) fun u₄ ⟨k₄, m₄⟩ => ?_)
  refine wp_movz fun u₅ o₅ e₅ => wp_nil ⟨((hm.only O₃).frame k₄ (R := oR s) (by
    rw [m₄]; have := frame_writeBytes u₃.mem (s.gpr .x0) (Spec.Rsa.bytesAt u₃.mem (valA s) (s.gpr .x1).toNat)
    rwa [bytesAt_length] at this) (slots_out hp)).only o₅, by rw [e₅]; rfl, ?_⟩
  rw [o₅.mem, m₄, O₃.mem]
  have := bytesAt_writeBytes y.mem (s.gpr .x0) (Spec.Rsa.bytesAt y.mem (valA s) (s.gpr .x1).toNat)
    (by rw [bytesAt_length]; omega)
  rwa [bytesAt_length] at this

/-! ## After the call -/

/-- `vg_rsa_pkcs1_recover`'s result, from the entry state, for the hash
function `h`, if the signature is `k` bytes. -/
def recOut (s : State) (h : Spec.RsaPkcs1Sig.Hash) : Option (List Byte) :=
  match pubOut s with
  | some em =>
    if Spec.RsaPkcs1Sig.encode h (em.drop ((s.gpr .x3).toNat - h.len)) (s.gpr .x3).toNat = some em then
      some (em.drop ((s.gpr .x3).toNat - h.len))
    else none
  | none => none

theorem encArgs_ok {K : Nat} {s t : State} (hp : PreR K s) (hm : Mid s t) :
    WP isa (.block encArgs) t fun u => Only [.x8, .x9, .x10, .x12, .x11] t u ∧
      u.gpr .x8 = fb s + BitVec.ofNat 64 oEM2 ∧ u.gpr .x9 = s.gpr .x3 ∧
      u.gpr .x10 = ((s.gpr .x6).setWidth 32).setWidth 64 ∧ u.gpr .x12 = s.gpr .x1 ∧ u.gpr .x11 = valA s := by
  unfold encArgs
  rw [WP.block_append_iff]
  refine wp_addSp (by decide) fun u₁ o₁ e₁ => wp_mov fun u₂ o₂ e₂ => wp_mov fun u₃ o₃ e₃ =>
    wp_mov fun u₄ o₄ e₄ => wp_nil ?_
  have O₄ : Only [.x8, .x9, .x10, .x12] t u₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
  refine WP.mono (valPtr_ok hp (by rw [O₄.sp, hm.sp]) (by rw [O₄.get .x21, hm.x21]) (by rw [O₄.get .x20, hm.x20]))
    fun u ⟨o, e⟩ => ⟨(O₄.trans o).mono, ?_, ?_, ?_, ?_, e⟩
  · rw [o.get .x8, o₄.get .x8, o₃.get .x8, o₂.get .x8, e₁, hm.sp]
  · rw [o.get .x9, o₄.get .x9, o₃.get .x9, e₂, o₁.get .x21, hm.x21]
  · rw [o.get .x10, o₄.get .x10, e₃, o₂.get .x22, o₁.get .x22, hm.x22]
  · rw [o.get .x12, e₄, o₃.get .x20, o₂.get .x20, o₁.get .x20, hm.x20]

/-- The encoding of the last `h.len` bytes of `em`, with `k` bytes. -/
def encRes (s : State) (h : Spec.RsaPkcs1Sig.Hash) (em : List Byte) : Option (List Byte) :=
  Spec.RsaPkcs1Sig.encode h (em.drop ((s.gpr .x3).toNat - h.len)) (s.gpr .x3).toNat

/-- Before `encode`, `EM₁` holding `em`. -/
structure AtEnc (s : State) (em : List Byte) (u : State) : Prop where
  mid : Mid s u
  x8 : u.gpr .x8 = fb s + BitVec.ofNat 64 oEM2
  x9 : u.gpr .x9 = s.gpr .x3
  x10 : u.gpr .x10 = ((s.gpr .x6).setWidth 32).setWidth 64
  x12 : u.gpr .x12 = s.gpr .x1
  x11 : u.gpr .x11 = valA s
  em1 : Spec.Rsa.bytesAt u.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .x3).toNat = em

theorem atEnc_ok {K : Nat} {s t : State} (hp : PreR K s) (hm : Mid s t) {em : List Byte}
    (hem : Spec.Rsa.bytesAt t.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .x3).toNat = em) :
    WP isa (.block encArgs) t (AtEnc s em) :=
  WP.mono (encArgs_ok hp hm) fun _ ⟨O, x8, x9, x10, x12, x11⟩ =>
    ⟨hm.only O, x8, x9, x10, x12, x11, by rw [O.mem, hem]⟩

/-- After `encode`: its result, and the buffers. -/
structure AfterEnc (s : State) (h : Spec.RsaPkcs1Sig.Hash) (em : List Byte) (w : State) : Prop where
  mid : Mid s w
  res : match encRes s h em with
    | none => w.gpr .x0 = 0
    | some em' => w.gpr .x0 = 1 ∧ Spec.Rsa.bytesAt w.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .x3).toNat = em ∧
      Spec.Rsa.bytesAt w.mem (fb s + BitVec.ofNat 64 oEM2) (s.gpr .x3).toNat = em' ∧
      Spec.Rsa.bytesAt w.mem (valA s) (s.gpr .x1).toNat = em.drop ((s.gpr .x3).toNat - h.len)

theorem enc_ok {K : Nat} {s u : State} (hp : PreR K s) {h : Spec.RsaPkcs1Sig.Hash}
    (hh : Spec.RsaPkcs1Sig.Hash.ofId ((s.gpr .x6).setWidth 32).toNat = some h) (hol : (s.gpr .x1).toNat = h.len)
    {em : List Byte} (hu : AtEnc s em u) : WP isa encode u (AfterEnc s h em) := by
  obtain ⟨hl0, hl1⟩ := hlen hp
  have hk1 := hp.k1; have hk2 := hp.k2
  have hval : Spec.Rsa.bytesAt u.mem (u.gpr .x11) (u.gpr .x12).toNat = em.drop ((s.gpr .x3).toNat - h.len) := by
    rw [hu.x11, hu.x12, val_bytes hl1 hu.em1, hol]
  have hpre : EPre u ((s.gpr .x6).setWidth 32) (s.gpr .x3).toNat := {
    x10 := by rw [hu.x10]; simp
    hk := by rw [hu.x9]
    kle := hk2
    buf := fun i hi => by
      rw [hu.mid.wr, hu.x8, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      exact in_frame _ _ (by unfold oEM2 frameBytes; omega)
    rd := fun j hj => by
      rw [hu.x11]; rw [hu.x12] at hj
      exact frame_bytes hu.mid.wr (by unfold oEM1 frameBytes; omega) j hj
    sep := fun j hj i hi => by
      rw [hu.x11, hu.x8]; rw [hu.x12] at hj
      exact ne_of_disjoint (Offset.disjoint _ (by unfold oEM1 oEM2; omega) (by unfold oEM1; omega)
        (by unfold oEM2; omega)) (by omega) (by omega) hj hi }
  refine WP.mono (encode_ok hpre) fun w ⟨hK, hout⟩ => ?_
  have henc : encodeId ((s.gpr .x6).setWidth 32) (em.drop ((s.gpr .x3).toNat - h.len)) (s.gpr .x3).toNat =
      encRes s h em := by
    unfold encodeId encRes; rw [hh]
  rw [hval, henc] at hout
  refine ⟨?_, ?_⟩
  · cases heo : encRes s h em with
    | none =>
      rw [heo] at hout
      exact hu.mid.only (Ver.Only.of_keep hK hout.2)
    | some em' =>
      rw [heo] at hout
      have hl' : em'.length = (s.gpr .x3).toNat := Proof.RsaPkcs1Sig.encode_length heo
      exact hu.mid.frame hK (R := ⟨fb s + BitVec.ofNat 64 oEM2, em'.length⟩) (by rw [hout.2, hu.x8]; exact frame_writeBytes _ _ _)
        (Offset.disjoint _ (by unfold oEM2; omega) (by decide) (by unfold oEM2; omega))
  · cases heo : encRes s h em with
    | none => rw [heo] at hout; exact hout.1
    | some em' =>
      rw [heo] at hout
      obtain ⟨h1, hme⟩ := hout
      have hl' : em'.length = (s.gpr .x3).toNat := Proof.RsaPkcs1Sig.encode_length heo
      have fw : Frame [⟨fb s + BitVec.ofNat 64 oEM2, em'.length⟩] u.mem w.mem := by
        rw [hme, hu.x8]; exact frame_writeBytes _ _ _
      have d1 : (⟨fb s + BitVec.ofNat 64 oEM1, (s.gpr .x3).toNat⟩ : Region).Disjoint
          ⟨fb s + BitVec.ofNat 64 oEM2, em'.length⟩ := by
        rw [hl']; exact Offset.disjoint _ (by unfold oEM1 oEM2; omega) (by unfold oEM1; omega) (by unfold oEM2; omega)
      have dv : (⟨valA s, (s.gpr .x1).toNat⟩ : Region).Disjoint ⟨fb s + BitVec.ofNat 64 oEM2, em'.length⟩ := by
        rw [hl']; exact Offset.disjoint _ (by unfold oEM1 oEM2; omega) (by unfold oEM1; omega) (by unfold oEM2; omega)
      refine ⟨h1, ?_, ?_, ?_⟩
      · rw [← hu.em1]
        exact bytes_apart (R := ⟨fb s + BitVec.ofNat 64 oEM1, (s.gpr .x3).toNat⟩) fw d1 (by dsimp only; omega)
      · rw [hme, hu.x8, ← hl', bytesAt_writeBytes _ _ _ (by omega)]
      · rw [← hol, ← val_bytes hl1 hu.em1]
        exact bytes_apart (R := ⟨valA s, (s.gpr .x1).toNat⟩) fw dv (by dsimp only; omega)

/-- Before `compare`. -/
structure AtCmp (s : State) (h : Spec.RsaPkcs1Sig.Hash) (em em' : List Byte) (v : State) : Prop where
  mid : Mid s v
  x14 : v.gpr .x14 = fb s + BitVec.ofNat 64 oEM1
  x15 : v.gpr .x15 = fb s + BitVec.ofNat 64 oEM2
  x13 : v.gpr .x13 = BitVec.ofNat 64 (s.gpr .x3).toNat
  b1 : Spec.Rsa.bytesAt v.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .x3).toNat = em
  b2 : Spec.Rsa.bytesAt v.mem (fb s + BitVec.ofNat 64 oEM2) (s.gpr .x3).toNat = em'
  val : Spec.Rsa.bytesAt v.mem (valA s) (s.gpr .x1).toNat = em.drop ((s.gpr .x3).toNat - h.len)

theorem cmpArgs_ok {s w : State} {h : Spec.RsaPkcs1Sig.Hash} {em em' : List Byte} (hm : Mid s w)
    (b1 : Spec.Rsa.bytesAt w.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .x3).toNat = em)
    (b2 : Spec.Rsa.bytesAt w.mem (fb s + BitVec.ofNat 64 oEM2) (s.gpr .x3).toNat = em')
    (hv : Spec.Rsa.bytesAt w.mem (valA s) (s.gpr .x1).toNat = em.drop ((s.gpr .x3).toNat - h.len)) :
    WP isa (.block cmpArgs) w (AtCmp s h em em') := by
  unfold cmpArgs
  refine wp_addSp (by decide) fun v₁ p₁ f₁ => wp_addSp (by decide) fun v₂ p₂ f₂ =>
    wp_mov fun v₃ p₃ f₃ => wp_nil ?_
  have P₃ : Only [.x14, .x15, .x13] w v₃ := (p₁.trans (p₂.trans p₃)).mono
  refine ⟨hm.only P₃, ?_, ?_, ?_, by rw [P₃.mem, b1], by rw [P₃.mem, b2], by rw [P₃.mem, hv]⟩
  · rw [p₃.get .x14, p₂.get .x14, f₁, hm.sp]
  · rw [p₃.get .x15, f₂, p₁.sp, hm.sp]
  · rw [f₃, p₂.get .x21, p₁.get .x21, hm.x21, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- After `compare`: its result, and the hash value in `EM₁`. -/
structure AfterCmp (s : State) (h : Spec.RsaPkcs1Sig.Hash) (em em' : List Byte) (y : State) : Prop where
  mid : Mid s y
  hiff : y.gpr .x12 = 0 ↔ em = em'
  val : Spec.Rsa.bytesAt y.mem (valA s) (s.gpr .x1).toNat = em.drop ((s.gpr .x3).toNat - h.len)

theorem cmp_ok {K : Nat} {s v : State} (hp : PreR K s) {h : Spec.RsaPkcs1Sig.Hash} {em em' : List Byte}
    (hv : AtCmp s h em em' v) : WP isa compare v (AfterCmp s h em em') := by
  have hk1 := hp.k1; have hk2 := hp.k2
  refine WP.mono (compare_ok (s := v) (n := (s.gpr .x3).toNat) (by omega) (by omega) hv.x13
    (fun j hj => by rw [hv.x14]; exact frame_bytes hv.mid.wr (by unfold oEM1 frameBytes; omega) j hj)
    (fun j hj => by rw [hv.x15]; exact frame_bytes hv.mid.wr (by unfold oEM2 frameBytes; omega) j hj))
    fun y ⟨oy, hiff, _⟩ => ⟨hv.mid.only oy, ?_, by rw [oy.mem, hv.val]⟩
  rw [hv.x14, hv.x15, hv.b1, hv.b2] at hiff
  exact hiff

theorem release_ok {K : Nat} {s y : State} (hp : PreR K s) {h : Spec.RsaPkcs1Sig.Hash} {em em' : List Byte}
    (hy : AfterCmp s h em em' y) :
    WP isa release y fun w => Mid s w ∧ Spec.Rsa.written w.mem (s.gpr .x0) (s.gpr .x1).toNat
      ((w.gpr .x0).setWidth 32) (if some em' = some em then some (em.drop ((s.gpr .x3).toNat - h.len)) else none) := by
  unfold release
  by_cases he : em = em'
  · refine WP.ite false (by rw [eval_nonzero]; simp [hy.hiff.mpr he]) (by simp) fun _ => ?_
    refine WP.mono (copyOut_ok hp hy.mid) fun w' ⟨m', hw'⟩ => ⟨m', ?_⟩
    rw [hy.val] at hw'
    simpa [he] using hw'
  · have hne : y.gpr .x12 ≠ 0 := fun h' => he (hy.hiff.mp h')
    refine WP.ite true (by rw [eval_nonzero]; simp; exact hne) (fun _ => ?_) (by simp)
    refine WP.mono (zeroKept_ok hp hy.mid) fun w' hw => ⟨hw.1, ?_⟩
    have : ¬ some em' = some em := fun h' => he (Option.some.inj h').symm
    simpa [this] using hw.2

theorem tail_ok {K : Nat} {s w : State} (hp : PreR K s) {h : Spec.RsaPkcs1Sig.Hash} {em : List Byte}
    (hw : AfterEnc s h em w) :
    WP isa tail w fun w' => Mid s w' ∧ Spec.Rsa.written w'.mem (s.gpr .x0) (s.gpr .x1).toNat
      ((w'.gpr .x0).setWidth 32)
      (if encRes s h em = some em then some (em.drop ((s.gpr .x3).toNat - h.len)) else none) := by
  have hres := hw.res
  unfold tail
  cases heo : encRes s h em with
  | none =>
    rw [heo] at hres
    refine WP.ite true ((eval_zero' w .x0).trans (by rw [hres]; rfl)) (fun _ => ?_) (by simp)
    refine WP.mono (zeroKept_ok hp hw.mid) fun w' hw' => ⟨hw'.1, ?_⟩
    simpa using hw'.2
  | some em' =>
    rw [heo] at hres
    obtain ⟨h1, b1, b2, hv⟩ := hres
    refine WP.ite false ((eval_zero' w .x0).trans (by rw [h1]; rfl)) (by simp) fun _ => ?_
    exact WP.seq (WP.mono (cmpArgs_ok hw.mid b1 b2 hv) fun v hv' =>
      WP.seq (WP.mono (cmp_ok hp hv') fun y hy => release_ok hp hy))

theorem afterPub_ok {K : Nat} {s t : State} (hp : PreR K s) {h : Spec.RsaPkcs1Sig.Hash}
    (hh : Spec.RsaPkcs1Sig.Hash.ofId ((s.gpr .x6).setWidth 32).toNat = some h) (hol : (s.gpr .x1).toNat = h.len)
    (ha : AfterCall s t) :
    WP isa afterPub t fun w => Mid s w ∧
      Spec.Rsa.written w.mem (s.gpr .x0) (s.gpr .x1).toNat ((w.gpr .x0).setWidth 32) (recOut s h) := by
  have hres := ha.res
  unfold afterPub recOut
  cases hpo : pubOut s with
  | none =>
    rw [hpo] at hres
    refine WP.ite true (by simp [eval, State.read, hres.1]) (fun _ => ?_) (by simp)
    exact zeroKept_ok hp ha.toMid
  | some em =>
    rw [hpo] at hres
    obtain ⟨hr, hem⟩ := hres
    dsimp only
    refine WP.ite false (by simp [eval, State.read, hr]) (by simp) fun _ => ?_
    exact WP.seq (WP.mono (atEnc_ok hp ha.toMid hem) fun u hu =>
      WP.seq (WP.mono (enc_ok hp hh hol hu) fun w hw => tail_ok hp hw))

/-! ## The restores, and the whole function -/

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
    · have hr'' : r ∈ [Reg.x23, .x24, .x25, .x26, .x27, .x28] := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr'
        rcases hr' with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> first | decide | simp_all [saved]
      have h16 : r ∉ [Reg.x16] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'' ⊢
        rcases hr'' with h | h | h | h | h | h <;> subst h <;> decide
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

/-- What `vg_rsa_pkcs1_recover` returns and writes, and the calling
convention. -/
def Post (s s' : State) : Prop :=
  abiPreserved s s' ∧ ∀ h, Spec.RsaPkcs1Sig.Hash.ofId ((s.gpr .x6).setWidth 32).toNat = some h →
    Spec.Rsa.written s'.mem (s.gpr .x0) (s.gpr .x1).toNat ((s'.gpr .x0).setWidth 32)
      (Spec.RsaPkcs1Sig.recover (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat) h
        (Spec.Rsa.bytesAt s.mem (s.gpr .x7) (stackArg s 0).toNat))

theorem recover_eq {s : State} (h : Spec.RsaPkcs1Sig.Hash) (hsig : stackArg s 0 = s.gpr .x3) :
    Spec.RsaPkcs1Sig.recover (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat) h
      (Spec.Rsa.bytesAt s.mem (s.gpr .x7) (stackArg s 0).toNat) = recOut s h := by
  rw [recover_eq_recoverEnc, recoverEnc, bytesAt_length, bytesAt_length, hsig, ite_eq_left rfl]
  rfl

theorem recover_none {s : State} (h : Spec.RsaPkcs1Sig.Hash) (hsig : stackArg s 0 ≠ s.gpr .x3) :
    Spec.RsaPkcs1Sig.recover (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat) h
      (Spec.Rsa.bytesAt s.mem (s.gpr .x7) (stackArg s 0).toNat) = none := by
  rw [recover_eq_recoverEnc, recoverEnc, bytesAt_length, bytesAt_length,
    ite_eq_right fun e => hsig (BitVec.eq_of_toNat_eq e)]

theorem lenCheck_ok {K : Nat} {s : State} (hp : PreR K s) :
    WP isa (.block lenCheck) s fun t₁ => Only [.x8] s t₁ ∧ t₁.gpr .x8 = stackArg s 0 - s.gpr .x3 := by
  refine VG.Proof.RsaPkcs1Sig.AArch64.wp_ldrSp (by decide) ?_ fun t₀ o₀ e₀ =>
    wp_sub fun t₁ o₁ e₁ => wp_nil ⟨(o₀.trans o₁).mono, ?_⟩
  · have h := arg_in (s := s) (j := 0) (rs := s.rd ++ s.wr) hp (Covers.left (Covers.refl _)) (by decide)
    simpa [stackArgAddr] using h
  · rw [e₁, e₀, o₀.get .x3, BitVec.add_zero, ← VG.Proof.RsaPkcs1Sig.AArch64.sa0 s]; rfl

theorem eval_len {s t : State} (e : t.gpr .x8 = stackArg s 0 - s.gpr .x3) :
    isa.eval (.nonzero .x .x8) t = some (decide (stackArg s 0 ≠ s.gpr .x3)) := by
  rw [eval_nonzero, e, ne_zero_iff, BitVec.toNat_sub]
  have := (stackArg s 0).isLt; have := (s.gpr .x3).isLt
  refine congrArg some (decide_eq_decide.mpr ⟨fun h e => ?_, fun h e => h ?_⟩)
  · rw [e] at h; omega
  · apply BitVec.eq_of_toNat_eq; omega

/-- Zeros to `out`, from the entry state but for `x8`. -/
theorem zeroArgs_ok {K : Nat} {s t : State} (hp : PreR K s) (o : Only [.x8] s t) :
    WP isa zeroArgs t fun w => Keep [.x8, .x14, .x13, .x15, .x13, .x14, .x0] s w ∧
      Spec.Rsa.written w.mem (s.gpr .x0) (s.gpr .x1).toNat ((w.gpr .x0).setWidth 32) none := by
  obtain ⟨hl0, hl1⟩ := hlen hp
  have := hp.k2
  unfold zeroArgs
  refine WP.seq (wp_mov fun u₁ o₁ e₁ => wp_mov fun u₂ o₂ e₂ => wp_nil ?_)
  have O₂ : Only [.x8, .x14, .x13] s u₂ := (o.trans (o₁.trans o₂)).mono
  refine WP.mono (zeroOut_ok (p := s.gpr .x0) (n := (s.gpr .x1).toNat) hl0 (by omega)
    (by rw [o₂.get .x14, e₁, o.get .x0]) (by rw [e₂, o₁.get .x1, o.get .x1, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (by rw [O₂.wr]; exact out_wr hp [])) fun w ⟨k, mw, x0⟩ => ⟨(O₂.keep.trans k).mono, by rw [x0]; rfl, ?_⟩
  rw [mw, O₂.mem]
  have := bytesAt_writeBytes s.mem (s.gpr .x0) (List.replicate (s.gpr .x1).toNat 0) (by simp; omega)
  rwa [List.length_replicate] at this

theorem code_ok (c : PubChecked) {s : State} (hp : PreR c.stack s) :
    WP isa (code c.name c.code) s (Post s) := by
  obtain ⟨h, hh, hol⟩ := hp.hh
  have hof : ∀ h', Spec.RsaPkcs1Sig.Hash.ofId ((s.gpr .x6).setWidth 32).toNat = some h' → h' = h :=
    fun h' e => Option.some.inj (e.symm.trans hh)
  unfold code
  refine WP.seq (WP.mono (lenCheck_ok hp) fun t₁ ⟨o₁, e₁⟩ => ?_)
  have hne := eval_len e₁
  by_cases hsig : stackArg s 0 = s.gpr .x3
  · refine WP.ite false (by rw [hne]; simp [hsig]) (by simp) fun _ => ?_
    refine WP.alloc (by decide) (by rw [o₁.sp]; have := hp.sp1; unfold stk at this; omega) ?_
    unfold body
    refine WP.seq (WP.mono (pubArgs_ok hp (by simp [allocated, o₁.sp]) (by simp [allocated, o₁.rd])
      (by simp [allocated, o₁.sp, o₁.wr]) (by simp [allocated, o₁.mem]) (fun r hr => by
        simp only [allocated]; exact o₁.gpr r (by simpa using hr)) (fun r hr => o₁.vcs r hr))
      fun t₂ h₂ => ?_)
    refine WP.seq (WP.mono (call_ok c hp h₂ hsig) fun t₃ h₃ => ?_)
    refine WP.seq (WP.mono (afterPub_ok hp hh hol h₃) fun t₄ ⟨m₄, r₄⟩ => ?_)
    refine WP.mono (restore_ok m₄) fun w ⟨habi, hx0, hmem⟩ => ⟨habi, fun h' e => ?_⟩
    rw [hof h' e, recover_eq h hsig, hx0, hmem]; exact r₄
  · refine WP.ite true (by rw [hne]; simp [hsig]) (fun _ => WP.mono (zeroArgs_ok hp o₁) fun w ⟨o, r⟩ =>
      ⟨⟨fun r hr => ?_, ?_, fun r hr => ?_⟩, fun h' _ => ?_⟩) (by simp)
    · have h8 : r ∉ [Reg.x8, .x14, .x13, .x15, .x13, .x14, .x0] := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide
      exact o.gpr r h8
    · rw [o.sp]
    · rw [o.vcs r hr]
    · rw [recover_none h' hsig]; exact r

end VG.Proof.RsaPkcs1Sig.AArch64.Rec
