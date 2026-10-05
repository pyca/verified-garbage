import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecValid

/-!
# RSAES-PKCS1-v1_5 decryption on x86-64: the output

`*msg_len` and each byte of `out` selected without branches, reading both
`EM` and `AM` (`selLoop_ok`), and the result (`selPart_step`).
-/

namespace VG.Proof.RsaPkcs1Enc.X86_64.Dec

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Decrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Enc.X86_64

/-- Byte `i` of the output. -/
def outByte (v ok : Bool) (kl i : Nat) (e a : Byte) : Byte :=
  if kl ≤ i ∧ ok = true then (if v then e else a) else 0

theorem selBody_run {t : State} {p q : Addr} {i k kl : Nat} {v ok : Bool} {e a : Byte} (hi : i < k)
    (hk : k < 2 ^ 32) (hkl : kl ≤ k) (hdi : t.gpr .rdi = p) (hsi : t.gpr .rsi = q)
    (hcx : t.gpr .rcx = BitVec.ofNat 64 i) (hdx : t.gpr .rdx = BitVec.ofNat 64 kl) (h9 : t.gpr .r9 = BitVec.ofNat 64 k)
    (h10 : t.gpr .r10 = bmask v) (h11 : t.gpr .r11 = bmask ok) (he : t.mem (off p i) = e) (ha : t.mem (off q i) = a)
    (hie : InRegions (t.rd ++ t.wr) (off p i) 1) (hia : InRegions (t.rd ++ t.wr) (off q i) 1)
    (hw : InRegions t.wr (off p i) 1) :
    WP isa (.block selBody) t fun t' => t'.mem = t.mem.writeW (off p i) (outByte v ok kl i e a) ∧
      t'.gpr .rcx = BitVec.ofNat 64 (i + 1) ∧ t'.zf = some (decide (i + 1 = k)) ∧ Keep [.rax, .r8, .rcx] t t' := by
  refine WP.keep [.rax, .r8, .rcx] (c := .block selBody) (Q := fun t' =>
    t'.mem = t.mem.writeW (off p i) (outByte v ok kl i e a) ∧ t'.gpr .rcx = BitVec.ofNat 64 (i + 1) ∧
      t'.zf = some (decide (i + 1 = k))) ?_ rfl |>.mono fun t' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩
  have e1 : 0 + i = i := Nat.zero_add _
  xrun [selBody, ea_bxd (p := p) (j := i), ea_bxd (p := q) (j := i), hdi, hsi, hcx, e1, hie, hia, hw, he, ha,
    hdx, h9, h10, h11, borrow_mask, bmask_not, bmask_and, ofNat_add_one,
    ofNat_sub_beq (show i + 1 < 2 ^ 64 by omega) (show k < 2 ^ 64 by omega), sel_xor]
  congr 1
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show kl < 2 ^ 64 by omega)]
  unfold outByte
  have and255 : ∀ x : Byte, x &&& 255#8 = x := fun x => by
    rw [show (255#8) = BitVec.allOnes 8 from rfl, BitVec.and_allOnes]
  by_cases h : kl ≤ i
  · cases ok <;> cases v <;> simp [h, Nat.not_lt.mpr h, bmask, and255, BitVec.xor_assoc]
  · cases ok <;> cases v <;> simp [h, Nat.lt_of_not_le h, bmask]


theorem selLoop_ok {t₀ : State} {p q : Addr} {k kl : Nat} {v ok : Bool} (hk0 : 0 < k) (hk : k < 2 ^ 32)
    (hkl : kl ≤ k) (hdi : t₀.gpr .rdi = p) (hsi : t₀.gpr .rsi = q) (hcx : t₀.gpr .rcx = BitVec.ofNat 64 0)
    (hdx : t₀.gpr .rdx = BitVec.ofNat 64 kl) (h9 : t₀.gpr .r9 = BitVec.ofNat 64 k) (h10 : t₀.gpr .r10 = bmask v)
    (h11 : t₀.gpr .r11 = bmask ok) (hie : ∀ i < k, InRegions (t₀.rd ++ t₀.wr) (off p i) 1)
    (hia : ∀ i < k, InRegions (t₀.rd ++ t₀.wr) (off q i) 1) (hw : ∀ i < k, InRegions t₀.wr (off p i) 1)
    (hpq : ∀ i < k, k ≤ ofs p (off q i)) :
    WP isa selLoop t₀ fun t => Keep [.rax, .r8, .rcx] t₀ t ∧ Outside p 0 k t₀.mem t.mem ∧
      ∀ i < k, byte t.mem p i = outByte v ok kl i (t₀.mem (off p i)) (t₀.mem (off q i)) := by
  refine wp_upto (a := 0) (N := k) hk0 (fun j u => Keep [.rax, .r8, .rcx] t₀ u ∧ Outside p 0 j t₀.mem u.mem ∧
      (∀ i < j, byte u.mem p i = outByte v ok kl i (t₀.mem (off p i)) (t₀.mem (off q i))) ∧
      u.gpr .rcx = BitVec.ofNat 64 j) (fun j _ hj u ⟨ku, ho, hb, hcxu⟩ => ?_)
    (fun _ ⟨k, ho, hb, _⟩ => ⟨k, ho, hb⟩) ⟨Keep.refl _ _, Outside.refl _ _ _ _, fun _ h => absurd h (by omega), hcx⟩
  have g : ∀ r, r ∉ [Reg.rax, .r8, .rcx] → u.gpr r = t₀.gpr r := fun r hr => ku.gpr hr
  have he : u.mem (off p j) = t₀.mem (off p j) := ho _ (.inr (by rw [ofs_off0 _ (by omega)]; omega))
  have ha : u.mem (off q j) = t₀.mem (off q j) := ho _ (.inr (by have := hpq j hj; omega))
  refine WP.mono (selBody_run hj hk hkl ((g .rdi (by decide)).trans hdi) ((g .rsi (by decide)).trans hsi) hcxu
    ((g .rdx (by decide)).trans hdx) ((g .r9 (by decide)).trans h9) ((g .r10 (by decide)).trans h10)
    ((g .r11 (by decide)).trans h11) he ha (by rw [ku.2.1, ku.2.2]; exact hie j hj)
    (by rw [ku.2.1, ku.2.2]; exact hia j hj) (by rw [ku.2.2]; exact hw j hj))
    fun u' ⟨hm, hcx', hz, k'⟩ => ⟨hz, (ku.trans k').mono (by decide), ?_, ?_, hcx'⟩
  · rw [hm]; exact Outside.wb (Outside.mono ho (by omega) (by omega)) _ (by omega) (by omega) (by omega)
  · intro i hi
    rw [hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [byte_wb _ _ _ (by omega) (by omega) (by omega)]; exact hb i hi
    · rw [show off p i = off p (0 + i) by rw [Nat.zero_add]]
      have := byte_wb_self u.mem p i (outByte v ok kl i (t₀.mem (off p i)) (t₀.mem (off q i)))
      simpa using this


/-- The selected length, as a number. -/
abbrev lselOf (v : Bool) (sep al k : Nat) : Nat := if v then k - sep - 1 else al

theorem lenOf_eq (v : Bool) (sep al k : Nat) : lenOf v sep al k = BitVec.ofNat 64 (lselOf v sep al k) := by
  cases v <;> rfl

/-- At the end. -/
structure Fin (s : State) (R : BitVec 64) (EM AM : List Byte) (v ok : Bool) (L : Nat) (t : State) : Prop where
  rsp : t.gpr .rsp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  mem : Frame (wrs s) s.mem t.mem
  rax : t.gpr .rax = R
  out : ∀ i < kOf s, t.mem (off (s.gpr .rdi) i) = outByte v ok (kOf s - L) i (EM.getD i 1) (AM.getD i 0)
  ml : t.mem.readW (s.gpr .rdx) 64 = BitVec.ofNat 64 L &&& bmask ok
  cs : ∀ r ∈ calleeSaved, r ≠ .rsp → t.gpr r = s.gpr r
  amLen : AM.length = kOf s


/-- The alternative message. -/
abbrev amOf (s : State) : List Byte := Spec.RsaPkcs1Enc.irprf (kdkOf s) (Spec.RsaPkcs1Enc.ascii "message") (kOf s)

/-- The validity of `EM`'s padding, as the scan finds it. -/
abbrev vEM (EM : List Byte) (k : Nat) : Bool :=
  vOf (EM.getD 0 1) (EM.getD 1 1) (firstZero EM k).isSome ((firstZero EM k).getD 0)

/-- The selected length. -/
abbrev lEM (s : State) (EM : List Byte) : Nat :=
  lselOf (vEM EM (kOf s)) ((firstZero EM (kOf s)).getD 0) (Spec.RsaPkcs1Enc.altLength (kOf s) (clOf s)) (kOf s)

theorem selPart_step {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (h : SC s R EM t) :
    WP isa selPart t (Fin s R EM (amOf s) (vEM EM (kOf s)) (okOf R) (lEM s EM)) := by
  have hk1 := hp.k1
  have hk2 := hp.k2
  have hkk : kOf s ≤ 1024 := hk2
  have hkk1 : 64 ≤ kOf s := hk1
  have hc := h.ctx
  have hs := hc.frm hp
  have hsc := hc.scr hp
  have hsep : (firstZero EM (kOf s)).getD 0 < kOf s := by
    cases hf : firstZero EM (kOf s) with
    | none => simp; omega
    | some i => have := firstZero_some hf; simpa using this.2.1
  have hal := altFold_le (kOf s) (clOf s) 128
  rw [← altLength_eq] at hal
  have hL : lEM s EM ≤ kOf s := by
    simp only [lEM, lselOf]; split <;> omega
  -- the checks
  have hR : t.mem.readW (fb s + BitVec.ofNat 64 oR) 64 = R := hc.sR
  have hio : ∀ i n, i + n ≤ kOf s → InRegions (t.rd ++ t.wr) (off (s.gpr .rdi) i) n := fun i n h' =>
    let ⟨r, hr, hcr⟩ := hc.outIn hp h'; ⟨r, List.mem_append_right _ hr, hcr⟩
  refine WP.seq (WP.mono (validBlock_run (p := s.gpr .rdi) (F := fb s) (b0 := EM.getD 0 1) (b1 := EM.getD 1 1)
    h.rdi (by rw [← hc.em (i := 0) (by omega)]; exact (congrArg t.mem (off_zero _)).symm)
    (hc.em (by omega)) (by have := hio 0 1 (by omega); rwa [off_zero] at this) (hio 1 1 (by omega)) h.rdx h.r10 h.r11
    h.r9 hc.rsp hR (hs.ld (d := oR) (by decide)) hsep (by omega))
    fun t₁ ⟨⟨hm₁, h10₁, hdx₁, h11₁, hsi₁⟩, k₁⟩ => ?_)
  have hc₁ : Ctx s R EM t₁ := hc.regs hp hm₁ k₁ (by decide)
  have hs₁ := hc₁.frm hp
  rw [lenOf_eq] at hdx₁ hsi₁
  -- the pointers
  refine WP.seq (WP.mono (WP.keep [.r8, .rcx] (c := .block outPtrs) (Q := fun t' => t'.mem = t₁.mem ∧
      t'.gpr .r8 = s.gpr .rdx ∧ t'.gpr .rcx = scA s sAM) (by
    xrun [outPtrs, scr, List.cons_append, List.nil_append, ea_sp, hc₁.rsp, hs₁.ld (d := oML) (by decide),
      hs₁.ld (d := oScr) (by decide), hc₁.slots.sML, hc₁.slots.sScr, sx (d := sAM) (by decide)]) rfl)
    fun t₂ ⟨⟨hm₂, h8₂, hcx₂⟩, k₂⟩ => ?_)
  have hml : InRegions t₂.wr (s.gpr .rdx) 8 :=
    ⟨mlR s, by rw [k₂.2.2, k₁.2.2, hc.wr, hp.hwr]; simp [mlR], Region.contains_self _ _⟩
  have hdx₂ : t₂.gpr .rdx = BitVec.ofNat 64 (lEM s EM) &&& bmask (okOf R) := (k₂.gpr (by decide)).trans hdx₁
  have hsi₂ : t₂.gpr .rsi = BitVec.ofNat 64 (kOf s) - BitVec.ofNat 64 (lEM s EM) := (k₂.gpr (by decide)).trans hsi₁
  refine WP.seq (WP.mono (WP.keep [.rdx, .rsi, .rcx] (c := .block outInit) (Q := fun t' =>
      t'.mem = t₂.mem.writeW (s.gpr .rdx) (BitVec.ofNat 64 (lEM s EM) &&& bmask (okOf R)) ∧
      t'.gpr .rdx = BitVec.ofNat 64 (kOf s - lEM s EM) ∧ t'.gpr .rsi = scA s sAM ∧
      t'.gpr .rcx = BitVec.ofNat 64 0) (by
    have e : BitVec.ofNat 64 (kOf s) - BitVec.ofNat 64 (lEM s EM) = BitVec.ofNat 64 (kOf s - lEM s EM) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    xrun [outInit, ea_atd (p := s.gpr .rdx), h8₂, hml, hdx₂, hsi₂, hcx₂, e]) rfl)
    fun t₃ ⟨⟨hm₃, hdx₃, hsi₃, hcx₃⟩, k₃⟩ => ?_)
  have hsi' := hp.hsi
  have hwO := hp.wO
  have hwM := hp.wM
  have dOM : (⟨s.gpr .rdi, kOf s⟩ : Region).Disjoint ⟨s.gpr .rdx, 8⟩ := by have := hp.dOm; rwa [hsi'] at this
  have dOS : (⟨s.gpr .rdi, kOf s⟩ : Region).Disjoint (scrR s) := by have := hp.dOs; rwa [hsi'] at this
  have dKO : (stkR s).Disjoint ⟨s.gpr .rdi, kOf s⟩ := by have := hp.dKo; rwa [hsi'] at this
  obtain ⟨hS1, _⟩ := scr_len hp
  have dAM : ∀ {n : Nat}, sAM + n ≤ scrBytes → Region.Sub ⟨scA s sAM, n⟩ (scrR s) := fun h =>
    sub_trans (scSub h) (Region.sub_prefix hS1)
  have hmt : t₂.mem = t.mem := hm₂.trans hm₁
  have hfw₃ : Frame [⟨s.gpr .rdx, 8⟩] t.mem t₃.mem := by
    rw [hm₃, hmt]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have he₃ : ∀ i < kOf s, t₃.mem (off (s.gpr .rdi) i) = EM.getD i 1 := fun i hi => by
    rw [← hc.em hi]
    exact hfw₃.bytes (R := ⟨s.gpr .rdi, kOf s⟩) (fun r hr => by rw [List.mem_singleton.mp hr]; exact dOM)
      (show kOf s ≤ 2 ^ 64 by omega) hi
  have hAM := h.am
  have ha₃ : ∀ i < kOf s, t₃.mem (off (scA s sAM) i) = (amOf s).getD i 0 := fun i hi => by
    show _ = (Spec.RsaPkcs1Enc.irprf (kdkOf s) (Spec.RsaPkcs1Enc.ascii "message") (kOf s)).getD i 0
    rw [← hAM, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [blen]; exact hi), Option.getD_some, bget]
    exact hfw₃.bytes (R := ⟨scA s sAM, kOf s⟩) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact (hp.dMs.sub_right (dAM (by unfold sAM scrBytes; omega))).symm)
      (show kOf s ≤ 2 ^ 64 by omega) hi
  have kk : Keep ([.rax, .rsi, .rdx, .r10, .r11] ++ [.r8, .rcx] ++ [.rdx, .rsi, .rcx]) t t₃ := (k₁.trans k₂).trans k₃
  have g : ∀ r, r ∉ [Reg.rax, .rsi, .rdx, .r10, .r11, .r8, .rcx] → t₃.gpr r = t.gpr r := fun r hr =>
    have hr' : r ∉ [Reg.rax, .rsi, .rdx, .r10, .r11] ++ [.r8, .rcx] ++ [.rdx, .rsi, .rcx] := by
      intro h; apply hr
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with ((h | h | h | h | h) | (h | h)) | (h | h | h) <;> subst h <;> simp
    kk.gpr hr'
  have hrw : t₃.rd ++ t₃.wr = t.rd ++ t.wr := by rw [kk.2.1, kk.2.2]
  refine WP.seq (WP.mono (selLoop_ok (p := s.gpr .rdi) (q := scA s sAM) (k := kOf s) (kl := kOf s - lEM s EM)
    (v := vEM EM (kOf s)) (ok := okOf R) (by omega) (by omega) (by omega) ((g .rdi (by decide)).trans h.rdi)
    hsi₃ hcx₃ hdx₃ ((g .r9 (by decide)).trans h.r9)
    ((k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h10₁))
    ((k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h11₁))
    (fun i hi => by rw [hrw]; exact hio i 1 (by omega))
    (fun i hi => by
      rw [hrw]
      obtain ⟨r, hr, hcr⟩ := hsc.region (d := sAM + i) (n := 1) (by unfold sAM scrBytes; omega) (by decide)
      exact ⟨r, List.mem_append_right _ hr, by rw [scA, off_off]; exact hcr⟩)
    (fun i hi => by rw [kk.2.2]; exact hc.outIn hp (i := i) (n := 1) (by omega))
    (fun i hi => ofs_of_disjoint (dOS.sub_right (dAM (by unfold sAM scrBytes; omega))) hi (by omega)))
    fun t₄ ⟨k₄, ho₄, hb₄⟩ => ?_)
  have hfo₄ : Frame [⟨s.gpr .rdi, kOf s⟩] t₃.mem t₄.mem := by
    have := frame_of_out ho₄ (by omega); rwa [off_zero] at this
  have hR₄ : word t₄.mem (fb s) oR = R := by
    rw [← hc.sR]
    refine (hfo₄.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)).trans
      (hfw₃.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide))
    · rw [List.mem_singleton.mp hr]; exact (dKO.sub_left (frame_sub s (by decide)))
    · rw [List.mem_singleton.mp hr]; exact (hp.dKm.sub_left (frame_sub s (by decide)))
  have hsp₄ : t₄.gpr .rsp = fb s := (k₄.gpr (by decide)).trans ((g .rsp (by decide)).trans hc.rsp)
  have hs₄ : Scr t₄ (fb s) frameBytes := Scr.of_mem (by rw [k₄.2.2, kk.2.2, hc.wr]; exact List.mem_cons_self ..)
    (by have := (fb_toNat hp).1; omega)
  refine WP.mono (WP.keep [.rax] (c := .block [.mov .rax (.mem (sp oR))]) (Q := fun t' => t'.mem = t₄.mem ∧
    t'.gpr .rax = R) (by xrun [ea_sp, hsp₄, hs₄.ld (d := oR) (by decide), hR₄]) rfl) fun t₅ ⟨⟨hm₅, hax₅⟩, k₅⟩ => ?_
  have k' := (kk.trans k₄).trans k₅
  refine ⟨(k₅.gpr (by decide)).trans hsp₄, k'.2.1.trans hc.rd, k'.2.2.trans hc.wr, ?_, hax₅, fun i hi => ?_, ?_,
    fun r hr hr' => (k'.cs (by decide) r hr).trans (hc.cs r hr hr'), by show (Spec.RsaPkcs1Enc.irprf _ _ _).length = _; rw [← hAM, blen]⟩
  · rw [hm₅]
    refine frame_call (frame_call hc.mem hfw₃ fun r hr => ?_) hfo₄ fun r hr => ?_
    · rw [List.mem_singleton.mp hr]; exact ⟨mlR s, by simp, fun _ h => h⟩
    · rw [List.mem_singleton.mp hr]; exact ⟨outR s, by simp, by simp only [outR]; rw [hsi']; exact fun _ h => h⟩
  · rw [hm₅]
    have := hb₄ i hi
    simp only [byte] at this
    rw [this, he₃ i hi, ha₃ i hi]
  · rw [hm₅, hfo₄.readW (Region.contains_self _ _) (fun r hr => by rw [List.mem_singleton.mp hr]; exact dOM.symm)
      (by decide), hm₃, Mem.readW_writeW_self64]

end VG.Proof.RsaPkcs1Enc.X86_64.Dec
