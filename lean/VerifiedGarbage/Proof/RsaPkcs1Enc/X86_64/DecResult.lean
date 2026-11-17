module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecScan
import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-! ### `RsaPkcs1Enc.X86_64.DecSel`, which this module and modules that import it used -/

section

/-! ### `RsaPkcs1Enc.X86_64.DecValid`, which only this module used -/

section

/-!
# RSAES-PKCS1-v1_5 decryption on x86-64: the checks of the padding

The validity mask, the selected length and the mask of the private-key
operation's success, from the scan, without branches (`validBlock_run`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86_64.Dec

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Decrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Enc.X86_64

theorem zero_test (b : Byte) : decide ((BitVec.setWidth 64 b).toNat < BitVec.toNat (1 : BitVec 64)) =
    decide (b = 0) := by
  rw [zext_toNat, one64_toNat]
  exact decide_eq_decide.mpr ⟨fun h => BitVec.eq_of_toNat_eq (by simp; omega_using [h]), fun h => by simp [h]⟩

theorem two_test (b : Byte) : decide ((BitVec.setWidth 64 b ^^^ 2).toNat < BitVec.toNat (1 : BitVec 64)) =
    decide (b = 2) := by
  rw [one64_toNat]
  refine decide_eq_decide.mpr ⟨fun h => ?_, fun h => by subst h; decide⟩
  obtain h0 : BitVec.setWidth 64 b ^^^ 2 = 0 := BitVec.eq_of_toNat_eq (by rw [show (0 : BitVec 64).toNat = 0 from rfl]; omega_using [h])
  have : BitVec.setWidth 64 b = 2 := by
    have := congrArg (· ^^^ (2 : BitVec 64)) h0
    simpa [BitVec.xor_assoc] using this
  have := congrArg (BitVec.setWidth 8) this
  rwa [trunc_zext] at this

theorem ten_test {sep : Nat} (h : sep < 2 ^ 64) :
    decide ((BitVec.ofNat 64 sep).toNat < (BitVec.signExtend 64 (10 : BitVec 32)).toNat) = decide (sep < 10) := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, show (BitVec.signExtend 64 (10 : BitVec 32)).toNat = 10 from rfl]

theorem ok_test (R : BitVec 64) :
    decide ((BitVec.setWidth 64 (BitVec.setWidth 32 R) ^^^ 1).toNat < BitVec.toNat (1 : BitVec 64)) = decide (R.setWidth 32 = 1) := by
  rw [one64_toNat]
  refine decide_eq_decide.mpr ⟨fun h => ?_, fun h => by rw [h]; decide⟩
  obtain h0 : BitVec.setWidth 64 (BitVec.setWidth 32 R) ^^^ 1 = 0 :=
    BitVec.eq_of_toNat_eq (by rw [show (0 : BitVec 64).toNat = 0 from rfl]; omega_using [h])
  have : BitVec.setWidth 64 (BitVec.setWidth 32 R) = 1 := by
    have := congrArg (· ^^^ (1 : BitVec 64)) h0
    simpa [BitVec.xor_assoc] using this
  have := congrArg (BitVec.setWidth 32) this
  rwa [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq] at this

theorem bmask_not (a : Bool) : bmask a ^^^ BitVec.signExtend 64 (BitVec.ofInt 32 (-1)) = bmask (!a) := by
  cases a <;> decide

theorem bmask_and (a b : Bool) : bmask a &&& bmask b = bmask (a && b) := by
  cases a <;> cases b <;> decide

theorem sel_xor (x y : BitVec 64) (v : Bool) : (x ^^^ y) &&& bmask v ^^^ x = if v then y else x := by
  cases v
  · simp [bmask]
  · simp only [bmask, ite_true]
    rw [BitVec.and_allOnes, BitVec.xor_comm x y, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- Whether the padding is valid, from the scan. -/
abbrev vOf (b0 b1 : Byte) (f : Bool) (sep : Nat) : Bool := decide (b0 = 0 ∧ b1 = 2 ∧ f = true ∧ 10 ≤ sep)

/-- The selected length. -/
abbrev lenOf (v : Bool) (sep al k : Nat) : BitVec 64 :=
  if v then BitVec.ofNat 64 (k - sep - 1) else BitVec.ofNat 64 al

/-- Whether the private-key operation succeeded. -/
abbrev okOf (R : BitVec 64) : Bool := decide (R.setWidth 32 = 1)

/-- What `validBlock` leaves. -/
def VOut (b0 b1 : Byte) (f : Bool) (sep al k : Nat) (R : BitVec 64) (t t' : State) : Prop :=
  t'.mem = t.mem ∧ t'.gpr .r10 = bmask (vOf b0 b1 f sep) ∧
    t'.gpr .rdx = lenOf (vOf b0 b1 f sep) sep al k &&& bmask (okOf R) ∧ t'.gpr .r11 = bmask (okOf R) ∧
    t'.gpr .rsi = BitVec.ofNat 64 k - lenOf (vOf b0 b1 f sep) sep al k

theorem validBlock_run {t : State} {p F : Addr} {b0 b1 : Byte} {f : Bool} {sep al k : Nat} {R : BitVec 64}
    (hdi : t.gpr .rdi = p) (h0 : t.mem p = b0) (h1 : t.mem (off p 1) = b1)
    (hi0 : InRegions (t.rd ++ t.wr) p 1) (hi1 : InRegions (t.rd ++ t.wr) (off p 1) 1)
    (hdx : t.gpr .rdx = bmask f) (h10 : t.gpr .r10 = BitVec.ofNat 64 sep) (h11 : t.gpr .r11 = BitVec.ofNat 64 al)
    (h9 : t.gpr .r9 = BitVec.ofNat 64 k) (hsp : t.gpr .rsp = F) (hR : t.mem.readW (F + BitVec.ofNat 64 oR) 64 = R)
    (hiR : InRegions (t.rd ++ t.wr) (F + BitVec.ofNat 64 oR) 8) (hsk : sep < k) (hk : k < 2 ^ 32) :
    WP isa (.block validBlock) t fun t' => VOut b0 b1 f sep al k R t t' ∧ Keep [.rax, .rsi, .rdx, .r10, .r11] t t' := by
  refine WP.keep [.rax, .rsi, .rdx, .r10, .r11] (c := .block validBlock) (Q := VOut b0 b1 f sep al k R t) ?_ rfl
  xrun [VOut, validBlock, ea_atd (p := p), hdi, h0, h1, hi0, hi1, hdx, h10, h11, h9, ea_sp, hsp, hR, hiR, borrow_mask,
    zero_test, two_test, ten_test (show sep < 2 ^ 64 by omega_using [hsk, hk]), ok_test, bmask_not, bmask_and]
  obtain e : BitVec.ofNat 64 k - BitVec.ofNat 64 sep - 1 = BitVec.ofNat 64 (k - sep - 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
    omega_using [hsk]
  obtain hv : (decide (b0 = 0) && decide (b1 = 2) && f && !decide (sep < 10)) = vOf b0 b1 f sep := by
    simp only [vOf]
    by_cases h₂ : sep < 10
    · simp [h₂, show ¬ 10 ≤ sep by omega_using [h₂]]
    · simp [h₂, show 10 ≤ sep by omega_using [h₂], Bool.and_assoc]
  rw [e, sel_xor, hv]
  exact ⟨rfl, rfl, rfl⟩

end VG.Proof.RsaPkcs1Enc.X86_64.Dec

end

end


/-!
# RSAES-PKCS1-v1_5 decryption on x86-64: the output

`*msg_len` and each byte of `out` selected without branches, reading both
`EM` and `AM` (`selLoop_ok`), and the result (`selPart_step`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86_64.Dec

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Decrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Enc.X86_64

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
  obtain e1 : 0 + i = i := Nat.zero_add _
  xrun [selBody, ea_bxd (p := p) (j := i), ea_bxd (p := q) (j := i), hdi, hsi, hcx, e1, hie, hia, hw, he, ha,
    hdx, h9, h10, h11, borrow_mask, bmask_not, bmask_and, ofNat_add_one,
    ofNat_sub_beq (show i + 1 < 2 ^ 64 by omega_arith) (show k < 2 ^ 64 by omega_arith), sel_xor]
  congr 1
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega_arith),
    Nat.mod_eq_of_lt (show kl < 2 ^ 64 by omega_arith)]
  unfold outByte
  obtain and255 : ∀ x : Byte, x &&& 255#8 = x := fun x => by
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
    (fun _ ⟨k, ho, hb, _⟩ => ⟨k, ho, hb⟩) ⟨Keep.refl _ _, Outside.refl _ _ _ _, fun _ h => absurd h (by omega_arith), hcx⟩
  obtain g : ∀ r, r ∉ [Reg.rax, .r8, .rcx] → u.gpr r = t₀.gpr r := fun r hr => ku.gpr hr
  obtain he : u.mem (off p j) = t₀.mem (off p j) := ho _ (.inr (by rw [ofs_off0 _ (by omega_arith)]; omega_arith))
  obtain ha : u.mem (off q j) = t₀.mem (off q j) := ho _ (.inr (by have := hpq j hj; omega_arith))
  refine WP.mono (selBody_run hj hk hkl ((g .rdi (by decide)).trans hdi) ((g .rsi (by decide)).trans hsi) hcxu
    ((g .rdx (by decide)).trans hdx) ((g .r9 (by decide)).trans h9) ((g .r10 (by decide)).trans h10)
    ((g .r11 (by decide)).trans h11) he ha (by rw [ku.2.1, ku.2.2]; exact hie j hj)
    (by rw [ku.2.1, ku.2.2]; exact hia j hj) (by rw [ku.2.2]; exact hw j hj))
    fun u' ⟨hm, hcx', hz, k'⟩ => ⟨hz, (ku.trans k').mono (by decide), ?_, ?_, hcx'⟩
  · rw [hm]; exact Outside.wb (Outside.mono ho (by omega_arith) (by omega_arith)) _ (by omega_arith) (by omega_arith) (by omega_arith)
  · intro i hi
    rw [hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [byte_wb _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]; exact hb i hi
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
    | none => simp; omega_arith
    | some i => have := firstZero_some hf; simpa using this.2.1
  have hal := altFold_le (kOf s) (clOf s) 128
  rw [← altLength_eq] at hal
  have hL : lEM s EM ≤ kOf s := by
    simp only [lEM, lselOf]; split <;> omega_arith
  -- the checks
  have hR : t.mem.readW (fb s + BitVec.ofNat 64 oR) 64 = R := hc.sR
  have hio : ∀ i n, i + n ≤ kOf s → InRegions (t.rd ++ t.wr) (off (s.gpr .rdi) i) n := fun i n h' =>
    let ⟨r, hr, hcr⟩ := hc.outIn hp h'; ⟨r, List.mem_append_right _ hr, hcr⟩
  refine WP.seq (WP.mono (validBlock_run (p := s.gpr .rdi) (F := fb s) (b0 := EM.getD 0 1) (b1 := EM.getD 1 1)
    h.rdi (by rw [← hc.em (i := 0) (by omega_arith)]; exact (congrArg t.mem (off_zero _)).symm)
    (hc.em (by omega_arith)) (by have := hio 0 1 (by omega_arith); rwa [off_zero] at this) (hio 1 1 (by omega_arith)) h.rdx h.r10 h.r11
    h.r9 hc.rsp hR (hs.ld (d := oR) (by decide)) hsep (by omega_arith))
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
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega_arith
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
      (show kOf s ≤ 2 ^ 64 by omega_arith) hi
  have hAM := h.am
  have ha₃ : ∀ i < kOf s, t₃.mem (off (scA s sAM) i) = (amOf s).getD i 0 := fun i hi => by
    show _ = (Spec.RsaPkcs1Enc.irprf (kdkOf s) (Spec.RsaPkcs1Enc.ascii "message") (kOf s)).getD i 0
    rw [← hAM, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [blen]; exact hi), Option.getD_some, bget]
    exact hfw₃.bytes (R := ⟨scA s sAM, kOf s⟩) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact (hp.dMs.sub_right (dAM (by unfold sAM scrBytes; omega_arith))).symm)
      (show kOf s ≤ 2 ^ 64 by omega_arith) hi
  have kk : Keep (([.rax, .rsi, .rdx, .r10, .r11] : List Reg) ++ ([.r8, .rcx] : List Reg) ++
      ([.rdx, .rsi, .rcx] : List Reg)) t t₃ := (k₁.trans k₂).trans k₃
  have g : ∀ r, r ∉ [Reg.rax, .rsi, .rdx, .r10, .r11, .r8, .rcx] → t₃.gpr r = t.gpr r := fun r hr =>
    have hr' : r ∉ ([Reg.rax, .rsi, .rdx, .r10, .r11] : List Reg) ++ ([.r8, .rcx] : List Reg) ++
        ([.rdx, .rsi, .rcx] : List Reg) := by
      intro h; apply hr
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with ((h | h | h | h | h) | (h | h)) | (h | h | h) <;> subst h <;> simp
    kk.gpr hr'
  have hrw : t₃.rd ++ t₃.wr = t.rd ++ t.wr := by rw [kk.2.1, kk.2.2]
  refine WP.seq (WP.mono (selLoop_ok (p := s.gpr .rdi) (q := scA s sAM) (k := kOf s) (kl := kOf s - lEM s EM)
    (v := vEM EM (kOf s)) (ok := okOf R) (by omega_arith) (by omega_arith) (by omega_arith) ((g .rdi (by decide)).trans h.rdi)
    hsi₃ hcx₃ hdx₃ ((g .r9 (by decide)).trans h.r9)
    ((k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h10₁))
    ((k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h11₁))
    (fun i hi => by rw [hrw]; exact hio i 1 (by omega_arith))
    (fun i hi => by
      rw [hrw]
      obtain ⟨r, hr, hcr⟩ := hsc.region (d := sAM + i) (n := 1) (by unfold sAM scrBytes; omega_arith) (by decide)
      exact ⟨r, List.mem_append_right _ hr, by rw [scA, off_off]; exact hcr⟩)
    (fun i hi => by rw [kk.2.2]; exact hc.outIn hp (i := i) (n := 1) (by omega_arith))
    (fun i hi => ofs_of_disjoint (dOS.sub_right (dAM (by unfold sAM scrBytes; omega_arith))) hi (by omega_arith)))
    fun t₄ ⟨k₄, ho₄, hb₄⟩ => ?_)
  have hfo₄ : Frame [⟨s.gpr .rdi, kOf s⟩] t₃.mem t₄.mem := by
    have := frame_of_out ho₄ (by omega_arith); rwa [off_zero] at this
  have hR₄ : word t₄.mem (fb s) oR = R := by
    rw [← hc.sR]
    refine (hfo₄.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)).trans
      (hfw₃.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide))
    · rw [List.mem_singleton.mp hr]; exact (dKO.sub_left (frame_sub s (by decide)))
    · rw [List.mem_singleton.mp hr]; exact (hp.dKm.sub_left (frame_sub s (by decide)))
  have hsp₄ : t₄.gpr .rsp = fb s := (k₄.gpr (by decide)).trans ((g .rsp (by decide)).trans hc.rsp)
  have hs₄ : Scr t₄ (fb s) frameBytes := Scr.of_mem (by rw [k₄.2.2, kk.2.2, hc.wr]; exact List.mem_cons_self ..)
    (by have := (fb_toNat hp).1; omega_arith)
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

end

end

/-!
# RSAES-PKCS1-v1_5 decryption on x86-64: the selected message

What the output loop writes, for the validity, length and message the scan
and the derivation found, is the message `implicitDecode` returns, after
zeros (`sel_eq`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86_64.Dec

open VG VG.X86_64 Spec.RsaPkcs1Enc

theorem vEM_eq {EM : List Byte} {k : Nat} (hEM : EM.length = k) (hk : 2 ≤ k) : vEM EM k = valid EM := by
  rw [valid_eq, hEM, show EM.getD 1 0 = EM.getD 1 1 by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega_using [hEM, hk])]; rfl]
  simp only [vEM, vOf]
  cases hf : firstZero EM k with
  | none => simp
  | some i =>
    simp only [Option.isSome_some, Option.getD_some]
    generalize EM.getD 0 1 = x
    generalize EM.getD 1 1 = y
    by_cases a : x = 0 <;> by_cases b : y = 2 <;> by_cases c : 10 ≤ i <;> simp [a, b, c, Bool.beq_eq_decide_eq]

theorem msgLength_le {EM : List Byte} : msgLength EM ≤ EM.length := by
  rw [msgLength_eq]; split
  · exact Nat.le_trans (Nat.sub_le _ _) (Nat.sub_le _ _)
  · exact Nat.zero_le _

theorem lastN_length {l : Nat} {X : List Byte} (h : l ≤ X.length) : (lastN l X).length = l := by
  simp [lastN]; omega_using [h]

/-- The output of the selection, for a successful private-key operation. -/
theorem sel_eq {EM AM : List Byte} {k al : Nat} (hEM : EM.length = k) (hAM : AM.length = k) (hk : 11 ≤ k)
    (hal : al ≤ k - 11) :
    let M := if valid EM then lastN (msgLength EM) EM else lastN al AM
    lselOf (vEM EM k) ((firstZero EM k).getD 0) al k = M.length ∧
    (List.range k).map (fun i => outByte (vEM EM k) true (k - lselOf (vEM EM k) ((firstZero EM k).getD 0) al k) i
      (EM.getD i 1) (AM.getD i 0)) = List.replicate (k - M.length) 0 ++ M := by
  intro M
  rw [vEM_eq hEM (by omega_using [hk])]
  have hL : lselOf (valid EM) ((firstZero EM k).getD 0) al k = M.length := by
    simp only [lselOf, M]
    cases hv : valid EM
    · simp [lastN_length (show al ≤ AM.length by omega_using [hAM, hal])]
    · simp only [↓reduceIte]
      rw [lastN_length msgLength_le, msgLength_eq, hEM]
      rw [valid_eq, hEM] at hv
      cases hf : firstZero EM k with
      | none => simp [hf] at hv
      | some i => rfl
  refine ⟨hL, ?_⟩
  rw [hL]
  cases hv : valid EM
  · simp only [M, hv, Bool.false_eq_true, ↓reduceIte]
    have hl : al ≤ AM.length := by omega_using [hAM, hal]
    rw [lastN_length hl, show k = AM.length from hAM.symm, out_eq hl]
    refine List.map_congr_left fun i hi => ?_
    simp only [outByte, and_true, Bool.false_eq_true, ↓reduceIte]
  · simp only [M, hv, ↓reduceIte]
    have hl := (msgLength_le (EM := EM))
    rw [lastN_length hl, show k = EM.length from hEM.symm, out_eq hl]
    refine List.map_congr_left fun i hi => ?_
    simp only [outByte, and_true, ↓reduceIte]
    rw [List.mem_range] at hi
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    rfl

end VG.Proof.RsaPkcs1Enc.X86_64.Dec
