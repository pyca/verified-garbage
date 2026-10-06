import VerifiedGarbage.Impl.RsaPkcs1Sig.AArch64.Encode
import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem

/-!
# EMSA-PKCS1-v1_5 encoding on AArch64: correctness

As on x86-64 (`Proof/RsaPkcs1Sig/X86_64/Encode.lean`). `encode_ok`: from a
state whose `x8` points to `k` writable bytes, `x11` to the hash value,
which does not overlap them, `encode` returns 1 and writes the encoding of
the value (`Spec.RsaPkcs1Sig.encode`) to the buffer if it exists, and
returns 0 and leaves memory as it was if not. `compare_ok`: `compare` leaves
in `x12` a value that is zero exactly when its two buffers are equal.
-/

namespace VG.Proof.RsaPkcs1Sig.AArch64

open VG VG.AArch64 VG.Impl.RsaPkcs1Sig.AArch64 Spec.RsaPkcs1Sig VG.WriteBytes
open VG.Proof.MlKem.AArch64 (Keep Only MemTo wp_movz wp_strb wp_ldrb wp_addImm wp_subImm wp_sub wp_lsr
  wp_eor wp_orr wp_nil eval_nonzero ne_zero_iff count_loop)
open VG.Proof.RsaPkcs1Sig

/-! ## Loops -/

/-- A do-while loop on `cbnz cnt` whose body decrements `cnt`, from `N > 0`:
it runs `N` times. -/
theorem wp_countdown {body : Prog isa} {cnt : Reg} {N : Nat} (hN : N < 2 ^ 64) (hN0 : 0 < N)
    (Inv : Nat → State → Prop)
    (hbody : ∀ i < N, ∀ s, Inv i s → s.gpr cnt = BitVec.ofNat 64 (N - i) →
      WP isa body s fun s' => Inv (i + 1) s' ∧ s'.gpr cnt = s.gpr cnt - BitVec.ofNat 64 1)
    {s : State} (h0 : Inv 0 s) (hc : s.gpr cnt = BitVec.ofNat 64 N) :
    WP isa (.loop body (.nonzero .x cnt)) s (Inv N) := by
  refine WP.mono (count_loop (cr := cnt) hN0 (fun k s => Inv k s ∧ s.gpr cnt = BitVec.ofNat 64 (N - k))
    (fun k hk s ⟨hI, hc⟩ => WP.mono (hbody k hk s hI hc) fun s' ⟨hI', hc'⟩ => ⟨⟨hI', ?_⟩, ?_⟩)
    ⟨h0, by rw [hc, Nat.sub_zero]⟩) fun _ h => h.1
  · rw [hc', hc]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  · rw [hc', hc, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega

theorem ite_both {c : Cond} {th el : Prog isa} {s : State} {Q : State → Prop} (b : Bool)
    (hc : isa.eval c s = some b) (h₁ : WP isa th s Q) (h₂ : WP isa el s Q) : WP isa (.ite c th el) s Q := by
  cases b
  · exact WP.ite false hc (by simp) (fun _ => h₂)
  · exact WP.ite true hc (fun _ => h₁) (by simp)

theorem byte_setWidth (b : Byte) : ((b.setWidth 16).setWidth 64).setWidth 8 = b := by
  apply BitVec.eq_of_toNat_eq; simp

theorem byte_setWidth64 (b : Byte) : ((b.setWidth 64)).setWidth 8 = b := by
  apply BitVec.eq_of_toNat_eq; simp

theorem ofNat_succ' (a : Addr) (n : Nat) :
    a + BitVec.ofNat 64 n + BitVec.ofNat 64 1 = a + BitVec.ofNat 64 (n + 1) := ofNat_succ a n

/-! ## Writing the buffer -/

/-- The registers `encode` writes. -/
def clob : List Reg := [.x0, .x11, .x12, .x13, .x14, .x15]

/-- The buffer has been written with `acc` so far, and `x14` points after it. -/
def W (s₀ : State) (acc : List Byte) (s : State) : Prop :=
  Keep clob s₀ s ∧ s.mem = writeBytes s₀.mem (s₀.gpr .x8) acc ∧
    s.gpr .x14 = s₀.gpr .x8 + BitVec.ofNat 64 acc.length

/-- The buffer's bytes are writable. -/
def Buf (s₀ : State) (k : Nat) : Prop :=
  ∀ i < k, InRegions s₀.wr (s₀.gpr .x8 + BitVec.ofNat 64 i) 1

theorem putByte_ok {s₀ s : State} {k : Nat} (hb : Buf s₀ k) {acc : List Byte} (hl : acc.length < k)
    (hk : k < 2 ^ 64) (b : Byte) (h : W s₀ acc s) :
    WP isa (.block (putByte b)) s fun t => W s₀ (acc ++ [b]) t ∧ Keep [.x14, .x15] s t := by
  obtain ⟨hK, hm, h14⟩ := h
  refine wp_movz fun s₁ o₁ e₁ => ?_
  have hA : InRegions s₁.wr (s₁.gpr .x14 + BitVec.ofNat 64 0) 1 := by
    rw [o₁.wr, o₁.get .x14, h14, hK.wr, BitVec.add_zero]; exact hb _ hl
  refine wp_strb (by decide) rfl hA fun s₂ m₂ => ?_
  refine wp_addImm (by decide) fun s₃ o₃ e₃ => wp_nil ?_
  have hK' : Keep [.x14, .x15] s s₃ := (o₁.keep.trans (m₂.keep.trans o₃.keep)).mono
  refine ⟨⟨(hK.trans hK').mono, ?_, ?_⟩, hK'⟩
  · rw [o₃.mem, m₂.mem, o₁.mem, e₁, byte_setWidth, o₁.get .x14, h14, BitVec.add_zero, hm,
      writeBytes_snoc _ _ _ _ (by omega)]
  · rw [e₃, m₂.gpr, o₁.get .x14, h14, ofNat_succ', List.length_append, List.length_singleton]

theorem putBytes_ok {s₀ : State} {k : Nat} (hb : Buf s₀ k) (hk : k < 2 ^ 64) (bs : List Byte) :
    ∀ {acc : List Byte} {s : State}, acc.length + bs.length ≤ k → W s₀ acc s →
      WP isa (.block (putBytes bs)) s fun t => W s₀ (acc ++ bs) t ∧ Keep [.x14, .x15] s t := by
  induction bs with
  | nil => intro acc s _ h; exact WP.block_nil ⟨by simpa using h, Keep.refl _ _⟩
  | cons b bs ih =>
    intro acc s hl h
    simp only [putBytes, List.flatMap_cons] at ih ⊢
    rw [WP.block_append_iff]
    refine WP.mono (putByte_ok hb (by simp at hl; omega) hk b h) fun t ⟨ht, hk₁⟩ => ?_
    refine WP.mono (ih (acc := acc ++ [b]) (s := t) (by simp at hl ⊢; omega) ht) fun u ⟨hu, hk₂⟩ =>
      ⟨by simpa using hu, (hk₁.trans hk₂).mono⟩

/-- `PS`: `n` bytes `b` (in `x15`; `0xff` for `PS`), counted down in `x13`. -/
theorem psLoop_ok {s₀ s : State} {k : Nat} (hb : Buf s₀ k) (hk : k < 2 ^ 64) {acc : List Byte}
    {n : Nat} (hn : 0 < n) (hl : acc.length + n ≤ k) (h : W s₀ acc s) (b : Byte)
    (hax : (s.gpr .x15).setWidth 8 = b) (hc : s.gpr .x13 = BitVec.ofNat 64 n) :
    WP isa psLoop s fun t => W s₀ (acc ++ List.replicate n b) t ∧ Keep [.x13, .x14] s t := by
  refine WP.mono (wp_countdown (cnt := .x13) (by omega) hn
    (fun i t => W s₀ (acc ++ List.replicate i b) t ∧ (t.gpr .x15).setWidth 8 = b ∧ Keep [.x13, .x14] s t) ?_
    ⟨by simpa using h, hax, Keep.refl _ _⟩ hc) fun _ h => ⟨h.1, h.2.2⟩
  intro i hi t ⟨⟨hK, hm, h14⟩, hax, hKs⟩ _
  have hA : InRegions t.wr (t.gpr .x14 + BitVec.ofNat 64 0) 1 := by
    rw [h14, hK.wr, BitVec.add_zero]; exact hb _ (by simp; omega)
  refine wp_strb (by decide) rfl hA fun s₁ m₁ => ?_
  refine wp_addImm (by decide) fun s₂ o₂ e₂ => ?_
  refine wp_subImm (by decide) fun s₃ o₃ e₃ => wp_nil ?_
  have hK' : Keep [.x14, .x13] t s₃ := (m₁.keep.trans (o₂.keep.trans o₃.keep)).mono
  refine ⟨⟨⟨(hK.trans hK').mono, ?_, ?_⟩, by rw [hK'.get .x15]; exact hax, (hKs.trans hK').mono⟩, ?_⟩
  · rw [o₃.mem, o₂.mem, m₁.mem, hax, h14, BitVec.add_zero, hm, List.replicate_succ', ← List.append_assoc,
      writeBytes_snoc _ _ _ _ (by simp; omega)]
  · rw [o₃.get .x14, e₂, m₁.gpr, h14, ofNat_succ']; simp [List.replicate_succ', Nat.add_assoc]
  · rw [e₃, o₂.get .x13, m₁.gpr]

/-- The hash value: `n` bytes from `x11`, counted down in `x12`. -/
theorem copyLoop_ok {s₀ s : State} {k : Nat} (hb : Buf s₀ k) (hk : k < 2 ^ 64) {acc : List Byte}
    {n : Nat} (hn : 0 < n) (hl : acc.length + n ≤ k) (h : W s₀ acc s)
    (hsi : s.gpr .x11 = s₀.gpr .x11) (hc : s.gpr .x12 = BitVec.ofNat 64 n)
    (hr : ∀ j < n, InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x11 + BitVec.ofNat 64 j) 1)
    (hd : ∀ j < n, ∀ i < k, s₀.gpr .x11 + BitVec.ofNat 64 j ≠ s₀.gpr .x8 + BitVec.ofNat 64 i) :
    WP isa copyLoop s (W s₀ (acc ++ Spec.Rsa.bytesAt s₀.mem (s₀.gpr .x11) n)) := by
  have hn' : n < 2 ^ 64 := by omega
  refine WP.mono (wp_countdown (cnt := .x12) hn' hn
    (fun i t => W s₀ (acc ++ (Spec.Rsa.bytesAt s₀.mem (s₀.gpr .x11) n).take i) t ∧
      t.gpr .x11 = s₀.gpr .x11 + BitVec.ofNat 64 i) ?_
    ⟨by simpa using h, by rw [hsi]; simp⟩ hc) fun t h => ?_
  · intro i hi t ⟨⟨hK, hm, h14⟩, h11⟩ _
    have hlt : (acc ++ (Spec.Rsa.bytesAt s₀.mem (s₀.gpr .x11) n).take i).length = acc.length + i := by
      simp [Spec.Rsa.bytesAt]; omega
    have hR : InRegions (t.rd ++ t.wr) (t.gpr .x11 + BitVec.ofNat 64 0) 1 := by
      rw [h11, hK.rd, hK.wr, BitVec.add_zero]; exact hr _ hi
    have hv : t.mem (s₀.gpr .x11 + BitVec.ofNat 64 i) = s₀.mem (s₀.gpr .x11 + BitVec.ofNat 64 i) := by
      rw [hm, writeBytes_out _ _ _ _ k (hd i hi) (by omega)]
    refine wp_ldrb (by decide) rfl hR fun s₁ o₁ e₁ => ?_
    have hA : InRegions s₁.wr (s₁.gpr .x14 + BitVec.ofNat 64 0) 1 := by
      rw [o₁.wr, o₁.get .x14, h14, hK.wr, hlt, BitVec.add_zero]; exact hb _ (by omega)
    refine wp_strb (by decide) rfl hA fun s₂ m₂ => ?_
    refine wp_addImm (by decide) fun s₃ o₃ e₃ => ?_
    refine wp_addImm (by decide) fun s₄ o₄ e₄ => ?_
    refine wp_subImm (by decide) fun s₅ o₅ e₅ => wp_nil ?_
    have hK' : Keep [.x15, .x11, .x14, .x12] t s₅ :=
      (o₁.keep.trans (m₂.keep.trans (o₃.keep.trans (o₄.keep.trans o₅.keep)))).mono
    refine ⟨⟨⟨(hK.trans hK').mono, ?_, ?_⟩, ?_⟩, ?_⟩
    · rw [o₅.mem, o₄.mem, o₃.mem, m₂.mem, e₁, o₁.mem, h11]
      simp only [BitVec.add_zero]
      rw [hv, byte_setWidth64, o₁.get .x14, h14, hm, bytesAt_take_succ _ _ hi, ← List.append_assoc,
        writeBytes_snoc _ _ _ _ (by omega)]
    · rw [o₅.get .x14, e₄, o₃.get .x14, m₂.gpr, o₁.get .x14, h14, ofNat_succ', bytesAt_take_succ _ _ hi]
      simp only [List.length_append, List.length_singleton, Nat.add_assoc]
    · rw [o₅.get .x11, o₄.get .x11, e₃, m₂.gpr, o₁.get .x11, h11, ofNat_succ']
    · rw [e₅, o₄.get .x12, o₃.get .x12, m₂.gpr, o₁.get .x12]
  · rw [List.take_of_length_le (by simp [Spec.Rsa.bytesAt])] at h
    exact h.1

/-! ## The hash function's number -/

theorem ofId_hashes : ∀ j (h : j < hashes.length), Hash.ofId j = some hashes[j] := by decide

theorem ofId_ge {j : Nat} (h : hashes.length ≤ j) : Hash.ofId j = none := by
  unfold Hash.ofId; split <;> simp_all [hashes]

theorem subImm_w_ok {t : Reg} {i : Nat} (hi : i < 4096) (s : State) :
    WP isa (.block [.subImm .w t .x10 i]) s fun u => Only [t] s u ∧
      isa.eval (.zero .w t) u = some ((s.gpr .x10).setWidth 32 == BitVec.ofNat 32 i) := by
  refine VG.Proof.MlKem.AArch64.WP.cons (s' := s.write .w t ((s.gpr .x10).setWidth 32 - BitVec.ofNat 32 i)) ?_
    (wp_nil ⟨VG.Proof.MlKem.AArch64.only_write _ _ _ _, ?_⟩)
  · simp [exec, hi, State.read]
  · simp only [eval, State.read, State.write, ite_true, Size.bits]
    rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
    congr 1
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    bv_omega

/-- `dispatch t c d hs i`: `c (i + j) h` if `w10` is `i + j` for the `j`-th
function `h` of `hs`, `d` if it is none of them, from a state but for `t`. -/
theorem dispatch_ok (t : Reg) (c : Nat → Hash → Prog isa) (d : Prog isa) {Q : State → Prop} {s₀ : State}
    (x : BitVec 32) (hx : (s₀.gpr .x10).setWidth 32 = x) (ht : t ≠ .x10) :
    ∀ (hs : List Hash) (i : Nat), i + hs.length < 4096 →
      (∀ j (h : j < hs.length), x.toNat = i + j → ∀ s, Only [t] s₀ s → WP isa (c (i + j) hs[j]) s Q) →
      ((∀ j < hs.length, x.toNat ≠ i + j) → ∀ s, Only [t] s₀ s → WP isa d s Q) →
      ∀ s, Only [t] s₀ s → WP isa (dispatch t c d hs i) s Q := by
  intro hs
  induction hs with
  | nil => intro i _ _ hd s hs; exact hd (fun _ h => absurd h (Nat.not_lt_zero _)) s hs
  | cons h hs ih =>
    intro i hi hc hd s hs₀
    refine WP.seq (WP.mono (subImm_w_ok (t := t) (i := i) (by simp at hi; omega) s) fun u ⟨hu, hz⟩ => ?_)
    have hst : Only [t] s₀ u := (hs₀.trans hu).mono (by intro r hr; simpa using hr)
    have hrdx : (s.gpr .x10).setWidth 32 = x := by rw [hs₀.get .x10 (by simpa using ht.symm)]; exact hx
    rw [hrdx] at hz
    by_cases he : x.toNat = i
    · have hxe : x = BitVec.ofNat 32 i := by
        apply BitVec.eq_of_toNat_eq; rw [he, BitVec.toNat_ofNat]; simp at hi; omega
      refine WP.ite true (by rw [hz, hxe]; simp) (fun _ => ?_) (by simp)
      exact hc 0 (by simp) (by simpa using he) u hst
    · have hxe : x ≠ BitVec.ofNat 32 i := by
        intro h'; apply he; rw [h', BitVec.toNat_ofNat]; simp at hi; omega
      refine WP.ite false (by rw [hz]; simp [hxe]) (by simp) (fun _ => ?_)
      refine ih (i + 1) (by simp at hi; omega) (fun j hj hxj t' ht' => ?_) (fun hn t' ht' => ?_) u hst
      · have := hc (j + 1) (by simp; omega) (by omega) t' ht'
        simpa [Nat.add_assoc, Nat.add_comm 1 j] using this
      · refine hd (fun j hj => ?_) t' ht'
        cases j with
        | zero => simpa using he
        | succ j => have := hn j (by simp at hj; omega); omega

theorem hashes_length : hashes.length = 12 := rfl

theorem setWidth_ofNat16 {v : Nat} (h : v < 2 ^ 16) :
    (BitVec.ofNat 16 v).setWidth 64 = BitVec.ofNat 64 v := by
  apply BitVec.eq_of_toNat_eq; simp; omega

/-- `tLen` and `hLen` into `x13` and `x15`. -/
theorem lens_ok (h : Hash) (s : State) :
    WP isa (lens h) s fun t => Only [.x13, .x15] s t ∧
      t.gpr .x13 = BitVec.ofNat 64 (h.prefix.length + h.len) ∧ t.gpr .x15 = BitVec.ofNat 64 h.len := by
  have := prefix_length_le h
  refine wp_movz fun s₁ o₁ e₁ => wp_movz fun s₂ o₂ e₂ => wp_nil ⟨(o₁.trans o₂).mono, ?_, ?_⟩
  · rw [o₂.get .x13, e₁, setWidth_ofNat16 (by omega)]
  · rw [e₂, setWidth_ofNat16 (by omega)]

theorem W_only {s₀ s t : State} {acc : List Byte} (h : W s₀ acc s) (ht : Only [.x0] s t) : W s₀ acc t :=
  ⟨(h.1.trans ht.keep).mono, ht.mem.trans h.2.1, by rw [ht.get .x14]; exact h.2.2⟩

theorem ofNat_sub3 {k t : Nat} (h : t + 11 ≤ k) (hk : k < 2 ^ 64) :
    BitVec.ofNat 64 k - BitVec.ofNat 64 t - BitVec.ofNat 64 3 = BitVec.ofNat 64 (k - t - 3) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- What `write` needs: the state after the checks, for the hash function
`h` (numbered `x`), a value of `hLen` bytes and `k ≥ tLen + 11`. -/
structure WPre (s₀ : State) (x : BitVec 32) (h : Hash) (k : Nat) (s : State) : Prop where
  keep : Keep clob s₀ s
  mem : s.mem = s₀.mem
  x11 : s.gpr .x11 = s₀.gpr .x11
  x12 : s.gpr .x12 = BitVec.ofNat 64 h.len
  x13 : s.gpr .x13 = BitVec.ofNat 64 (h.prefix.length + h.len)
  x10 : (s₀.gpr .x10).setWidth 32 = x
  id : Hash.ofId x.toNat = some h
  hk : (s₀.gpr .x9).toNat = k
  len : h.prefix.length + h.len + 11 ≤ k
  kle : k ≤ 1024

theorem write_ok {s₀ s : State} {x : BitVec 32} {h : Hash} {k : Nat} (hb : Buf s₀ k)
    (hp : WPre s₀ x h k s)
    (hr : ∀ j < h.len, InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x11 + BitVec.ofNat 64 j) 1)
    (hd : ∀ j < h.len, ∀ i < k, s₀.gpr .x11 + BitVec.ofNat 64 j ≠ s₀.gpr .x8 + BitVec.ofNat 64 i) :
    WP isa write s fun t => Keep clob s₀ t ∧ t.gpr .x0 = 1 ∧
      t.mem = writeBytes s₀.mem (s₀.gpr .x8) ([0x00, 0x01] ++
        List.replicate (k - (h.prefix.length + h.len) - 3) 0xff ++ [0x00] ++ h.prefix ++
        Spec.Rsa.bytesAt s₀.mem (s₀.gpr .x11) h.len) := by
  have hkk : k < 2 ^ 64 := by have := hp.kle; omega
  have hlen := hp.len
  have h9 : s.gpr .x9 = s₀.gpr .x9 := hp.keep.get .x9
  have h8 : s.gpr .x8 = s₀.gpr .x8 := hp.keep.get .x8
  unfold write head
  rw [WP.seq_iff, List.append_assoc, List.append_assoc, WP.block_append_iff]
  -- `x14 := x8`
  refine WP.mono (wp_addImm (is := []) (by decide) fun t o e => wp_nil (Q := fun t =>
      W s₀ [] t ∧ Keep [.x14] s t) ⟨⟨(hp.keep.trans o.keep).mono, by rw [o.mem, hp.mem, writeBytes_nil],
        by rw [e, h8]; simp⟩, o.keep⟩) fun t₀ ⟨hw₀, hK₀⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (putByte_ok hb (by simp; omega) hkk 0x00 hw₀) fun t₁ ⟨hw₁, hK₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (putByte_ok hb (by simp; omega) hkk 0x01 hw₁) fun t₂ ⟨hw₂, hK₂⟩ => ?_
  have hK₂' : Keep [.x14, .x15] s t₂ := ((hK₀.trans hK₁).trans hK₂).mono
  -- `x13 := k - tLen - 3`, `x15 := 0xff`
  refine wp_sub fun t₃ o₃ e₃ => wp_subImm (by decide) fun t₄ o₄ e₄ => wp_movz fun t₅ o₅ e₅ => wp_nil ?_
  have hO : Only [.x13, .x15] t₂ t₅ := (o₃.trans (o₄.trans o₅)).mono
  have hw₃ : W s₀ ([] ++ [0x00] ++ [0x01]) t₅ :=
    ⟨(hw₂.1.trans hO.keep).mono, hO.mem.trans hw₂.2.1, by rw [hO.get .x14]; exact hw₂.2.2⟩
  have h13 : t₅.gpr .x13 = BitVec.ofNat 64 (k - (h.prefix.length + h.len) - 3) := by
    rw [o₅.get .x13, e₄, e₃, hK₂'.get .x9, hK₂'.get .x13, h9, hp.x13, ← ofNat_sub3 hlen hkk, ← hp.hk]
    simp
  -- `PS`
  refine WP.seq (WP.mono (psLoop_ok hb hkk (n := k - (h.prefix.length + h.len) - 3) (by omega)
    (by simp; omega) hw₃ 0xff (by rw [e₅]; rfl) h13) fun t₆ ⟨hw₆, hK₆⟩ => ?_)
  -- `0x00`
  refine WP.seq (WP.mono (putByte_ok hb (by simp; omega) hkk 0x00 hw₆) fun t₇ ⟨hw₇, hK₇⟩ => ?_)
  have hK₇' : Keep [.x13, .x14, .x15] s t₇ :=
    ((((hK₂'.trans hO.keep).trans hK₆).trans hK₇)).mono
  -- the prefix
  have h10₇ : (t₇.gpr .x10).setWidth 32 = x := by rw [hw₇.1.get .x10]; exact hp.x10
  have hcase : ∀ j (hj : j < hashes.length), x.toNat = 0 + j → ∀ u, Only [.x0] t₇ u →
      WP isa (prefixBytes hashes[j]) u fun t => W s₀ ([] ++ [0x00] ++ [0x01] ++
        List.replicate (k - (h.prefix.length + h.len) - 3) 0xff ++ [0x00] ++ h.prefix) t ∧
        Keep [.x0, .x13, .x14, .x15] s t := by
    intro j hj hxj u hu
    rw [Nat.zero_add] at hxj
    have hhj : hashes[j] = h := by
      have := hp.id; rw [hxj, ofId_hashes j hj] at this; exact Option.some.inj this
    rw [hhj]
    refine WP.mono (putBytes_ok hb hkk h.prefix (by simp; omega) (W_only hw₇ hu)) fun v ⟨hv, hKv⟩ =>
      ⟨hv, ((hK₇'.trans hu.keep).trans hKv).mono⟩
  have hdef : (∀ j < hashes.length, x.toNat ≠ 0 + j) → ∀ u, Only [.x0] t₇ u →
      WP isa (.block []) u fun t => W s₀ ([] ++ [0x00] ++ [0x01] ++
        List.replicate (k - (h.prefix.length + h.len) - 3) 0xff ++ [0x00] ++ h.prefix) t ∧
        Keep [.x0, .x13, .x14, .x15] s t := by
    intro hn u hu
    exfalso
    have hlt : x.toNat < hashes.length := by
      by_contra hc; have := hp.id; rw [ofId_ge (by omega)] at this; cases this
    exact hn _ hlt (by omega)
  refine WP.seq (WP.mono (dispatch_ok .x0 (fun _ h => prefixBytes h) (.block []) (s₀ := t₇) x h10₇
    (by decide) hashes 0 (by decide) hcase hdef t₇ (Only.refl _ _)) fun t₈ ⟨hw₈, hK₈⟩ => ?_)
  refine WP.seq (WP.mono (copyLoop_ok hb hkk (len_pos h) (by simp; omega) hw₈
    (by rw [hK₈.get .x11, hp.x11]) (by rw [hK₈.get .x12, hp.x12]) hr hd) fun t₉ hw₉ => ?_)
  refine wp_movz fun t o e => wp_nil ⟨(hw₉.1.trans o.keep).mono, by rw [e]; rfl, ?_⟩
  rw [o.mem, hw₉.2.1]
  simp only [List.nil_append, List.append_assoc, List.cons_append]

/-! ## `encode` -/

/-- The encoding of `H` to `k` bytes for the hash function numbered `x`. -/
def encodeId (x : BitVec 32) (H : List Byte) (k : Nat) : Option (List Byte) :=
  match Hash.ofId x.toNat with
  | some h => Spec.RsaPkcs1Sig.encode h H k
  | none => none

theorem fail_ok (s : State) :
    WP isa fail s fun t => Only [.x0] s t ∧ t.gpr .x0 = 0 := by
  exact wp_movz fun t o e => wp_nil ⟨o, by rw [e]; rfl⟩

/-- The borrow of `a - b`, for numbers below `2^63`. -/
theorem borrow_ne {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    ((BitVec.ofNat 64 a - BitVec.ofNat 64 b) >>> 63 != 0) = decide (a < b) := by
  rw [ne_zero_iff, BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  apply decide_eq_decide.mpr
  constructor <;> intro h <;> omega

theorem sub_ne {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b != 0) = decide (a ≠ b) := by
  rw [ne_zero_iff, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  apply decide_eq_decide.mpr
  constructor <;> intro h <;> omega

/-- What the encoding needs: the buffer of `k` bytes at `x8` is writable,
the hash value at `x11` (`x12` bytes) is readable and does not overlap it. -/
structure EPre (s₀ : State) (x : BitVec 32) (k : Nat) : Prop where
  x10 : (s₀.gpr .x10).setWidth 32 = x
  hk : (s₀.gpr .x9).toNat = k
  kle : k ≤ 1024
  buf : Buf s₀ k
  rd : ∀ j < (s₀.gpr .x12).toNat, InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x11 + BitVec.ofNat 64 j) 1
  sep : ∀ j < (s₀.gpr .x12).toNat, ∀ i < k,
    s₀.gpr .x11 + BitVec.ofNat 64 j ≠ s₀.gpr .x8 + BitVec.ofNat 64 i

/-- The result `o` of `encode` in the state `t` it ends in: 1 and the
encoding in the buffer, or 0 and memory as it was. -/
def EOut (s₀ t : State) : Option (List Byte) → Prop
  | some em => t.gpr .x0 = 1 ∧ t.mem = writeBytes s₀.mem (s₀.gpr .x8) em
  | none => t.gpr .x0 = 0 ∧ t.mem = s₀.mem

/-- The result of `encode`. -/
def EPost (s₀ : State) (x : BitVec 32) (k : Nat) (t : State) : Prop :=
  Keep clob s₀ t ∧ EOut s₀ t (encodeId x (Spec.Rsa.bytesAt s₀.mem (s₀.gpr .x11) (s₀.gpr .x12).toNat) k)

theorem check1_ok (s : State) {L : Nat} (hL : L < 2 ^ 64) (h15 : s.gpr .x15 = BitVec.ofNat 64 L) :
    WP isa (.block [.sub .x .x0 .x12 .x15]) s fun t => Only [.x0] s t ∧
      isa.eval (.nonzero .x .x0) t = some (decide ((s.gpr .x12).toNat ≠ L)) :=
  wp_sub fun t o e => wp_nil ⟨o, by
    rw [eval_nonzero, e, h15, ne_zero_iff, BitVec.toNat_sub, BitVec.toNat_ofNat]
    have := (s.gpr .x12).isLt
    exact congrArg some (decide_eq_decide.mpr (by constructor <;> intro h <;> omega))⟩

theorem check2_ok (s : State) {T k : Nat} (hT : T < 2 ^ 12) (h13 : s.gpr .x13 = BitVec.ofNat 64 T)
    (h9 : (s.gpr .x9).toNat = k) (hk : k ≤ 1024) :
    WP isa (.block [.addImm .x .x0 .x13 11, .sub .x .x0 .x9 .x0, .lsr .x .x0 .x0 63]) s fun t =>
      Only [.x0] s t ∧ isa.eval (.nonzero .x .x0) t = some (decide (k < T + 11)) :=
  wp_addImm (by decide) fun t₁ o₁ e₁ => wp_sub fun t₂ o₂ e₂ => wp_lsr (by decide) fun t₃ o₃ e₃ =>
    wp_nil ⟨(o₁.trans (o₂.trans o₃)).mono, by
      have e : t₂.gpr .x0 = BitVec.ofNat 64 k - BitVec.ofNat 64 (T + 11) := by
        rw [e₂, o₁.get .x9, e₁, h13, ← h9, BitVec.ofNat_toNat, BitVec.setWidth_eq]
        congr 1; apply BitVec.eq_of_toNat_eq; simp
      rw [eval_nonzero, e₃, e, borrow_ne (by omega) (by omega)]⟩

theorem encode_ok {s₀ : State} {x : BitVec 32} {k : Nat} (hp : EPre s₀ x k) :
    WP isa Impl.RsaPkcs1Sig.AArch64.encode s₀ (EPost s₀ x k) := by
  have hk := hp.hk
  have hkle := hp.kle
  let dl := (s₀.gpr .x12).toNat
  let H := Spec.Rsa.bytesAt s₀.mem (s₀.gpr .x11) dl
  have hHl : H.length = dl := bytesAt_length _ _ _
  have hfail : ∀ u, Only [.x0, .x13, .x15] s₀ u → encodeId x H k = none → WP isa fail u (EPost s₀ x k) :=
    fun u hu hE => WP.mono (fail_ok u) fun t ⟨o, e⟩ => ⟨(hu.keep.trans o.keep).mono, by
      show EOut s₀ t (encodeId x H k)
      rw [hE]; exact ⟨e, o.mem.trans hu.mem⟩⟩
  unfold Impl.RsaPkcs1Sig.AArch64.encode
  cases hid : Hash.ofId x.toNat with
  | none =>
    have hE : encodeId x H k = none := by simp [encodeId, hid]
    have hcase : ∀ j (hj : j < hashes.length), x.toNat = 0 + j → ∀ u, Only [.x0] s₀ u →
        WP isa (lens hashes[j]) u fun t => Only [.x0, .x13, .x15] s₀ t ∧ t.gpr .x13 = 2048 := by
      intro j hj hxj; rw [Nat.zero_add] at hxj; rw [hxj, ofId_hashes j hj] at hid; cases hid
    have hdef : (∀ j < hashes.length, x.toNat ≠ 0 + j) → ∀ u, Only [.x0] s₀ u →
        WP isa noLens u fun t => Only [.x0, .x13, .x15] s₀ t ∧ t.gpr .x13 = 2048 := by
      intro _ u hu
      exact wp_movz fun t₁ o₁ e₁ => wp_movz fun t₂ o₂ e₂ => wp_nil
        ⟨(hu.trans (o₁.trans o₂)).mono, by rw [o₂.get .x13, e₁]; rfl⟩
    refine WP.seq (WP.mono (dispatch_ok .x0 (fun _ h => lens h) noLens x hp.x10 (by decide) hashes 0
      (by decide) hcase hdef s₀ (Only.refl _ _)) fun t₁ ⟨o₁, h13⟩ => ?_)
    refine WP.seq (WP.mono (wp_sub (is := []) fun t o e => wp_nil (Q := fun t => Only [.x0] t₁ t) o)
      fun t₂ o₂ => ?_)
    have hO : Only [.x0, .x13, .x15] s₀ t₂ := (o₁.trans o₂).mono
    refine ite_both ((t₂.gpr .x0) != 0) (eval_nonzero _ _) (hfail t₂ hO hE) ?_
    refine WP.seq (WP.mono (check2_ok t₂ (T := 2048) (by decide) (by rw [o₂.get .x13, h13]; rfl)
      (by rw [hO.get .x9, hk]) hkle) fun t₃ ⟨o₃, hz⟩ => ?_)
    exact WP.ite true (by rw [hz]; simp; omega)
      (fun _ => hfail t₃ ((hO.trans o₃).mono) hE) (by simp)
  | some h =>
    have hcase : ∀ j (hj : j < hashes.length), x.toNat = 0 + j → ∀ u, Only [.x0] s₀ u →
        WP isa (lens hashes[j]) u fun t => Only [.x0, .x13, .x15] s₀ t ∧
          t.gpr .x13 = BitVec.ofNat 64 (h.prefix.length + h.len) ∧ t.gpr .x15 = BitVec.ofNat 64 h.len := by
      intro j hj hxj u hu
      rw [Nat.zero_add] at hxj
      have hhj : hashes[j] = h := by rw [hxj, ofId_hashes j hj] at hid; exact Option.some.inj hid
      rw [hhj]
      exact WP.mono (lens_ok h u) fun t ⟨o, h13, h15⟩ => ⟨(hu.trans o).mono, h13, h15⟩
    have hdef : (∀ j < hashes.length, x.toNat ≠ 0 + j) → ∀ u, Only [.x0] s₀ u →
        WP isa noLens u fun t => Only [.x0, .x13, .x15] s₀ t ∧
          t.gpr .x13 = BitVec.ofNat 64 (h.prefix.length + h.len) ∧ t.gpr .x15 = BitVec.ofNat 64 h.len := by
      intro hn
      exfalso
      have hlt : x.toNat < hashes.length := by
        by_contra hc; rw [ofId_ge (by omega)] at hid; cases hid
      exact hn _ hlt (by omega)
    have hpl := prefix_length_le h
    refine WP.seq (WP.mono (dispatch_ok .x0 (fun _ h => lens h) noLens x hp.x10 (by decide) hashes 0
      (by decide) hcase hdef s₀ (Only.refl _ _)) fun t₁ ⟨o₁, h13, h15⟩ => ?_)
    refine WP.seq (WP.mono (check1_ok t₁ (by omega) h15) fun t₂ ⟨o₂, hz₂⟩ => ?_)
    have hO : Only [.x0, .x13, .x15] s₀ t₂ := (o₁.trans o₂).mono
    rw [o₁.get .x12] at hz₂
    by_cases hdl : dl = h.len
    · refine WP.ite false (by rw [hz₂]; simp [dl] at hdl ⊢; omega) (by simp) (fun _ => ?_)
      refine WP.seq (WP.mono (check2_ok t₂ (T := h.prefix.length + h.len) (by omega)
        (by rw [o₂.get .x13, h13]) (by rw [hO.get .x9, hk]) hkle) fun t₃ ⟨o₃, hz⟩ => ?_)
      have hO₃ : Only [.x0, .x13, .x15] s₀ t₃ := (hO.trans o₃).mono
      by_cases hkl : k < h.prefix.length + h.len + 11
      · refine WP.ite true (by rw [hz]; simp [hkl]) (fun _ => hfail t₃ hO₃ ?_) (by simp)
        simp only [encodeId, hid, Spec.RsaPkcs1Sig.encode, digestInfo, List.length_append, hHl, hdl]
        simp [hkl]
      · refine WP.ite false (by rw [hz]; simp [hkl]) (by simp) (fun _ => ?_)
        have hw : WPre s₀ x h k t₃ := {
          keep := hO₃.keep.mono
          mem := hO₃.mem
          x11 := hO₃.get .x11
          x12 := by rw [hO₃.get .x12, ← hdl]; simp [dl]
          x13 := by rw [o₃.get .x13, o₂.get .x13, h13]
          x10 := hp.x10
          id := hid
          hk := hk
          len := by omega
          kle := hkle }
        refine WP.mono (write_ok hp.buf hw (fun j hj => hp.rd j (by simp [dl] at hdl; omega))
          (fun j hj => hp.sep j (by simp [dl] at hdl; omega))) fun t ⟨hK, hax, hm⟩ => ⟨hK, ?_⟩
        have hE : encodeId x (Spec.Rsa.bytesAt s₀.mem (s₀.gpr .x11) (s₀.gpr .x12).toNat) k =
            some ([0x00, 0x01] ++ List.replicate (k - (h.prefix.length + h.len) - 3) 0xff ++ [0x00] ++
              h.prefix ++ Spec.Rsa.bytesAt s₀.mem (s₀.gpr .x11) h.len) := by
          show encodeId x H k = _
          simp only [encodeId, hid, Spec.RsaPkcs1Sig.encode, digestInfo, List.length_append, hHl, hdl]
          simp [hkl, H, dl, hdl]
        rw [hE]
        exact ⟨hax, hm⟩
    · refine WP.ite true (by rw [hz₂]; simp [dl] at hdl ⊢; omega) (fun _ => hfail t₂ hO ?_) (by simp)
      simp [encodeId, hid, Spec.RsaPkcs1Sig.encode, hHl, hdl]

/-! ## `compare` -/

theorem snoc_eq_iff {a b : List Byte} {x y : Byte} (h : a.length = b.length) :
    a ++ [x] = b ++ [y] ↔ a = b ∧ x = y := by
  constructor
  · intro e
    obtain ⟨h1, h2⟩ := List.append_inj e h
    exact ⟨h1, by simpa using h2⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- `compare`: `x12` is zero exactly when the `n` bytes at `x14` and at
`x15` are equal. -/
theorem compare_ok {s : State} {n : Nat} (hn : 0 < n) (hn' : n < 2 ^ 64) (hc : s.gpr .x13 = BitVec.ofNat 64 n)
    (hr1 : ∀ j < n, InRegions (s.rd ++ s.wr) (s.gpr .x14 + BitVec.ofNat 64 j) 1)
    (hr2 : ∀ j < n, InRegions (s.rd ++ s.wr) (s.gpr .x15 + BitVec.ofNat 64 j) 1) :
    WP isa compare s fun t => Only [.x10, .x11, .x12, .x13, .x14, .x15] s t ∧
      (t.gpr .x12 = 0 ↔ Spec.Rsa.bytesAt s.mem (s.gpr .x14) n = Spec.Rsa.bytesAt s.mem (s.gpr .x15) n) ∧
      (t.gpr .x12).toNat < 256 := by
  let A := Spec.Rsa.bytesAt s.mem (s.gpr .x14) n
  let B := Spec.Rsa.bytesAt s.mem (s.gpr .x15) n
  refine WP.seq (wp_movz fun t₀ o₀ e₀ => wp_nil ?_)
  replace e₀ : t₀.gpr .x12 = 0 := by rw [e₀]; rfl
  refine WP.mono (wp_countdown (cnt := .x13) hn' hn (fun i t => Only [.x10, .x11, .x12, .x13, .x14, .x15] s t ∧
      (∃ c : Byte, t.gpr .x12 = c.setWidth 64 ∧ (c = 0 ↔ A.take i = B.take i)) ∧
      t.gpr .x14 = s.gpr .x14 + BitVec.ofNat 64 i ∧ t.gpr .x15 = s.gpr .x15 + BitVec.ofNat 64 i) ?_
    ⟨o₀.mono, ⟨0, by rw [e₀]; rfl, by simp⟩, by rw [o₀.get .x14]; simp, by rw [o₀.get .x15]; simp⟩
    (by rw [o₀.get .x13, hc])) fun t ⟨o, ⟨c, ec, hcz⟩, _, _⟩ => ⟨o, ?_, by rw [ec]; have := c.isLt; simp; omega⟩
  · intro i hi t ⟨o, ⟨c, ec, hcz⟩, h14, h15⟩ _
    have hR1 : InRegions (t.rd ++ t.wr) (t.gpr .x14 + BitVec.ofNat 64 0) 1 := by
      rw [h14, o.rd, o.wr, BitVec.add_zero]; exact hr1 _ hi
    refine wp_ldrb (by decide) rfl hR1 fun t₁ o₁ e₁ => ?_
    have hR2 : InRegions (t₁.rd ++ t₁.wr) (t₁.gpr .x15 + BitVec.ofNat 64 0) 1 := by
      rw [o₁.get .x15, h15, o₁.rd, o₁.wr, o.rd, o.wr, BitVec.add_zero]; exact hr2 _ hi
    refine wp_ldrb (by decide) rfl hR2 fun t₂ o₂ e₂ => ?_
    refine wp_eor fun t₃ o₃ e₃ => wp_orr fun t₄ o₄ e₄ => wp_addImm (by decide) fun t₅ o₅ e₅ =>
      wp_addImm (by decide) fun t₆ o₆ e₆ => wp_subImm (by decide) fun t₇ o₇ e₇ => wp_nil ?_
    have hO : Only [.x10, .x11, .x12, .x14, .x15, .x13] t t₇ :=
      (o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans (o₆.trans o₇)))))).mono
    have hm : t.mem = s.mem := o.mem
    let a := s.mem (s.gpr .x14 + BitVec.ofNat 64 i)
    let b := s.mem (s.gpr .x15 + BitVec.ofNat 64 i)
    have ha : t₂.gpr .x10 = a.setWidth 64 := by
      rw [o₂.get .x10, e₁, h14, hm, BitVec.add_zero]
    have hb : t₂.gpr .x11 = b.setWidth 64 := by
      rw [e₂, o₁.get .x15, h15, o₁.mem, hm, BitVec.add_zero]
    refine ⟨⟨(o.trans hO).mono, ⟨c ||| (a ^^^ b), ?_, ?_⟩, ?_, ?_⟩, ?_⟩
    · rw [o₇.get .x12, o₆.get .x12, o₅.get .x12, e₄, e₃, o₃.get .x12, ha, hb, o₂.get .x12, o₁.get .x12, ec,
        BitVec.setWidth_or, BitVec.setWidth_xor]
    · have e : (c ||| (a ^^^ b) = 0) ↔ (c = 0 ∧ a = b) := by
        simp [BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff]
      rw [e, hcz, bytesAt_take_succ _ _ hi,
        bytesAt_take_succ _ _ hi, snoc_eq_iff (by simp [bytesAt_length])]
    · rw [o₇.get .x14, o₆.get .x14, e₅, o₄.get .x14, o₃.get .x14, o₂.get .x14, o₁.get .x14, h14, ofNat_succ']
    · rw [o₇.get .x15, e₆, o₅.get .x15, o₄.get .x15, o₃.get .x15, o₂.get .x15, o₁.get .x15, h15, ofNat_succ']
    · rw [e₇, o₆.get .x13, o₅.get .x13, o₄.get .x13, o₃.get .x13, o₂.get .x13, o₁.get .x13]
  · rw [ec, List.take_of_length_le (by simp [A, bytesAt_length]),
      List.take_of_length_le (by simp [B, bytesAt_length])] at *
    rw [← hcz]
    constructor
    · intro h; bv_omega
    · intro h; rw [h]; rfl

/-! ## The loops, at any address -/

/-- `psLoop` writes `n` bytes `b` (the low byte of `x15`) from `x14 = p`,
counted down in `x13`, at any writable address. -/
theorem fill_ok {s : State} {p : Addr} {n : Nat} {b : Byte} (hn : 0 < n) (hn' : n < 2 ^ 64)
    (h14 : s.gpr .x14 = p) (h13 : s.gpr .x13 = BitVec.ofNat 64 n) (h15 : (s.gpr .x15).setWidth 8 = b)
    (hw : ∀ i < n, InRegions s.wr (p + BitVec.ofNat 64 i) 1) :
    WP isa psLoop s fun t => Keep [.x13, .x14] s t ∧ t.mem = writeBytes s.mem p (List.replicate n b) := by
  refine WP.mono (wp_countdown (cnt := .x13) hn' hn
    (fun i t => Keep [.x13, .x14] s t ∧ t.mem = writeBytes s.mem p (List.replicate i b) ∧
      t.gpr .x14 = p + BitVec.ofNat 64 i) ?_ ⟨Keep.refl _ _, by simp [writeBytes_nil], by simp [h14]⟩ h13)
    fun t h => ⟨h.1, h.2.1⟩
  intro i hi t ⟨hK, hm, h14'⟩ _
  have hA : InRegions t.wr (t.gpr .x14 + BitVec.ofNat 64 0) 1 := by
    rw [h14', hK.wr, BitVec.add_zero]; exact hw _ hi
  refine wp_strb (by decide) rfl hA fun s₁ m₁ => ?_
  refine wp_addImm (by decide) fun s₂ o₂ e₂ => ?_
  refine wp_subImm (by decide) fun s₃ o₃ e₃ => wp_nil ?_
  have hK' : Keep [.x14, .x13] t s₃ := (m₁.keep.trans (o₂.keep.trans o₃.keep)).mono
  refine ⟨⟨(hK.trans hK').mono, ?_, ?_⟩, ?_⟩
  · rw [o₃.mem, o₂.mem, m₁.mem, hK.get .x15, h15, h14', BitVec.add_zero, hm, List.replicate_succ',
      writeBytes_snoc _ _ _ _ (by simp; omega)]
    simp
  · rw [o₃.get .x14, e₂, m₁.gpr, h14', ofNat_succ']
  · rw [e₃, o₂.get .x13, m₁.gpr]

/-- `copyLoop` copies `n` bytes from `x11 = q` to `x14 = p`, counted down in
`x12`, the source readable, the destination writable and apart from it. -/
theorem copy_ok {s : State} {p q : Addr} {n : Nat} (hn : 0 < n) (hn' : n < 2 ^ 64)
    (h14 : s.gpr .x14 = p) (h11 : s.gpr .x11 = q) (h12 : s.gpr .x12 = BitVec.ofNat 64 n)
    (hr : ∀ j < n, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 j) 1)
    (hw : ∀ i < n, InRegions s.wr (p + BitVec.ofNat 64 i) 1)
    (hd : ∀ j < n, ∀ i < n, q + BitVec.ofNat 64 j ≠ p + BitVec.ofNat 64 i) :
    WP isa copyLoop s fun t => Keep [.x15, .x11, .x14, .x12] s t ∧
      t.mem = writeBytes s.mem p (Spec.Rsa.bytesAt s.mem q n) := by
  refine WP.mono (wp_countdown (cnt := .x12) hn' hn
    (fun i t => Keep [.x15, .x11, .x14, .x12] s t ∧
      t.mem = writeBytes s.mem p ((Spec.Rsa.bytesAt s.mem q n).take i) ∧
      t.gpr .x14 = p + BitVec.ofNat 64 i ∧ t.gpr .x11 = q + BitVec.ofNat 64 i) ?_
    ⟨Keep.refl _ _, by simp [writeBytes_nil], by simp [h14], by simp [h11]⟩ h12) fun t h => ⟨h.1, ?_⟩
  · intro i hi t ⟨hK, hm, h14', h11'⟩ _
    have hR : InRegions (t.rd ++ t.wr) (t.gpr .x11 + BitVec.ofNat 64 0) 1 := by
      rw [h11', hK.rd, hK.wr, BitVec.add_zero]; exact hr _ hi
    have hv : t.mem (q + BitVec.ofNat 64 i) = s.mem (q + BitVec.ofNat 64 i) := by
      rw [hm, writeBytes_out _ _ _ _ n (fun i' hi' => hd i hi i' hi')
        (by simp only [List.length_take, bytesAt_length]; omega)]
    refine wp_ldrb (by decide) rfl hR fun s₁ o₁ e₁ => ?_
    have hA : InRegions s₁.wr (s₁.gpr .x14 + BitVec.ofNat 64 0) 1 := by
      rw [o₁.wr, o₁.get .x14, h14', hK.wr, BitVec.add_zero]; exact hw _ hi
    refine wp_strb (by decide) rfl hA fun s₂ m₂ => ?_
    refine wp_addImm (by decide) fun s₃ o₃ e₃ => ?_
    refine wp_addImm (by decide) fun s₄ o₄ e₄ => ?_
    refine wp_subImm (by decide) fun s₅ o₅ e₅ => wp_nil ?_
    have hK' : Keep [.x15, .x11, .x14, .x12] t s₅ :=
      (o₁.keep.trans (m₂.keep.trans (o₃.keep.trans (o₄.keep.trans o₅.keep)))).mono
    have hlt : ((Spec.Rsa.bytesAt s.mem q n).take i).length = i := by
      simp [bytesAt_length]; omega
    refine ⟨⟨(hK.trans hK').mono, ?_, ?_, ?_⟩, ?_⟩
    · rw [o₅.mem, o₄.mem, o₃.mem, m₂.mem, e₁, o₁.mem, h11']
      simp only [BitVec.add_zero]
      rw [hv, byte_setWidth64, o₁.get .x14, h14', hm, bytesAt_take_succ _ _ hi,
        writeBytes_snoc _ _ _ _ (by omega), hlt]
    · rw [o₅.get .x14, e₄, o₃.get .x14, m₂.gpr, o₁.get .x14, h14', ofNat_succ']
    · rw [o₅.get .x11, o₄.get .x11, e₃, m₂.gpr, o₁.get .x11, h11', ofNat_succ']
    · rw [e₅, o₄.get .x12, o₃.get .x12, m₂.gpr, o₁.get .x12]
  · rw [List.take_of_length_le (by simp [bytesAt_length])] at h
    exact h.2.1

end VG.Proof.RsaPkcs1Sig.AArch64
