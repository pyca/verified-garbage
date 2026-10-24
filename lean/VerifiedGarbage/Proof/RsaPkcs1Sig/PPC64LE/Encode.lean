module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.PPC64LE.Encode
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Wp
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# EMSA-PKCS1-v1_5 encoding on PPC64LE: correctness

As on AArch64 (`Proof/RsaPkcs1Sig/AArch64/Encode.lean`). `encode_ok`: from a
state whose `r4` points to `k` writable bytes, `r7` to the hash value,
which does not overlap them, `encode` returns 1 and writes the encoding of
the value (`Spec.RsaPkcs1Sig.encode`) to the buffer if it exists, and
returns 0 and leaves memory as it was if not. `compare_ok`: `compare` leaves
in `r7` a value that is zero exactly when its two buffers are equal.
`fill_ok` and `copy_ok` are its loops at any address.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaPkcs1Sig.PPC64LE Spec.RsaPkcs1Sig VG.WriteBytes
open VG.Proof.RsaPkcs1Sig (bytesAt_length bytesAt_take_succ writeBytes_out prefix_length_le len_pos)

theorem byte_ofNat (b : Byte) : (BitVec.ofNat 64 b.toNat).setWidth 8 = b := by
  apply BitVec.eq_of_toNat_eq; simp

theorem byte_setWidth64 (b : Byte) : ((b.setWidth 64)).setWidth 8 = b := by
  apply BitVec.eq_of_toNat_eq; simp

theorem ofNat_succ' (a : Addr) (n : Nat) :
    a + BitVec.ofNat 64 n + BitVec.ofNat 64 1 = a + BitVec.ofNat 64 (n + 1) := by
  rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp

/-! ## Writing the buffer -/

/-- The registers `encode` writes. -/
def clob : List Reg := [.r0, .r3, .r4, .r7, .r8, .r9, .r10, .r11]

/-- The buffer has been written with `acc` so far, and `r4` points after it. -/
def W (s₀ : State) (acc : List Byte) (s : State) : Prop :=
  Keep clob s₀ s ∧ s.mem = writeBytes s₀.mem (s₀.gpr .r4) acc ∧
    s.gpr .r4 = s₀.gpr .r4 + BitVec.ofNat 64 acc.length

/-- The buffer's bytes are writable. -/
def Buf (s₀ : State) (k : Nat) : Prop :=
  ∀ i < k, InRegions s₀.wr (s₀.gpr .r4 + BitVec.ofNat 64 i) 1

theorem putByte_ok {s₀ s : State} {k : Nat} (hb : Buf s₀ k) {acc : List Byte} (hl : acc.length < k)
    (hk : k < 2 ^ 64) (b : Byte) (h : W s₀ acc s) :
    WP isa (.block (putByte b)) s fun t => W s₀ (acc ++ [b]) t ∧ Keep [.r0, .r4] s t := by
  obtain ⟨hK, hm, h4⟩ := h
  refine wp_li (by have := b.isLt; omega) fun s₁ o₁ e₁ => ?_
  have hA : InRegions s₁.wr (s₁.gpr .r4 + BitVec.ofNat 64 0) 1 := by
    rw [o₁.wr, o₁.get .r4, h4, hK.wr, BitVec.add_zero]; exact hb _ hl
  refine wp_stb rfl hA fun s₂ m₂ => ?_
  refine wp_addi fun s₃ o₃ e₃ => wp_nil ?_
  have hK' : Keep [.r0, .r4] s s₃ := (o₁.keep.trans (m₂.keep.trans o₃.keep)).mono
  refine ⟨⟨(hK.trans hK').mono, ?_, ?_⟩, hK'⟩
  · rw [o₃.mem, m₂.mem, o₁.mem, e₁, byte_ofNat, o₁.get .r4, h4, BitVec.add_zero, hm,
      writeBytes_snoc _ _ _ _ (by omega)]
  · rw [e₃, m₂.gpr, o₁.get .r4, h4, ofNat_succ', List.length_append, List.length_singleton]

theorem putBytes_ok {s₀ : State} {k : Nat} (hb : Buf s₀ k) (hk : k < 2 ^ 64) (bs : List Byte) :
    ∀ {acc : List Byte} {s : State}, acc.length + bs.length ≤ k → W s₀ acc s →
      WP isa (.block (putBytes bs)) s fun t => W s₀ (acc ++ bs) t ∧ Keep [.r0, .r4] s t := by
  induction bs with
  | nil => intro acc s _ h; exact WP.block_nil ⟨by simpa using h, Keep.refl _ _⟩
  | cons b bs ih =>
    intro acc s hl h
    simp only [putBytes, List.flatMap_cons] at ih ⊢
    rw [WP.block_append_iff]
    refine WP.mono (putByte_ok hb (by simp at hl; omega) hk b h) fun t ⟨ht, hk₁⟩ => ?_
    refine WP.mono (ih (acc := acc ++ [b]) (s := t) (by simp at hl ⊢; omega) ht) fun u ⟨hu, hk₂⟩ =>
      ⟨by simpa using hu, (hk₁.trans hk₂).mono⟩

/-- `PS`: `n` bytes `b` (in `r0`; `0xff` for `PS`), counted down in `r11`. -/
theorem fillLoop_ok {s₀ s : State} {k : Nat} (hb : Buf s₀ k) (hk : k < 2 ^ 64) {acc : List Byte}
    {n : Nat} (hn : 0 < n) (hl : acc.length + n ≤ k) (h : W s₀ acc s) (b : Byte)
    (hax : (s.gpr .r0).setWidth 8 = b) (hc : s.gpr .r11 = BitVec.ofNat 64 n) :
    WP isa fillLoop s fun t => W s₀ (acc ++ List.replicate n b) t ∧ Keep [.r4, .r11] s t := by
  refine WP.mono (wp_countdown (cnt := .r11) (by omega) hn
    (fun i t => W s₀ (acc ++ List.replicate i b) t ∧ (t.gpr .r0).setWidth 8 = b ∧ Keep [.r4, .r11] s t) ?_
    ⟨by simpa using h, hax, Keep.refl _ _⟩ hc) fun _ h => ⟨h.1, h.2.2⟩
  intro i hi t ⟨⟨hK, hm, h4⟩, hax, hKs⟩ _
  have hA : InRegions t.wr (t.gpr .r4 + BitVec.ofNat 64 0) 1 := by
    rw [h4, hK.wr, BitVec.add_zero]; exact hb _ (by simp; omega)
  refine wp_stb rfl hA fun s₁ m₁ => ?_
  refine wp_addi fun s₂ o₂ e₂ => ?_
  refine wp_subi fun s₃ o₃ e₃ => wp_nil ?_
  have hK' : Keep [.r4, .r11] t s₃ := (m₁.keep.trans (o₂.keep.trans o₃.keep)).mono
  refine ⟨⟨⟨(hK.trans hK').mono, ?_, ?_⟩, by rw [hK'.get .r0]; exact hax, (hKs.trans hK').mono⟩, ?_⟩
  · rw [o₃.mem, o₂.mem, m₁.mem, hax, h4, BitVec.add_zero, hm, List.replicate_succ', ← List.append_assoc,
      writeBytes_snoc _ _ _ _ (by simp; omega)]
  · rw [o₃.get .r4, e₂, m₁.gpr, h4, ofNat_succ']; simp [List.replicate_succ', Nat.add_assoc]
  · rw [e₃, o₂.get .r11, m₁.gpr]

/-- The hash value: `n` bytes from `r7`, counted down in `r8`. -/
theorem copyLoop_ok {s₀ s : State} {k : Nat} (hb : Buf s₀ k) (hk : k < 2 ^ 64) {acc : List Byte}
    {n : Nat} (hn : 0 < n) (hl : acc.length + n ≤ k) (h : W s₀ acc s)
    (hsi : s.gpr .r7 = s₀.gpr .r7) (hc : s.gpr .r8 = BitVec.ofNat 64 n)
    (hr : ∀ j < n, InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .r7 + BitVec.ofNat 64 j) 1)
    (hd : ∀ j < n, ∀ i < k, s₀.gpr .r7 + BitVec.ofNat 64 j ≠ s₀.gpr .r4 + BitVec.ofNat 64 i) :
    WP isa copyLoop s (W s₀ (acc ++ Spec.Rsa.bytesAt s₀.mem (s₀.gpr .r7) n)) := by
  have hn' : n < 2 ^ 64 := by omega
  refine WP.mono (wp_countdown (cnt := .r8) hn' hn
    (fun i t => W s₀ (acc ++ (Spec.Rsa.bytesAt s₀.mem (s₀.gpr .r7) n).take i) t ∧
      t.gpr .r7 = s₀.gpr .r7 + BitVec.ofNat 64 i) ?_
    ⟨by simpa using h, by rw [hsi]; simp⟩ hc) fun t h => ?_
  · intro i hi t ⟨⟨hK, hm, h4⟩, h7⟩ _
    have hlt : (acc ++ (Spec.Rsa.bytesAt s₀.mem (s₀.gpr .r7) n).take i).length = acc.length + i := by
      simp [Spec.Rsa.bytesAt]; omega
    have hR : InRegions (t.rd ++ t.wr) (t.gpr .r7 + BitVec.ofNat 64 0) 1 := by
      rw [h7, hK.rd, hK.wr, BitVec.add_zero]; exact hr _ hi
    have hv : t.mem (s₀.gpr .r7 + BitVec.ofNat 64 i) = s₀.mem (s₀.gpr .r7 + BitVec.ofNat 64 i) := by
      rw [hm, writeBytes_out _ _ _ _ k (hd i hi) (by omega)]
    refine wp_lbz rfl hR fun s₁ o₁ e₁ => ?_
    have hA : InRegions s₁.wr (s₁.gpr .r4 + BitVec.ofNat 64 0) 1 := by
      rw [o₁.wr, o₁.get .r4, h4, hK.wr, hlt, BitVec.add_zero]; exact hb _ (by omega)
    refine wp_stb rfl hA fun s₂ m₂ => ?_
    refine wp_addi fun s₃ o₃ e₃ => ?_
    refine wp_addi fun s₄ o₄ e₄ => ?_
    refine wp_subi fun s₅ o₅ e₅ => wp_nil ?_
    have hK' : Keep [.r0, .r7, .r4, .r8] t s₅ :=
      (o₁.keep.trans (m₂.keep.trans (o₃.keep.trans (o₄.keep.trans o₅.keep)))).mono
    refine ⟨⟨⟨(hK.trans hK').mono, ?_, ?_⟩, ?_⟩, ?_⟩
    · rw [o₅.mem, o₄.mem, o₃.mem, m₂.mem, e₁, o₁.mem, h7]
      simp only [BitVec.add_zero]
      rw [hv, byte_setWidth64, o₁.get .r4, h4, hm, bytesAt_take_succ _ _ hi, ← List.append_assoc,
        writeBytes_snoc _ _ _ _ (by omega)]
    · rw [o₅.get .r4, e₄, o₃.get .r4, m₂.gpr, o₁.get .r4, h4, ofNat_succ', bytesAt_take_succ _ _ hi]
      simp only [List.length_append, List.length_singleton, Nat.add_assoc]
    · rw [o₅.get .r7, o₄.get .r7, e₃, m₂.gpr, o₁.get .r7, h7, ofNat_succ']
    · rw [e₅, o₄.get .r8, o₃.get .r8, m₂.gpr, o₁.get .r8]
  · rw [List.take_of_length_le (by simp [Spec.Rsa.bytesAt])] at h
    exact h.1

/-! ## The hash function's number -/

theorem ofId_hashes : ∀ j (h : j < hashes.length), Hash.ofId j = some hashes[j] := by decide

theorem ofId_ge {j : Nat} (h : hashes.length ≤ j) : Hash.ofId j = none := by
  unfold Hash.ofId; split <;> simp_all [hashes]

theorem subi_w_ok {i : Nat} (hi : i < 2 ^ 15) (s : State) :
    WP isa (.block [.subi .r9 .r6 i]) s fun u => Only [.r9] s u ∧
      isa.eval (.zero .w .r9) u = some ((s.gpr .r6).setWidth 32 == BitVec.ofNat 32 i) :=
  wp_subi (h := by omega) fun u o e => wp_nil ⟨o, by
    rw [eval_zero_w, e]
    congr 1
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    bv_omega⟩

/-- `dispatch c d hs i`: `c h` if `r6` is `i + j` for the `j`-th function `h`
of `hs`, `d` if it is none of them, from a state but for `r9`. -/
theorem dispatch_ok (c : Hash → Prog isa) (d : Prog isa) {Q : State → Prop} {s₀ : State}
    (x : BitVec 32) (hx : (s₀.gpr .r6).setWidth 32 = x) :
    ∀ (hs : List Hash) (i : Nat), i + hs.length < 2 ^ 15 →
      (∀ j (h : j < hs.length), x.toNat = i + j → ∀ s, Only [.r9] s₀ s → WP isa (c hs[j]) s Q) →
      ((∀ j < hs.length, x.toNat ≠ i + j) → ∀ s, Only [.r9] s₀ s → WP isa d s Q) →
      ∀ s, Only [.r9] s₀ s → WP isa (dispatch c d hs i) s Q := by
  intro hs
  induction hs with
  | nil => intro i _ _ hd s hs; exact hd (fun _ h => absurd h (Nat.not_lt_zero _)) s hs
  | cons h hs ih =>
    intro i hi hc hd s hs₀
    refine WP.seq (WP.mono (subi_w_ok (i := i) (by simp at hi; omega) s) fun u ⟨hu, hz⟩ => ?_)
    have hst : Only [.r9] s₀ u := (hs₀.trans hu).mono (by intro r hr; simpa using hr)
    have hrdx : (s.gpr .r6).setWidth 32 = x := by rw [hs₀.get .r6]; exact hx
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
        simpa using this
      · refine hd (fun j hj => ?_) t' ht'
        cases j with
        | zero => simpa using he
        | succ j => have := hn j (by simp at hj; omega); omega

/-- `tLen` and `hLen` into `r9` and `r10`. -/
theorem lens_ok (h : Hash) (s : State) :
    WP isa (lens h) s fun t => Only [.r9, .r10] s t ∧
      t.gpr .r9 = BitVec.ofNat 64 (h.prefix.length + h.len) ∧ t.gpr .r10 = BitVec.ofNat 64 h.len := by
  have := prefix_length_le h
  refine wp_li (by omega) fun s₁ o₁ e₁ => wp_li (by omega) fun s₂ o₂ e₂ => wp_nil ⟨(o₁.trans o₂).mono, ?_, e₂⟩
  rw [o₂.get .r9, e₁]

theorem W_only {s₀ s t : State} {acc : List Byte} (h : W s₀ acc s) {rs : List Reg} (ht : Only rs s t)
    (hrs : ∀ r ∈ rs, r ∈ clob := by decide) (h4 : Reg.r4 ∉ rs := by decide) : W s₀ acc t :=
  ⟨(h.1.trans ht.keep).mono (fun r hr => by
    rcases List.mem_append.mp hr with h | h
    · exact h
    · exact hrs r h), ht.mem.trans h.2.1, by rw [ht.get .r4 h4]; exact h.2.2⟩

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
  r4 : s.gpr .r4 = s₀.gpr .r4
  r7 : s.gpr .r7 = s₀.gpr .r7
  r8 : s.gpr .r8 = BitVec.ofNat 64 h.len
  r9 : s.gpr .r9 = BitVec.ofNat 64 (h.prefix.length + h.len)
  r6 : (s₀.gpr .r6).setWidth 32 = x
  id : Hash.ofId x.toNat = some h
  hk : (s₀.gpr .r5).toNat = k
  len : h.prefix.length + h.len + 11 ≤ k
  kle : k ≤ 1024

theorem write_ok {s₀ s : State} {x : BitVec 32} {h : Hash} {k : Nat} (hb : Buf s₀ k)
    (hp : WPre s₀ x h k s)
    (hr : ∀ j < h.len, InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .r7 + BitVec.ofNat 64 j) 1)
    (hd : ∀ j < h.len, ∀ i < k, s₀.gpr .r7 + BitVec.ofNat 64 j ≠ s₀.gpr .r4 + BitVec.ofNat 64 i) :
    WP isa write s fun t => Keep clob s₀ t ∧ t.gpr .r3 = 1 ∧
      t.mem = writeBytes s₀.mem (s₀.gpr .r4) ([0x00, 0x01] ++
        List.replicate (k - (h.prefix.length + h.len) - 3) 0xff ++ [0x00] ++ h.prefix ++
        Spec.Rsa.bytesAt s₀.mem (s₀.gpr .r7) h.len) := by
  have hkk : k < 2 ^ 64 := by have := hp.kle; omega
  have hlen := hp.len
  have h5 : s.gpr .r5 = s₀.gpr .r5 := hp.keep.get .r5
  have hw₀ : W s₀ [] s := ⟨hp.keep, by rw [hp.mem, writeBytes_nil], by rw [hp.r4]; simp⟩
  unfold write head
  rw [WP.seq_iff, List.append_assoc, WP.block_append_iff]
  refine WP.mono (putByte_ok hb (by simp; omega) hkk 0x00 hw₀) fun t₁ ⟨hw₁, hK₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (putByte_ok hb (by simp; omega) hkk 0x01 hw₁) fun t₂ ⟨hw₂, hK₂⟩ => ?_
  have hK₂' : Keep [.r0, .r4] s t₂ := (hK₁.trans hK₂).mono
  -- `r11 := k - tLen - 3`, `r0 := 0xff`
  refine wp_sub fun t₃ o₃ e₃ => wp_subi fun t₄ o₄ e₄ => wp_li (by decide) fun t₅ o₅ e₅ => wp_nil ?_
  have hO : Only [.r11, .r0] t₂ t₅ := (o₃.trans (o₄.trans o₅)).mono
  have hw₃ : W s₀ ([] ++ [0x00] ++ [0x01]) t₅ := W_only hw₂ hO
  have h11 : t₅.gpr .r11 = BitVec.ofNat 64 (k - (h.prefix.length + h.len) - 3) := by
    rw [o₅.get .r11, e₄, e₃, hK₂'.get .r5, hK₂'.get .r9, h5, hp.r9, ← ofNat_sub3 hlen hkk, ← hp.hk]
    simp
  -- `PS`
  refine WP.seq (WP.mono (fillLoop_ok hb hkk (n := k - (h.prefix.length + h.len) - 3) (by omega)
    (by simp; omega) hw₃ 0xff (by rw [e₅]; rfl) h11) fun t₆ ⟨hw₆, hK₆⟩ => ?_)
  -- `0x00`
  refine WP.seq (WP.mono (putByte_ok hb (by simp; omega) hkk 0x00 hw₆) fun t₇ ⟨hw₇, hK₇⟩ => ?_)
  have hK₇' : Keep [.r0, .r4, .r11] s t₇ := (((hK₂'.trans hO.keep).trans hK₆).trans hK₇).mono
  -- the prefix
  have h6₇ : (t₇.gpr .r6).setWidth 32 = x := by rw [hw₇.1.get .r6]; exact hp.r6
  have hcase : ∀ j (hj : j < hashes.length), x.toNat = 0 + j → ∀ u, Only [.r9] t₇ u →
      WP isa (prefixBytes hashes[j]) u fun t => W s₀ ([] ++ [0x00] ++ [0x01] ++
        List.replicate (k - (h.prefix.length + h.len) - 3) 0xff ++ [0x00] ++ h.prefix) t ∧
        Keep [.r0, .r4, .r9, .r11] s t := by
    intro j hj hxj u hu
    rw [Nat.zero_add] at hxj
    have hhj : hashes[j] = h := by
      have := hp.id; rw [hxj, ofId_hashes j hj] at this; exact Option.some.inj this
    rw [hhj]
    refine WP.mono (putBytes_ok hb hkk h.prefix (by simp; omega) (W_only hw₇ hu)) fun v ⟨hv, hKv⟩ =>
      ⟨hv, ((hK₇'.trans hu.keep).trans hKv).mono⟩
  have hdef : (∀ j < hashes.length, x.toNat ≠ 0 + j) → ∀ u, Only [.r9] t₇ u →
      WP isa (.block []) u fun t => W s₀ ([] ++ [0x00] ++ [0x01] ++
        List.replicate (k - (h.prefix.length + h.len) - 3) 0xff ++ [0x00] ++ h.prefix) t ∧
        Keep [.r0, .r4, .r9, .r11] s t := by
    intro hn u hu
    exfalso
    have hlt : x.toNat < hashes.length := by
      by_contra hc; have := hp.id; rw [ofId_ge (by omega)] at this; cases this
    exact hn _ hlt (by omega)
  refine WP.seq (WP.mono (dispatch_ok (fun h => prefixBytes h) (.block []) (s₀ := t₇) x h6₇
    hashes 0 (by decide) hcase hdef t₇ (Only.refl _ _)) fun t₈ ⟨hw₈, hK₈⟩ => ?_)
  refine WP.seq (WP.mono (copyLoop_ok hb hkk (len_pos h) (by simp; omega) hw₈
    (by rw [hK₈.get .r7, hp.r7]) (by rw [hK₈.get .r8, hp.r8]) hr hd) fun t₉ hw₉ => ?_)
  refine wp_li (by decide) fun t o e => wp_nil ⟨(hw₉.1.trans o.keep).mono, by rw [e]; rfl, ?_⟩
  rw [o.mem, hw₉.2.1]
  simp only [List.nil_append, List.append_assoc, List.cons_append]

/-! ## `encode` -/

/-- The encoding of `H` to `k` bytes for the hash function numbered `x`. -/
def encodeId (x : BitVec 32) (H : List Byte) (k : Nat) : Option (List Byte) :=
  match Hash.ofId x.toNat with
  | some h => Spec.RsaPkcs1Sig.encode h H k
  | none => none

theorem fail_ok (s : State) :
    WP isa fail s fun t => Only [.r3] s t ∧ t.gpr .r3 = 0 :=
  wp_li (by decide) fun t o e => wp_nil ⟨o, by rw [e]; rfl⟩

/-- The borrow of `a - b`, for numbers below `2^63`. -/
theorem borrow_ne {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    ((BitVec.ofNat 64 a - BitVec.ofNat 64 b) >>> 63 != 0) = decide (a < b) := by
  rw [ne_zero_iff, BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  apply decide_eq_decide.mpr
  constructor <;> intro h <;> omega

/-- What the encoding needs: the buffer of `k` bytes at `r4` is writable,
the hash value at `r7` (`r8` bytes) is readable and does not overlap it. -/
structure EPre (s₀ : State) (x : BitVec 32) (k : Nat) : Prop where
  r6 : (s₀.gpr .r6).setWidth 32 = x
  hk : (s₀.gpr .r5).toNat = k
  kle : k ≤ 1024
  buf : Buf s₀ k
  rd : ∀ j < (s₀.gpr .r8).toNat, InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .r7 + BitVec.ofNat 64 j) 1
  sep : ∀ j < (s₀.gpr .r8).toNat, ∀ i < k,
    s₀.gpr .r7 + BitVec.ofNat 64 j ≠ s₀.gpr .r4 + BitVec.ofNat 64 i

/-- The result `o` of `encode` in the state `t` it ends in: 1 and the
encoding in the buffer, or 0 and memory as it was. -/
def EOut (s₀ t : State) : Option (List Byte) → Prop
  | some em => t.gpr .r3 = 1 ∧ t.mem = writeBytes s₀.mem (s₀.gpr .r4) em
  | none => t.gpr .r3 = 0 ∧ t.mem = s₀.mem

/-- The result of `encode`. -/
def EPost (s₀ : State) (x : BitVec 32) (k : Nat) (t : State) : Prop :=
  Keep clob s₀ t ∧ EOut s₀ t (encodeId x (Spec.Rsa.bytesAt s₀.mem (s₀.gpr .r7) (s₀.gpr .r8).toNat) k)

theorem check1_ok (s : State) {L : Nat} (hL : L < 2 ^ 64) (h10 : s.gpr .r10 = BitVec.ofNat 64 L) :
    WP isa (.block [.sub .r11 .r8 .r10]) s fun t => Only [.r11] s t ∧
      isa.eval (.nonzero .d .r11) t = some (decide ((s.gpr .r8).toNat ≠ L)) :=
  wp_sub fun t o e => wp_nil ⟨o, by
    rw [eval_nonzero, e, h10, ne_zero_iff, BitVec.toNat_sub, BitVec.toNat_ofNat]
    have := (s.gpr .r8).isLt
    exact congrArg some (decide_eq_decide.mpr (by constructor <;> intro h <;> omega))⟩

theorem check2_ok (s : State) {T k : Nat} (hT : T < 2 ^ 12) (h9 : s.gpr .r9 = BitVec.ofNat 64 T)
    (h5 : (s.gpr .r5).toNat = k) (hk : k ≤ 1024) :
    WP isa (.block [.addi .r11 .r9 11, .sub .r11 .r5 .r11, .lsr .d .r11 .r11 63]) s fun t =>
      Only [.r11] s t ∧ isa.eval (.nonzero .d .r11) t = some (decide (k < T + 11)) :=
  wp_addi fun t₁ o₁ e₁ => wp_sub fun t₂ o₂ e₂ => wp_lsr fun t₃ o₃ e₃ =>
    wp_nil ⟨(o₁.trans (o₂.trans o₃)).mono, by
      have e : t₂.gpr .r11 = BitVec.ofNat 64 k - BitVec.ofNat 64 (T + 11) := by
        rw [e₂, o₁.get .r5, e₁, h9, ← h5, BitVec.ofNat_toNat, BitVec.setWidth_eq]
        congr 1; apply BitVec.eq_of_toNat_eq; simp
      rw [eval_nonzero, e₃, e, borrow_ne (by omega) (by omega)]⟩

theorem encode_ok {s₀ : State} {x : BitVec 32} {k : Nat} (hp : EPre s₀ x k) :
    WP isa Impl.RsaPkcs1Sig.PPC64LE.encode s₀ (EPost s₀ x k) := by
  have hk := hp.hk
  have hkle := hp.kle
  let dl := (s₀.gpr .r8).toNat
  let H := Spec.Rsa.bytesAt s₀.mem (s₀.gpr .r7) dl
  have hHl : H.length = dl := bytesAt_length _ _ _
  have hfail : ∀ u, Only [.r9, .r10, .r11] s₀ u → encodeId x H k = none → WP isa fail u (EPost s₀ x k) :=
    fun u hu hE => WP.mono (fail_ok u) fun t ⟨o, e⟩ => ⟨(hu.keep.trans o.keep).mono, by
      show EOut s₀ t (encodeId x H k)
      rw [hE]; exact ⟨e, o.mem.trans hu.mem⟩⟩
  unfold Impl.RsaPkcs1Sig.PPC64LE.encode
  cases hid : Hash.ofId x.toNat with
  | none =>
    have hE : encodeId x H k = none := by simp [encodeId, hid]
    have hcase : ∀ j (hj : j < hashes.length), x.toNat = 0 + j → ∀ u, Only [.r9] s₀ u →
        WP isa (lens hashes[j]) u fun t => Only [.r9, .r10] s₀ t ∧ t.gpr .r9 = 2048 := by
      intro j hj hxj; rw [Nat.zero_add] at hxj; rw [hxj, ofId_hashes j hj] at hid; cases hid
    have hdef : (∀ j < hashes.length, x.toNat ≠ 0 + j) → ∀ u, Only [.r9] s₀ u →
        WP isa noLens u fun t => Only [.r9, .r10] s₀ t ∧ t.gpr .r9 = 2048 := by
      intro _ u hu
      exact wp_li (by decide) fun t₁ o₁ e₁ => wp_li (by decide) fun t₂ o₂ e₂ => wp_nil
        ⟨(hu.trans (o₁.trans o₂)).mono, by rw [o₂.get .r9, e₁]; rfl⟩
    refine WP.seq (WP.mono (dispatch_ok (fun h => lens h) noLens x hp.r6 hashes 0
      (by decide) hcase hdef s₀ (Only.refl _ _)) fun t₁ ⟨o₁, h9⟩ => ?_)
    refine WP.seq (WP.mono (wp_sub (is := []) fun t o e => wp_nil (Q := fun t => Only [.r11] t₁ t) o)
      fun t₂ o₂ => ?_)
    have hO : Only [.r9, .r10, .r11] s₀ t₂ := (o₁.trans o₂).mono
    refine ite_both ((t₂.gpr .r11) != 0) (eval_nonzero _ _) (hfail t₂ hO hE) ?_
    refine WP.seq (WP.mono (check2_ok t₂ (T := 2048) (by decide) (by rw [o₂.get .r9, h9]; rfl)
      (by rw [hO.get .r5, hk]) hkle) fun t₃ ⟨o₃, hz⟩ => ?_)
    exact WP.ite true (by rw [hz]; simp; omega)
      (fun _ => hfail t₃ ((hO.trans o₃).mono) hE) (by simp)
  | some h =>
    have hcase : ∀ j (hj : j < hashes.length), x.toNat = 0 + j → ∀ u, Only [.r9] s₀ u →
        WP isa (lens hashes[j]) u fun t => Only [.r9, .r10] s₀ t ∧
          t.gpr .r9 = BitVec.ofNat 64 (h.prefix.length + h.len) ∧ t.gpr .r10 = BitVec.ofNat 64 h.len := by
      intro j hj hxj u hu
      rw [Nat.zero_add] at hxj
      have hhj : hashes[j] = h := by rw [hxj, ofId_hashes j hj] at hid; exact Option.some.inj hid
      rw [hhj]
      exact WP.mono (lens_ok h u) fun t ⟨o, h9, h10⟩ => ⟨(hu.trans o).mono, h9, h10⟩
    have hdef : (∀ j < hashes.length, x.toNat ≠ 0 + j) → ∀ u, Only [.r9] s₀ u →
        WP isa noLens u fun t => Only [.r9, .r10] s₀ t ∧
          t.gpr .r9 = BitVec.ofNat 64 (h.prefix.length + h.len) ∧ t.gpr .r10 = BitVec.ofNat 64 h.len := by
      intro hn
      exfalso
      have hlt : x.toNat < hashes.length := by
        by_contra hc; rw [ofId_ge (by omega)] at hid; cases hid
      exact hn _ hlt (by omega)
    have hpl := prefix_length_le h
    refine WP.seq (WP.mono (dispatch_ok (fun h => lens h) noLens x hp.r6 hashes 0
      (by decide) hcase hdef s₀ (Only.refl _ _)) fun t₁ ⟨o₁, h9, h10⟩ => ?_)
    refine WP.seq (WP.mono (check1_ok t₁ (by omega) h10) fun t₂ ⟨o₂, hz₂⟩ => ?_)
    have hO : Only [.r9, .r10, .r11] s₀ t₂ := (o₁.trans o₂).mono
    rw [o₁.get .r8] at hz₂
    by_cases hdl : dl = h.len
    · refine WP.ite false (by rw [hz₂]; simp [dl] at hdl ⊢; omega) (by simp) (fun _ => ?_)
      refine WP.seq (WP.mono (check2_ok t₂ (T := h.prefix.length + h.len) (by omega)
        (by rw [o₂.get .r9, h9]) (by rw [hO.get .r5, hk]) hkle) fun t₃ ⟨o₃, hz⟩ => ?_)
      have hO₃ : Only [.r9, .r10, .r11] s₀ t₃ := (hO.trans o₃).mono
      by_cases hkl : k < h.prefix.length + h.len + 11
      · refine WP.ite true (by rw [hz]; simp [hkl]) (fun _ => hfail t₃ hO₃ ?_) (by simp)
        simp only [encodeId, hid, Spec.RsaPkcs1Sig.encode, digestInfo, List.length_append, hHl, hdl]
        simp [hkl]
      · refine WP.ite false (by rw [hz]; simp [hkl]) (by simp) (fun _ => ?_)
        have hw : WPre s₀ x h k t₃ := {
          keep := hO₃.keep.mono
          mem := hO₃.mem
          r4 := hO₃.get .r4
          r7 := hO₃.get .r7
          r8 := by rw [hO₃.get .r8, ← hdl]; simp [dl]
          r9 := by rw [o₃.get .r9, o₂.get .r9, h9]
          r6 := hp.r6
          id := hid
          hk := hk
          len := by omega
          kle := hkle }
        refine WP.mono (write_ok hp.buf hw (fun j hj => hp.rd j (by simp [dl] at hdl; omega))
          (fun j hj => hp.sep j (by simp [dl] at hdl; omega))) fun t ⟨hK, hax, hm⟩ => ⟨hK, ?_⟩
        have hE : encodeId x (Spec.Rsa.bytesAt s₀.mem (s₀.gpr .r7) (s₀.gpr .r8).toNat) k =
            some ([0x00, 0x01] ++ List.replicate (k - (h.prefix.length + h.len) - 3) 0xff ++ [0x00] ++
              h.prefix ++ Spec.Rsa.bytesAt s₀.mem (s₀.gpr .r7) h.len) := by
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

/-- `compare`: `r7` is zero exactly when the `n` bytes at `r4` and at `r5`
are equal. -/
theorem compare_ok {s : State} {n : Nat} (hn : 0 < n) (hn' : n < 2 ^ 64) (hc : s.gpr .r6 = BitVec.ofNat 64 n)
    (hr1 : ∀ j < n, InRegions (s.rd ++ s.wr) (s.gpr .r4 + BitVec.ofNat 64 j) 1)
    (hr2 : ∀ j < n, InRegions (s.rd ++ s.wr) (s.gpr .r5 + BitVec.ofNat 64 j) 1) :
    WP isa compare s fun t => Only [.r4, .r5, .r6, .r7, .r8, .r9] s t ∧
      (t.gpr .r7 = 0 ↔ Spec.Rsa.bytesAt s.mem (s.gpr .r4) n = Spec.Rsa.bytesAt s.mem (s.gpr .r5) n) ∧
      (t.gpr .r7).toNat < 256 := by
  let A := Spec.Rsa.bytesAt s.mem (s.gpr .r4) n
  let B := Spec.Rsa.bytesAt s.mem (s.gpr .r5) n
  refine WP.seq (wp_li (by decide) fun t₀ o₀ e₀ => wp_nil ?_)
  replace e₀ : t₀.gpr .r7 = 0 := by rw [e₀]; rfl
  refine WP.mono (wp_countdown (cnt := .r6) hn' hn (fun i t => Only [.r4, .r5, .r6, .r7, .r8, .r9] s t ∧
      (∃ c : Byte, t.gpr .r7 = c.setWidth 64 ∧ (c = 0 ↔ A.take i = B.take i)) ∧
      t.gpr .r4 = s.gpr .r4 + BitVec.ofNat 64 i ∧ t.gpr .r5 = s.gpr .r5 + BitVec.ofNat 64 i) ?_
    ⟨o₀.mono, ⟨0, by rw [e₀]; rfl, by simp⟩, by rw [o₀.get .r4]; simp, by rw [o₀.get .r5]; simp⟩
    (by rw [o₀.get .r6, hc])) fun t ⟨o, ⟨c, ec, hcz⟩, _, _⟩ => ⟨o, ?_, by rw [ec]; have := c.isLt; simp; omega⟩
  · intro i hi t ⟨o, ⟨c, ec, hcz⟩, h4, h5⟩ _
    have hR1 : InRegions (t.rd ++ t.wr) (t.gpr .r4 + BitVec.ofNat 64 0) 1 := by
      rw [h4, o.rd, o.wr, BitVec.add_zero]; exact hr1 _ hi
    refine wp_lbz rfl hR1 fun t₁ o₁ e₁ => ?_
    have hR2 : InRegions (t₁.rd ++ t₁.wr) (t₁.gpr .r5 + BitVec.ofNat 64 0) 1 := by
      rw [o₁.get .r5, h5, o₁.rd, o₁.wr, o.rd, o.wr, BitVec.add_zero]; exact hr2 _ hi
    refine wp_lbz rfl hR2 fun t₂ o₂ e₂ => ?_
    refine wp_xor fun t₃ o₃ e₃ => wp_or fun t₄ o₄ e₄ => wp_addi fun t₅ o₅ e₅ =>
      wp_addi fun t₆ o₆ e₆ => wp_subi fun t₇ o₇ e₇ => wp_nil ?_
    have hO : Only [.r8, .r9, .r7, .r4, .r5, .r6] t t₇ :=
      (o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans (o₆.trans o₇)))))).mono
    have hm : t.mem = s.mem := o.mem
    let a := s.mem (s.gpr .r4 + BitVec.ofNat 64 i)
    let b := s.mem (s.gpr .r5 + BitVec.ofNat 64 i)
    have ha : t₂.gpr .r8 = a.setWidth 64 := by
      rw [o₂.get .r8, e₁, h4, hm, BitVec.add_zero]
    have hb : t₂.gpr .r9 = b.setWidth 64 := by
      rw [e₂, o₁.get .r5, h5, o₁.mem, hm, BitVec.add_zero]
    refine ⟨⟨(o.trans hO).mono, ⟨c ||| (a ^^^ b), ?_, ?_⟩, ?_, ?_⟩, ?_⟩
    · rw [o₇.get .r7, o₆.get .r7, o₅.get .r7, e₄, e₃, o₃.get .r7, ha, hb, o₂.get .r7, o₁.get .r7, ec,
        BitVec.setWidth_or, BitVec.setWidth_xor]
    · have e : (c ||| (a ^^^ b) = 0) ↔ (c = 0 ∧ a = b) := by
        simp [BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff]
      rw [e, hcz, bytesAt_take_succ _ _ hi,
        bytesAt_take_succ _ _ hi, snoc_eq_iff (by simp [bytesAt_length])]
    · rw [o₇.get .r4, o₆.get .r4, e₅, o₄.get .r4, o₃.get .r4, o₂.get .r4, o₁.get .r4, h4, ofNat_succ']
    · rw [o₇.get .r5, e₆, o₅.get .r5, o₄.get .r5, o₃.get .r5, o₂.get .r5, o₁.get .r5, h5, ofNat_succ']
    · rw [e₇, o₆.get .r6, o₅.get .r6, o₄.get .r6, o₃.get .r6, o₂.get .r6, o₁.get .r6]
  · rw [ec, List.take_of_length_le (by simp [A, bytesAt_length]),
      List.take_of_length_le (by simp [B, bytesAt_length])] at *
    rw [← hcz]
    constructor
    · intro h; bv_omega
    · intro h; rw [h]; rfl

/-- The borrow of `x - 1`, for `x < 256`: whether `x` is 0. -/
theorem borrow1 {x : BitVec 64} (h : x.toNat < 256) :
    (x - BitVec.ofNat 64 1) >>> 63 = if x = 0 then 1 else 0 := by
  by_cases hx : x = 0
  · subst hx; decide
  · simp only [hx, ↓reduceIte]
    have : x.toNat ≠ 0 := fun h' => hx (BitVec.eq_of_toNat_eq (by simpa using h'))
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_sub]
    simp; omega

/-! ## The loops, at any address -/

/-- `fillLoop` writes `n` bytes `b` (the low byte of `r0`) from `r4 = p`,
counted down in `r11`, at any writable address. -/
theorem fill_ok {s : State} {p : Addr} {n : Nat} {b : Byte} (hn : 0 < n) (hn' : n < 2 ^ 64)
    (h4 : s.gpr .r4 = p) (h11 : s.gpr .r11 = BitVec.ofNat 64 n) (h0 : (s.gpr .r0).setWidth 8 = b)
    (hw : ∀ i < n, InRegions s.wr (p + BitVec.ofNat 64 i) 1) :
    WP isa fillLoop s fun t => Keep [.r4, .r11] s t ∧ t.mem = writeBytes s.mem p (List.replicate n b) := by
  refine WP.mono (wp_countdown (cnt := .r11) hn' hn
    (fun i t => Keep [.r4, .r11] s t ∧ t.mem = writeBytes s.mem p (List.replicate i b) ∧
      t.gpr .r4 = p + BitVec.ofNat 64 i) ?_ ⟨Keep.refl _ _, by simp [writeBytes_nil], by simp [h4]⟩ h11)
    fun t h => ⟨h.1, h.2.1⟩
  intro i hi t ⟨hK, hm, h4'⟩ _
  have hA : InRegions t.wr (t.gpr .r4 + BitVec.ofNat 64 0) 1 := by
    rw [h4', hK.wr, BitVec.add_zero]; exact hw _ hi
  refine wp_stb rfl hA fun s₁ m₁ => ?_
  refine wp_addi fun s₂ o₂ e₂ => ?_
  refine wp_subi fun s₃ o₃ e₃ => wp_nil ?_
  have hK' : Keep [.r4, .r11] t s₃ := (m₁.keep.trans (o₂.keep.trans o₃.keep)).mono
  refine ⟨⟨(hK.trans hK').mono, ?_, ?_⟩, ?_⟩
  · rw [o₃.mem, o₂.mem, m₁.mem, hK.get .r0, h0, h4', BitVec.add_zero, hm, List.replicate_succ',
      writeBytes_snoc _ _ _ _ (by simp; omega)]
    simp
  · rw [o₃.get .r4, e₂, m₁.gpr, h4', ofNat_succ']
  · rw [e₃, o₂.get .r11, m₁.gpr]

/-- `copyLoop` copies `n` bytes from `r7 = q` to `r4 = p`, counted down in
`r8`, the source readable, the destination writable and apart from it. -/
theorem copy_ok {s : State} {p q : Addr} {n : Nat} (hn : 0 < n) (hn' : n < 2 ^ 64)
    (h4 : s.gpr .r4 = p) (h7 : s.gpr .r7 = q) (h8 : s.gpr .r8 = BitVec.ofNat 64 n)
    (hr : ∀ j < n, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 j) 1)
    (hw : ∀ i < n, InRegions s.wr (p + BitVec.ofNat 64 i) 1)
    (hd : ∀ j < n, ∀ i < n, q + BitVec.ofNat 64 j ≠ p + BitVec.ofNat 64 i) :
    WP isa copyLoop s fun t => Keep [.r0, .r7, .r4, .r8] s t ∧
      t.mem = writeBytes s.mem p (Spec.Rsa.bytesAt s.mem q n) := by
  refine WP.mono (wp_countdown (cnt := .r8) hn' hn
    (fun i t => Keep [.r0, .r7, .r4, .r8] s t ∧
      t.mem = writeBytes s.mem p ((Spec.Rsa.bytesAt s.mem q n).take i) ∧
      t.gpr .r4 = p + BitVec.ofNat 64 i ∧ t.gpr .r7 = q + BitVec.ofNat 64 i) ?_
    ⟨Keep.refl _ _, by simp [writeBytes_nil], by simp [h4], by simp [h7]⟩ h8) fun t h => ⟨h.1, ?_⟩
  · intro i hi t ⟨hK, hm, h4', h7'⟩ _
    have hR : InRegions (t.rd ++ t.wr) (t.gpr .r7 + BitVec.ofNat 64 0) 1 := by
      rw [h7', hK.rd, hK.wr, BitVec.add_zero]; exact hr _ hi
    have hv : t.mem (q + BitVec.ofNat 64 i) = s.mem (q + BitVec.ofNat 64 i) := by
      rw [hm, writeBytes_out _ _ _ _ n (fun i' hi' => hd i hi i' hi')
        (by simp only [List.length_take, bytesAt_length]; omega)]
    refine wp_lbz rfl hR fun s₁ o₁ e₁ => ?_
    have hA : InRegions s₁.wr (s₁.gpr .r4 + BitVec.ofNat 64 0) 1 := by
      rw [o₁.wr, o₁.get .r4, h4', hK.wr, BitVec.add_zero]; exact hw _ hi
    refine wp_stb rfl hA fun s₂ m₂ => ?_
    refine wp_addi fun s₃ o₃ e₃ => ?_
    refine wp_addi fun s₄ o₄ e₄ => ?_
    refine wp_subi fun s₅ o₅ e₅ => wp_nil ?_
    have hK' : Keep [.r0, .r7, .r4, .r8] t s₅ :=
      (o₁.keep.trans (m₂.keep.trans (o₃.keep.trans (o₄.keep.trans o₅.keep)))).mono
    have hlt : ((Spec.Rsa.bytesAt s.mem q n).take i).length = i := by
      simp [bytesAt_length]; omega
    refine ⟨⟨(hK.trans hK').mono, ?_, ?_, ?_⟩, ?_⟩
    · rw [o₅.mem, o₄.mem, o₃.mem, m₂.mem, e₁, o₁.mem, h7']
      simp only [BitVec.add_zero]
      rw [hv, byte_setWidth64, o₁.get .r4, h4', hm, bytesAt_take_succ _ _ hi,
        writeBytes_snoc _ _ _ _ (by omega), hlt]
    · rw [o₅.get .r4, e₄, o₃.get .r4, m₂.gpr, o₁.get .r4, h4', ofNat_succ']
    · rw [o₅.get .r7, o₄.get .r7, e₃, m₂.gpr, o₁.get .r7, h7', ofNat_succ']
    · rw [e₅, o₄.get .r8, o₃.get .r8, m₂.gpr, o₁.get .r8]
  · rw [List.take_of_length_le (by simp [bytesAt_length])] at h
    exact h.2.1

end VG.Proof.RsaPkcs1Sig.PPC64LE
