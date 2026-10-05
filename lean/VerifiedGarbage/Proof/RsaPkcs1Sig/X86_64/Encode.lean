import VerifiedGarbage.Impl.RsaPkcs1Sig.X86_64.Encode
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Spec.Rsa.Contract

/-!
# EMSA-PKCS1-v1_5 encoding on x86-64: correctness

`encode_ok`: from a state whose `r8` points to `k` writable bytes, `rsi` to
the hash value, which does not overlap them, `encode` returns 1 and writes
the encoding of the value (`Spec.RsaPkcs1Sig.encode`) to the buffer if it
exists, and returns 0 and leaves memory as it was if not.
-/

namespace VG.Proof.RsaPkcs1Sig.X86_64

open VG VG.X86_64 VG.Impl.RsaPkcs1Sig.X86_64 Spec.RsaPkcs1Sig
open VG.Proof.MlKem.X86_64 VG.WriteBytes

/-- The registers `encode` writes. -/
def clob : List Reg := [.rax, .rsi, .rdi, .r9, .r10, .r11]

/-- The buffer has been written with `acc` so far, and `rdi` points after it. -/
def W (s₀ : State) (acc : List Byte) (s : State) : Prop :=
  Keep clob s₀ s ∧ s.mem = writeBytes s₀.mem (s₀.gpr .r8) acc ∧
    s.gpr .rdi = s₀.gpr .r8 + BitVec.ofNat 64 acc.length

/-- The buffer's bytes are writable. -/
def Buf (s₀ : State) (k : Nat) : Prop :=
  ∀ i < k, InRegions s₀.wr (s₀.gpr .r8 + BitVec.ofNat 64 i) 1

theorem ea0 (s : State) (r : Reg) : s.ea { base := r } = s.gpr r := by
  simp [State.ea]

theorem byte_setWidth (b : Byte) : ((b.setWidth 32).setWidth 64).setWidth 8 = b := by
  apply BitVec.eq_of_toNat_eq; simp

theorem byte_setWidth64 (b : Byte) : (b.setWidth 64).setWidth 8 = b := by
  apply BitVec.eq_of_toNat_eq; simp

theorem ofNat_succ (a : Addr) (n : Nat) :
    a + BitVec.ofNat 64 n + 1 = a + BitVec.ofNat 64 (n + 1) := by
  rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp

theorem putByte_ok {s₀ s : State} {k : Nat} (hb : Buf s₀ k) {acc : List Byte} (hl : acc.length < k)
    (hk : k < 2 ^ 64) (b : Byte) (h : W s₀ acc s) :
    WP isa (.block (putByte b)) s fun t => W s₀ (acc ++ [b]) t ∧ Keep [.rax, .rdi] s t := by
  obtain ⟨hK, hm, hdi⟩ := h
  have hA : InRegions s.wr (s.gpr .rdi) 1 := by
    rw [hdi, hK.2.2]; exact hb _ hl
  refine WP.mono (WP.keep [.rax, .rdi] (Q := fun t => t.mem = (s.mem.writeW (s.gpr .rdi) b) ∧
      t.gpr .rdi = s.gpr .rdi + 1) (by
    xrun [putByte, ea0, hA, byte_setWidth]) rfl) fun t ⟨⟨hm', hdi'⟩, hK'⟩ => ⟨⟨(hK.trans hK').mono
      (by simp [clob]), ?_, ?_⟩, hK'⟩
  · rw [hm', hm, hdi, writeBytes_snoc _ _ _ _ (by omega)]
  · rw [hdi', hdi, List.length_append, List.length_singleton, ofNat_succ]

theorem putBytes_ok {s₀ : State} {k : Nat} (hb : Buf s₀ k) (hk : k < 2 ^ 64) (bs : List Byte) :
    ∀ {acc : List Byte} {s : State}, acc.length + bs.length ≤ k → W s₀ acc s →
      WP isa (.block (putBytes bs)) s fun t => W s₀ (acc ++ bs) t ∧ Keep [.rax, .rdi] s t := by
  induction bs with
  | nil => intro acc s _ h; exact WP.block_nil ⟨by simpa using h, Keep.refl _ _⟩
  | cons b bs ih =>
    intro acc s hl h
    simp only [putBytes, List.flatMap_cons] at ih ⊢
    rw [WP.block_append_iff]
    refine WP.mono (putByte_ok hb (by simp at hl; omega) hk b h) fun t ⟨ht, hk₁⟩ => ?_
    refine WP.mono (ih (acc := acc ++ [b]) (s := t) (by simp at hl ⊢; omega) ht) fun u ⟨hu, hk₂⟩ =>
      ⟨by simpa using hu, (hk₁.trans hk₂).mono (by simp)⟩

/-- `PS`: `n` bytes `b` (in `rax`; `0xff` for `PS`), counted down in `r10`. -/
theorem psLoop_ok {s₀ s : State} {k : Nat} (hb : Buf s₀ k) (hk : k < 2 ^ 64) {acc : List Byte}
    {n : Nat} (hn : 0 < n) (hl : acc.length + n ≤ k) (h : W s₀ acc s) (b : Byte)
    (hax : s.gpr .rax = b.setWidth 64) (hc : s.gpr .r10 = BitVec.ofNat 64 n) :
    WP isa psLoop s fun t => W s₀ (acc ++ List.replicate n b) t ∧ Keep [.rdi, .r10] s t := by
  refine wp_countdown (cnt := .r10) (by omega) hn
    (fun i t => W s₀ (acc ++ List.replicate i b) t ∧ t.gpr .rax = b.setWidth 64 ∧ Keep [.rdi, .r10] s t) ?_
    (fun _ h => ⟨h.1, h.2.2⟩) ⟨by simpa using h, hax, Keep.refl _ _⟩ hc
  intro i hi t ⟨⟨hK, hm, hdi⟩, hax, hKs⟩ _
  have hA : InRegions t.wr (t.gpr .rdi) 1 := by
    rw [hdi, hK.2.2]; exact hb _ (by simp; omega)
  refine WP.mono (WP.keep [.rdi, .r10] (Q := fun t' => t'.mem = (t.mem.writeW (t.gpr .rdi) b) ∧
      t'.gpr .rdi = t.gpr .rdi + 1 ∧ t'.gpr .rax = b.setWidth 64 ∧ t'.gpr .r10 = t.gpr .r10 - 1 ∧
      t'.zf = some (t.gpr .r10 - 1 == 0)) (by
    xrun [psLoop, ea0, hA, hax, byte_setWidth64]) rfl) fun t' ⟨⟨hm', hdi', hax', hc', hz⟩, hK'⟩ =>
      ⟨⟨⟨(hK.trans hK').mono (by simp [clob]), ?_, ?_⟩, hax', (hKs.trans hK').mono (by simp)⟩, hc', hz⟩
  · rw [hm', hm, hdi, List.replicate_succ', ← List.append_assoc,
      writeBytes_snoc _ _ _ _ (by simp; omega)]
  · rw [hdi', hdi, ofNat_succ]; simp [List.replicate_succ', Nat.add_assoc]

theorem bytesAt_take_succ (m : Mem) (p : Addr) {n i : Nat} (hi : i < n) :
    (Spec.Rsa.bytesAt m p n).take (i + 1) =
      (Spec.Rsa.bytesAt m p n).take i ++ [m (p + BitVec.ofNat 64 i)] := by
  simp only [Spec.Rsa.bytesAt]
  rw [← List.map_take, ← List.map_take, List.take_range, List.take_range, Nat.min_eq_left (by omega),
    Nat.min_eq_left (by omega), List.range_succ, List.map_append]
  rfl

/-- The byte at `a`, outside the buffer, is kept by writing it. -/
theorem writeBytes_out (m : Mem) (q a : Addr) (xs : List Byte) (k : Nat)
    (hd : ∀ i < k, a ≠ q + BitVec.ofNat 64 i) (hl : xs.length ≤ k) : writeBytes m q xs a = m a := by
  simp only [writeBytes]
  split
  · rename_i h
    exact absurd (show a = q + BitVec.ofNat 64 (a - q).toNat by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega) (hd _ (by omega))
  · rfl

/-- The hash value: `n` bytes from `rsi`, counted down in `r9`. -/
theorem copyLoop_ok {s₀ s : State} {k : Nat} (hb : Buf s₀ k) (hk : k < 2 ^ 64) {acc : List Byte}
    {n : Nat} (hn : 0 < n) (hl : acc.length + n ≤ k) (h : W s₀ acc s)
    (hsi : s.gpr .rsi = s₀.gpr .rsi) (hc : s.gpr .r9 = BitVec.ofNat 64 n)
    (hr : ∀ j < n, InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rsi + BitVec.ofNat 64 j) 1)
    (hd : ∀ j < n, ∀ i < k, s₀.gpr .rsi + BitVec.ofNat 64 j ≠ s₀.gpr .r8 + BitVec.ofNat 64 i) :
    WP isa copyLoop s (W s₀ (acc ++ Spec.Rsa.bytesAt s₀.mem (s₀.gpr .rsi) n)) := by
  have hn' : n < 2 ^ 64 := by omega
  refine wp_countdown (cnt := .r9) hn' hn
    (fun i t => W s₀ (acc ++ (Spec.Rsa.bytesAt s₀.mem (s₀.gpr .rsi) n).take i) t ∧
      t.gpr .rsi = s₀.gpr .rsi + BitVec.ofNat 64 i) ?_ (fun t h => ?_)
    ⟨by simpa using h, by rw [hsi]; simp⟩ hc
  · intro i hi t ⟨⟨hK, hm, hdi⟩, hsi'⟩ _
    have hlt : (acc ++ (Spec.Rsa.bytesAt s₀.mem (s₀.gpr .rsi) n).take i).length = acc.length + i := by
      simp [Spec.Rsa.bytesAt]; omega
    have hA : InRegions t.wr (t.gpr .rdi) 1 := by
      rw [hdi, hK.2.2, hlt]; exact hb _ (by omega)
    have hR : InRegions (t.rd ++ t.wr) (t.gpr .rsi) 1 := by
      rw [hsi', hK.2.1, hK.2.2]; exact hr _ hi
    have hv : t.mem (t.gpr .rsi) = s₀.mem (s₀.gpr .rsi + BitVec.ofNat 64 i) := by
      rw [hm, hsi', writeBytes_out _ _ _ _ k (hd i hi) (by omega)]
    refine WP.mono (WP.keep [.rax, .rsi, .rdi, .r9] (Q := fun t' =>
        t'.mem = (t.mem.writeW (t.gpr .rdi) (s₀.mem (s₀.gpr .rsi + BitVec.ofNat 64 i))) ∧
        t'.gpr .rdi = t.gpr .rdi + 1 ∧ t'.gpr .rsi = t.gpr .rsi + 1 ∧ t'.gpr .r9 = t.gpr .r9 - 1 ∧
        t'.zf = some (t.gpr .r9 - 1 == 0)) (by
      xrun [copyLoop, ea0, hA, hR, hv, byte_setWidth64]) rfl)
      fun t' ⟨⟨hm', hdi', hsi'', hc', hz⟩, hK'⟩ =>
        ⟨⟨⟨(hK.trans hK').mono (by simp [clob]), ?_, ?_⟩, ?_⟩, hc', hz⟩
    · rw [hm', hm, hdi, bytesAt_take_succ _ _ hi, ← List.append_assoc,
        writeBytes_snoc _ _ _ _ (by omega)]
    · rw [hdi', hdi, ofNat_succ, bytesAt_take_succ _ _ hi]
      simp only [List.length_append, List.length_take, List.length_singleton, Spec.Rsa.bytesAt,
        List.length_map, List.length_range]
      congr 2
    · rw [hsi'', hsi', ofNat_succ]
  · rw [List.take_of_length_le (by simp [Spec.Rsa.bytesAt])] at h
    exact h.1

theorem sub_beq32 (a b : BitVec 32) : (a - b == 0) = (a == b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  bv_omega

/-- `s'` is `s` but for the flags. -/
def SameF (s s' : State) : Prop := s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr

theorem cmp_ok (s : State) (i : Nat) :
    WP isa (.block [.alu32 .cmp .rdx (.imm (BitVec.ofNat 32 i))]) s fun t => SameF s t ∧
      t.zf = some ((s.gpr .rdx).setWidth 32 == BitVec.ofNat 32 i) := by
  xrun
  exact ⟨⟨rfl, rfl, rfl, rfl⟩, sub_beq32 _ _⟩

/-- `dispatch c d hs i`: `c (i + j) h` if `rdx`'s low 32 bits are `i + j`
for the `j`-th function `h` of `hs`, `d` if they are none of them, from a
state but for the flags. -/
theorem dispatch_ok (c : Nat → Hash → Prog isa) (d : Prog isa) {Q : State → Prop} {s₀ : State}
    (x : BitVec 32) (hx : (s₀.gpr .rdx).setWidth 32 = x) :
    ∀ (hs : List Hash) (i : Nat), i + hs.length < 2 ^ 32 →
      (∀ j (h : j < hs.length), x.toNat = i + j → ∀ s, SameF s₀ s → WP isa (c (i + j) hs[j]) s Q) →
      ((∀ j < hs.length, x.toNat ≠ i + j) → ∀ s, SameF s₀ s → WP isa d s Q) →
      ∀ s, SameF s₀ s → WP isa (dispatch c d hs i) s Q := by
  intro hs
  induction hs with
  | nil => intro i _ _ hd s hs; exact hd (fun _ h => absurd h (Nat.not_lt_zero _)) s hs
  | cons h hs ih =>
    intro i hi hc hd s hs₀
    refine WP.seq (WP.mono (cmp_ok s i) fun t ⟨ht, hz⟩ => ?_)
    have hst : SameF s₀ t := ⟨ht.1.trans hs₀.1, ht.2.1.trans hs₀.2.1, ht.2.2.1.trans hs₀.2.2.1,
      ht.2.2.2.trans hs₀.2.2.2⟩
    have hrdx : (s.gpr .rdx).setWidth 32 = x := by rw [hs₀.1]; exact hx
    rw [hrdx] at hz
    by_cases he : x.toNat = i
    · have hxe : x = BitVec.ofNat 32 i := by
        apply BitVec.eq_of_toNat_eq; rw [he, BitVec.toNat_ofNat]; simp at hi; omega
      refine WP.ite true (by simp [eval, hz, hxe]) (fun _ => ?_) (by simp)
      exact hc 0 (by simp) (by simpa using he) t hst
    · have hxe : x ≠ BitVec.ofNat 32 i := by
        intro h'; apply he; rw [h', BitVec.toNat_ofNat]; simp at hi; omega
      refine WP.ite false (by simp [eval, hz, hxe]) (by simp) (fun _ => ?_)
      refine ih (i + 1) (by simp at hi; omega) (fun j hj hxj t' ht' => ?_) (fun hn t' ht' => ?_) t hst
      · have := hc (j + 1) (by simp; omega) (by omega) t' ht'
        simpa [Nat.add_assoc, Nat.add_comm 1 j] using this
      · refine hd (fun j hj => ?_) t' ht'
        cases j with
        | zero => simpa using he
        | succ j => have := hn j (by simp at hj; omega); omega

/-! ## The hash functions' numbers -/

theorem ofId_hashes : ∀ j (h : j < hashes.length), Hash.ofId j = some hashes[j] := by decide

theorem ofId_ge {j : Nat} (h : hashes.length ≤ j) : Hash.ofId j = none := by
  unfold Hash.ofId; split <;> simp_all [hashes]

theorem hashes_length : hashes.length = 12 := rfl

theorem setWidth_ofNat32 {v : Nat} (h : v < 2 ^ 32) :
    (BitVec.ofNat 32 v).setWidth 64 = BitVec.ofNat 64 v := by
  apply BitVec.eq_of_toNat_eq; simp; omega

theorem prefix_length_le (h : Hash) : h.prefix.length + h.len ≤ 83 := by cases h <;> decide

/-- `tLen` and `hLen` into `r10` and `r11`. -/
theorem lens_ok (h : Hash) (s : State) :
    WP isa (lens h) s fun t => t.mem = s.mem ∧ Keep [.r10, .r11] s t ∧
      t.gpr .r10 = BitVec.ofNat 64 (h.prefix.length + h.len) ∧ t.gpr .r11 = BitVec.ofNat 64 h.len := by
  have := prefix_length_le h
  refine WP.mono (WP.keep [.r10, .r11] (Q := fun t => t.mem = s.mem ∧
      t.gpr .r10 = BitVec.ofNat 64 (h.prefix.length + h.len) ∧ t.gpr .r11 = BitVec.ofNat 64 h.len) (by
    xrun [lens, setWidth_ofNat32 (show h.prefix.length + h.len < 2 ^ 32 by omega),
      setWidth_ofNat32 (show h.len < 2 ^ 32 by omega)]) rfl) fun t ⟨⟨hm, h10, h11⟩, hK⟩ =>
    ⟨hm, hK, h10, h11⟩

theorem W_sameF {s₀ s t : State} {acc : List Byte} (h : W s₀ acc s) (ht : SameF s t) : W s₀ acc t :=
  ⟨⟨fun r hr => by rw [ht.1]; exact h.1.1 r hr, ht.2.2.1.trans h.1.2.1, ht.2.2.2.trans h.1.2.2⟩,
    ht.2.1.trans h.2.1, by rw [ht.1]; exact h.2.2⟩

theorem ofNat_sub3 {k t : Nat} (h : t + 11 ≤ k) (hk : k < 2 ^ 64) :
    BitVec.ofNat 64 k - BitVec.ofNat 64 t - 3 = BitVec.ofNat 64 (k - t - 3) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  have : (3 : BitVec 64).toNat = 3 := rfl
  rw [this]; omega

/-- What `write` needs: the state after the checks, for the hash function
`h` (numbered `x`), a value of `hLen` bytes and `k ≥ tLen + 11`. -/
structure WPre (s₀ : State) (x : BitVec 32) (h : Hash) (k : Nat) (s : State) : Prop where
  keep : Keep clob s₀ s
  mem : s.mem = s₀.mem
  rsi : s.gpr .rsi = s₀.gpr .rsi
  r9 : s.gpr .r9 = BitVec.ofNat 64 h.len
  r10 : s.gpr .r10 = BitVec.ofNat 64 (h.prefix.length + h.len)
  rdx : (s₀.gpr .rdx).setWidth 32 = x
  id : Hash.ofId x.toNat = some h
  hk : (s₀.gpr .rcx).toNat = k
  len : h.prefix.length + h.len + 11 ≤ k
  kle : k ≤ 1024

theorem write_ok {s₀ s : State} {x : BitVec 32} {h : Hash} {k : Nat} (hb : Buf s₀ k)
    (hp : WPre s₀ x h k s)
    (hr : ∀ j < h.len, InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rsi + BitVec.ofNat 64 j) 1)
    (hd : ∀ j < h.len, ∀ i < k, s₀.gpr .rsi + BitVec.ofNat 64 j ≠ s₀.gpr .r8 + BitVec.ofNat 64 i) :
    WP isa write s fun t => Keep clob s₀ t ∧ t.gpr .rax = 1 ∧
      t.mem = writeBytes s₀.mem (s₀.gpr .r8) ([0x00, 0x01] ++
        List.replicate (k - (h.prefix.length + h.len) - 3) 0xff ++ [0x00] ++ h.prefix ++
        Spec.Rsa.bytesAt s₀.mem (s₀.gpr .rsi) h.len) := by
  have hkk : k < 2 ^ 64 := by have := hp.kle; omega
  have hlen := hp.len
  have hcx : s.gpr .rcx = s₀.gpr .rcx := hp.keep.gpr (by decide)
  have h8 : s.gpr .r8 = s₀.gpr .r8 := hp.keep.gpr (by decide)
  -- `rdi := r8`
  have w0 : WP isa (.block [.mov .rdi (.reg .r8)]) s fun t => W s₀ [] t ∧ Keep [.rdi] s t := by
    refine WP.mono (WP.keep [.rdi] (Q := fun t => t.mem = s.mem ∧ t.gpr .rdi = s.gpr .r8) (by xrun) rfl)
      fun t ⟨⟨hm, hdi⟩, hK⟩ => ⟨⟨(hp.keep.trans hK).mono (by simp [clob]), by
        rw [hm, hp.mem, writeBytes_nil], by rw [hdi, h8]; simp⟩, hK⟩
  unfold write head
  rw [WP.seq_iff, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono w0 fun t₀ ⟨hw₀, hK₀⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (putByte_ok hb (by simp; omega) hkk 0x00 hw₀) fun t₁ ⟨hw₁, hK₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (putByte_ok hb (by simp; omega) hkk 0x01 hw₁) fun t₂ ⟨hw₂, hK₂⟩ => ?_
  have hK₂' : Keep [.rax, .rdi] s t₂ := ((hK₀.trans hK₁).trans hK₂).mono (by simp)
  have h10 : t₂.gpr .r10 = BitVec.ofNat 64 (h.prefix.length + h.len) := by rw [hK₂'.gpr (by decide), hp.r10]
  have hc2 : t₂.gpr .rcx = BitVec.ofNat 64 k := by rw [hK₂'.gpr (by decide), hcx, ← hp.hk]; simp
  -- `r10 := k - tLen - 3`, `rax := 0xff`
  refine WP.mono (WP.keep [.rax, .r10] (Q := fun t => t.mem = t₂.mem ∧
      t.gpr .r10 = BitVec.ofNat 64 (k - (h.prefix.length + h.len) - 3) ∧ t.gpr .rax = 0xff) (by
    xrun [h10, hc2, ofNat_sub3 hlen hkk]) rfl) fun t₃ ⟨⟨hm₃, h10₃, hax₃⟩, hK₃⟩ => ?_
  have hw₃ : W s₀ ([] ++ [0x00] ++ [0x01]) t₃ :=
    ⟨(hw₂.1.trans hK₃).mono (by simp [clob]), hm₃.trans hw₂.2.1, by rw [hK₃.gpr (by decide)]; exact hw₂.2.2⟩
  -- `PS`
  refine WP.seq (WP.mono (psLoop_ok hb hkk (n := k - (h.prefix.length + h.len) - 3) (by omega)
    (by simp; omega) hw₃ 0xff (by rw [hax₃]; rfl) h10₃) fun t₄ ⟨hw₄, hK₄⟩ => ?_)
  -- `0x00`
  refine WP.seq (WP.mono (putByte_ok hb (by simp; omega) hkk 0x00 hw₄) fun t₅ ⟨hw₅, hK₅⟩ => ?_)
  have hK₅' : Keep [.rax, .rdi, .r10] s t₅ := ((((hK₂'.trans hK₃).trans hK₄).trans hK₅)).mono (by simp)
  -- the prefix
  have hrdx₅ : (t₅.gpr .rdx).setWidth 32 = x := by rw [hw₅.1.gpr (by decide)]; exact hp.rdx
  have hcase : ∀ j (hj : j < hashes.length), x.toNat = 0 + j → ∀ u, SameF t₅ u →
      WP isa (prefixBytes hashes[j]) u fun t => W s₀ ([] ++ [0x00] ++ [0x01] ++
        List.replicate (k - (h.prefix.length + h.len) - 3) 0xff ++ [0x00] ++ h.prefix) t ∧
        Keep [.rax, .rdi, .r10] s t := by
    intro j hj hxj u hu
    rw [Nat.zero_add] at hxj
    have hhj : hashes[j] = h := by
      have := hp.id; rw [hxj, ofId_hashes j hj] at this; exact Option.some.inj this
    rw [hhj]
    refine WP.mono (putBytes_ok hb hkk h.prefix (by simp; omega) (W_sameF hw₅ hu)) fun v ⟨hv, hKv⟩ =>
      ⟨hv, ?_⟩
    exact ⟨fun r hr => by
        rw [hKv.gpr (by simp at hr ⊢; exact ⟨hr.1, hr.2.1⟩), hu.1]; exact hK₅'.gpr hr,
      hKv.2.1.trans (hu.2.2.1.trans hK₅'.2.1), hKv.2.2.trans (hu.2.2.2.trans hK₅'.2.2)⟩
  have hdef : (∀ j < hashes.length, x.toNat ≠ 0 + j) → ∀ u, SameF t₅ u →
      WP isa (.block []) u fun t => W s₀ ([] ++ [0x00] ++ [0x01] ++
        List.replicate (k - (h.prefix.length + h.len) - 3) 0xff ++ [0x00] ++ h.prefix) t ∧
        Keep [.rax, .rdi, .r10] s t := by
    intro hn u hu
    exfalso
    have hlt : x.toNat < hashes.length := by
      by_contra hc; have := hp.id; rw [ofId_ge (by omega)] at this; cases this
    exact hn _ hlt (by omega)
  refine WP.seq (WP.mono (dispatch_ok (fun _ h => prefixBytes h) (.block []) (s₀ := t₅) x hrdx₅ hashes 0
    (by decide) hcase hdef t₅ ⟨rfl, rfl, rfl, rfl⟩) fun t₆ ⟨hw₆, hK₆⟩ => ?_)
  have hlen0 : 0 < h.len := by cases h <;> decide
  refine WP.seq (WP.mono (copyLoop_ok hb hkk hlen0 (by simp; omega) hw₆
    (by rw [hK₆.gpr (by decide), hp.rsi]) (by rw [hK₆.gpr (by decide), hp.r9]) hr hd) fun t₇ hw₇ => ?_)
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = t₇.mem ∧ t.gpr .rax = 1) (by xrun) rfl)
    fun t ⟨⟨hm, hax⟩, hK⟩ => ⟨(hw₇.1.trans hK).mono (by simp [clob]), hax, ?_⟩
  rw [hm, hw₇.2.1]
  simp only [List.nil_append, List.append_assoc, List.cons_append]

/-! ## `encode` -/

/-- The encoding of `H` to `k` bytes for the hash function numbered `x`. -/
def encodeId (x : BitVec 32) (H : List Byte) (k : Nat) : Option (List Byte) :=
  match Hash.ofId x.toNat with
  | some h => Spec.RsaPkcs1Sig.encode h H k
  | none => none

theorem sub_beq64 (a b : BitVec 64) : (a - b == 0) = (a == b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  bv_omega

theorem fail_ok (s : State) :
    WP isa fail s fun t => Keep [.rax] s t ∧ t.mem = s.mem ∧ t.gpr .rax = 0 := by
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s.mem ∧ t.gpr .rax = 0) (by xrun [fail]) rfl)
    fun t ⟨h, hK⟩ => ⟨hK, h⟩

theorem Keep.sameF {rs : List Reg} {s t u : State} (h : Keep rs s t) (ht : SameF t u) : Keep rs s u :=
  ⟨fun r hr => by rw [ht.1]; exact h.1 r hr, ht.2.2.1.trans h.2.1, ht.2.2.2.trans h.2.2⟩

theorem ite_both {c : Cond} {th el : Prog isa} {s : State} {Q : State → Prop} (b : Bool)
    (hc : isa.eval c s = some b) (h₁ : WP isa th s Q) (h₂ : WP isa el s Q) : WP isa (.ite c th el) s Q := by
  cases b
  · exact WP.ite false hc (by simp) (fun _ => h₂)
  · exact WP.ite true hc (fun _ => h₁) (by simp)

theorem cmpLen_ok (s : State) :
    WP isa (.block [.alu .cmp .r9 (.reg .r11)]) s fun t => SameF s t ∧
      t.zf = some (s.gpr .r9 == s.gpr .r11) := by
  xrun
  exact ⟨⟨rfl, rfl, rfl, rfl⟩, sub_beq64 _ _⟩

theorem sx11 : BitVec.signExtend 64 (11 : BitVec 32) = 11 := by decide

theorem cmpK_ok (s : State) :
    WP isa (.block [.mov .rax (.reg .r10), .alu .add .rax (.imm 11), .alu .cmp .rcx (.reg .rax)]) s
      fun t => Keep [.rax] s t ∧ t.mem = s.mem ∧
        t.cf = some (decide ((s.gpr .rcx).toNat < (s.gpr .r10 + 11).toNat)) := by
  refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t => t.mem = s.mem ∧ t.gpr .rcx = s.gpr .rcx ∧
        t.cf = some (decide ((s.gpr .rcx).toNat < (s.gpr .r10 + 11).toNat))) (by xrun [sx11]) (by rfl))
    fun t ⟨⟨hm, hc, hcf⟩, hK⟩ => ⟨⟨fun r hr => by
      by_cases h : r = .rcx
      · subst h; exact hc
      · exact hK.gpr (by simp at hr ⊢; exact ⟨hr, h⟩), hK.2⟩, hm, hcf⟩

/-- What the encoding needs: the buffer of `k` bytes at `r8` is writable,
the hash value at `rsi` (`r9` bytes) is readable and does not overlap it. -/
structure EPre (s₀ : State) (x : BitVec 32) (k : Nat) : Prop where
  rdx : (s₀.gpr .rdx).setWidth 32 = x
  hk : (s₀.gpr .rcx).toNat = k
  kle : k ≤ 1024
  buf : Buf s₀ k
  rd : ∀ j < (s₀.gpr .r9).toNat, InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rsi + BitVec.ofNat 64 j) 1
  sep : ∀ j < (s₀.gpr .r9).toNat, ∀ i < k,
    s₀.gpr .rsi + BitVec.ofNat 64 j ≠ s₀.gpr .r8 + BitVec.ofNat 64 i

/-- The result of `encode`: 1 and the encoding in the buffer, or 0 and
memory as it was. -/
def EPost (s₀ : State) (x : BitVec 32) (k : Nat) (t : State) : Prop :=
  Keep clob s₀ t ∧
    match encodeId x (Spec.Rsa.bytesAt s₀.mem (s₀.gpr .rsi) (s₀.gpr .r9).toNat) k with
    | some em => t.gpr .rax = 1 ∧ t.mem = writeBytes s₀.mem (s₀.gpr .r8) em
    | none => t.gpr .rax = 0 ∧ t.mem = s₀.mem

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (Spec.Rsa.bytesAt m p n).length = n := by
  simp [Spec.Rsa.bytesAt]

theorem encode_ok {s₀ : State} {x : BitVec 32} {k : Nat} (hp : EPre s₀ x k) :
    WP isa Impl.RsaPkcs1Sig.X86_64.encode s₀ (EPost s₀ x k) := by
  have hkk : k < 2 ^ 64 := by have := hp.kle; omega
  have hk := hp.hk
  have hkle := hp.kle
  let dl := (s₀.gpr .r9).toNat
  let H := Spec.Rsa.bytesAt s₀.mem (s₀.gpr .rsi) dl
  unfold Impl.RsaPkcs1Sig.X86_64.encode
  cases hid : Hash.ofId x.toNat with
  | none =>
    have hE : encodeId x H k = none := by simp [encodeId, hid]
    -- No hash function: `tLen := 2048`, and the length check fails.
    have hcase : ∀ j (hj : j < hashes.length), x.toNat = 0 + j → ∀ u, SameF s₀ u →
        WP isa (lens hashes[j]) u fun t => Keep clob s₀ t ∧ t.mem = s₀.mem ∧ t.gpr .r10 = 2048 := by
      intro j hj hxj; rw [Nat.zero_add] at hxj; rw [hxj, ofId_hashes j hj] at hid; cases hid
    have hdef : (∀ j < hashes.length, x.toNat ≠ 0 + j) → ∀ u, SameF s₀ u →
        WP isa noLens u fun t => Keep clob s₀ t ∧ t.mem = s₀.mem ∧ t.gpr .r10 = 2048 := by
      intro _ u hu
      refine WP.mono (WP.keep [.r10, .r11] (Q := fun t => t.mem = u.mem ∧ t.gpr .r10 = 2048)
        (by xrun [noLens]) rfl) fun t ⟨⟨hm, h10⟩, hK⟩ => ⟨⟨fun r hr => by
          rw [hK.gpr (by simp [clob] at hr ⊢; exact ⟨hr.2.2.2.2.1, hr.2.2.2.2.2⟩), hu.1],
          hK.2.1.trans hu.2.2.1, hK.2.2.trans hu.2.2.2⟩, hm.trans hu.2.1, h10⟩
    refine WP.seq (WP.mono (dispatch_ok (fun _ h => lens h) noLens x hp.rdx hashes 0 (by decide) hcase hdef s₀
      ⟨rfl, rfl, rfl, rfl⟩) fun t₁ ⟨hK₁, hm₁, h10⟩ => ?_)
    refine WP.seq (WP.mono (cmpLen_ok t₁) fun t₂ ⟨hs₂, hz₂⟩ => ?_)
    have hK₂ : Keep clob s₀ t₂ := Keep.sameF hK₁ hs₂
    have hfail : ∀ u, Keep clob s₀ u → u.mem = s₀.mem → WP isa fail u (EPost s₀ x k) := fun u hKu hmu =>
      WP.mono (fail_ok u) fun t ⟨hK, hm, hax⟩ => ⟨(hKu.trans hK).mono (by simp [clob]), by
        rw [show encodeId x _ k = none from hE]; exact ⟨hax, hm.trans hmu⟩⟩
    refine ite_both (!(t₁.gpr .r9 == t₁.gpr .r11)) (by simp only [eval, hz₂]; rfl)
      (hfail t₂ hK₂ (hs₂.2.1.trans hm₁)) ?_
    refine WP.seq (WP.mono (cmpK_ok t₂) fun t₃ ⟨hK₃, hm₃, hcf⟩ => ?_)
    have hcx : t₂.gpr .rcx = s₀.gpr .rcx := hK₂.gpr (by decide)
    have h10' : t₂.gpr .r10 = 2048 := by rw [hs₂.1]; exact h10
    rw [hcx, h10', hk] at hcf
    refine WP.ite true (by
      simp only [eval, hcf, show ((2048 : BitVec 64) + 11).toNat = 2059 from rfl]; simp; omega) (fun _ => hfail t₃
      ((hK₂.trans hK₃).mono (by simp [clob])) (hm₃.trans (hs₂.2.1.trans hm₁))) (by simp)
  | some h =>
    have hcase : ∀ j (hj : j < hashes.length), x.toNat = 0 + j → ∀ u, SameF s₀ u →
        WP isa (lens hashes[j]) u fun t => Keep clob s₀ t ∧ t.mem = s₀.mem ∧
          t.gpr .rsi = s₀.gpr .rsi ∧ t.gpr .r9 = s₀.gpr .r9 ∧
          t.gpr .r10 = BitVec.ofNat 64 (h.prefix.length + h.len) ∧ t.gpr .r11 = BitVec.ofNat 64 h.len := by
      intro j hj hxj u hu
      rw [Nat.zero_add] at hxj
      have hhj : hashes[j] = h := by rw [hxj, ofId_hashes j hj] at hid; exact Option.some.inj hid
      rw [hhj]
      refine WP.mono (lens_ok h u) fun t ⟨hm, hK, h10, h11⟩ => ⟨⟨fun r hr => by
          rw [hK.gpr (by simp [clob] at hr ⊢; exact ⟨hr.2.2.2.2.1, hr.2.2.2.2.2⟩), hu.1],
          hK.2.1.trans hu.2.2.1, hK.2.2.trans hu.2.2.2⟩, hm.trans hu.2.1,
        by rw [hK.gpr (by decide), hu.1], by rw [hK.gpr (by decide), hu.1], h10, h11⟩
    have hdef : (∀ j < hashes.length, x.toNat ≠ 0 + j) → ∀ u, SameF s₀ u →
        WP isa noLens u fun t => Keep clob s₀ t ∧ t.mem = s₀.mem ∧
          t.gpr .rsi = s₀.gpr .rsi ∧ t.gpr .r9 = s₀.gpr .r9 ∧
          t.gpr .r10 = BitVec.ofNat 64 (h.prefix.length + h.len) ∧ t.gpr .r11 = BitVec.ofNat 64 h.len := by
      intro hn
      exfalso
      have hlt : x.toNat < hashes.length := by
        by_contra hc; rw [ofId_ge (by omega)] at hid; cases hid
      exact hn _ hlt (by omega)
    refine WP.seq (WP.mono (dispatch_ok (fun _ h => lens h) noLens x hp.rdx hashes 0 (by decide) hcase hdef s₀
      ⟨rfl, rfl, rfl, rfl⟩) fun t₁ ⟨hK₁, hm₁, hsi₁, h9₁, h10, h11⟩ => ?_)
    refine WP.seq (WP.mono (cmpLen_ok t₁) fun t₂ ⟨hs₂, hz₂⟩ => ?_)
    have hK₂ : Keep clob s₀ t₂ := Keep.sameF hK₁ hs₂
    have hHl : H.length = dl := bytesAt_length _ _ _
    have hfail : ∀ u, Keep clob s₀ u → u.mem = s₀.mem → Spec.RsaPkcs1Sig.encode h H k = none →
        WP isa fail u (EPost s₀ x k) := fun u hKu hmu hE =>
      WP.mono (fail_ok u) fun t ⟨hK, hm, hax⟩ => ⟨(hKu.trans hK).mono (by simp [clob]), by
        rw [show encodeId x _ k = none by simp only [encodeId, hid]; exact hE]; exact ⟨hax, hm.trans hmu⟩⟩
    have h9 : t₁.gpr .r9 = BitVec.ofNat 64 dl := by rw [h9₁]; simp [dl]
    by_cases hdl : dl = h.len
    · refine WP.ite false (by simp [eval, hz₂, h9, h11, hdl]) (by simp) (fun _ => ?_)
      refine WP.seq (WP.mono (cmpK_ok t₂) fun t₃ ⟨hK₃, hm₃, hcf⟩ => ?_)
      have hcx : t₂.gpr .rcx = s₀.gpr .rcx := hK₂.gpr (by decide)
      have h10' : t₂.gpr .r10 = BitVec.ofNat 64 (h.prefix.length + h.len) := by rw [hs₂.1]; exact h10
      have hpl := prefix_length_le h
      rw [hcx, h10', hk, show (BitVec.ofNat 64 (h.prefix.length + h.len) + 11).toNat =
        h.prefix.length + h.len + 11 by simp; omega] at hcf
      by_cases hkl : k < h.prefix.length + h.len + 11
      · refine WP.ite true (by simp [eval, hcf, hkl]) (fun _ => hfail t₃ ((hK₂.trans hK₃).mono
          (by simp [clob])) (hm₃.trans (hs₂.2.1.trans hm₁)) ?_) (by simp)
        simp only [Spec.RsaPkcs1Sig.encode, digestInfo, List.length_append, hHl, hdl]
        simp [hkl]
      · refine WP.ite false (by simp [eval, hcf, hkl]) (by simp) (fun _ => ?_)
        have hw : WPre s₀ x h k t₃ := {
          keep := (hK₂.trans hK₃).mono (by simp [clob])
          mem := hm₃.trans (hs₂.2.1.trans hm₁)
          rsi := by rw [hK₃.gpr (by decide), hs₂.1, hsi₁]
          r9 := by rw [hK₃.gpr (by decide), hs₂.1, h9, hdl]
          r10 := by rw [hK₃.gpr (by decide), h10']
          rdx := hp.rdx
          id := hid
          hk := hk
          len := by omega
          kle := hkle }
        refine WP.mono (write_ok hp.buf hw (fun j hj => hp.rd j (by omega))
          (fun j hj => hp.sep j (by omega))) fun t ⟨hK, hax, hm⟩ => ⟨hK, ?_⟩
        have hE : encodeId x (Spec.Rsa.bytesAt s₀.mem (s₀.gpr .rsi) (s₀.gpr .r9).toNat) k =
            some ([0x00, 0x01] ++ List.replicate (k - (h.prefix.length + h.len) - 3) 0xff ++ [0x00] ++
              h.prefix ++ Spec.Rsa.bytesAt s₀.mem (s₀.gpr .rsi) h.len) := by
          show encodeId x H k = _
          simp only [encodeId, hid, Spec.RsaPkcs1Sig.encode, digestInfo, List.length_append, hHl, hdl]
          simp [hkl, H, dl, hdl]
        rw [hE]
        exact ⟨hax, hm⟩
    · have hne : ¬ (BitVec.ofNat 64 dl == BitVec.ofNat 64 h.len) = true := by
        simp only [beq_iff_eq]; intro h'
        have := congrArg BitVec.toNat h'
        have hdl' : dl < 2 ^ 64 := (s₀.gpr .r9).isLt
        have : h.len < 2 ^ 64 := by have := prefix_length_le h; omega
        simp only [BitVec.toNat_ofNat] at *; omega
      have hev : isa.eval .ne t₂ = some true := by
        simp only [eval, hz₂, h9, h11, Bool.eq_false_iff.mpr hne]; rfl
      refine WP.ite true hev (fun _ => hfail t₂ hK₂ (hs₂.2.1.trans hm₁) ?_) (by simp)
      simp [Spec.RsaPkcs1Sig.encode, hHl, hdl]

/-! ## The buffer after `encode` -/

/-- Writing `xs` at `q` changes memory only there. -/
theorem frame_writeBytes (m : Mem) (q : Addr) (xs : List Byte) :
    Frame [⟨q, xs.length⟩] m (writeBytes m q xs) := by
  intro x hx
  have h := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at h
  simp only [writeBytes]
  rw [ite_eq_right_iff.mpr (fun h' => absurd h' (by omega))]

/-- The bytes written. -/
theorem bytesAt_writeBytes (m : Mem) (q : Addr) (xs : List Byte) (hl : xs.length < 2 ^ 64) :
    Spec.Rsa.bytesAt (writeBytes m q xs) q xs.length = xs := by
  apply List.ext_getElem (by simp [Spec.Rsa.bytesAt])
  intro i h₁ h₂
  simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, writeBytes,
    Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega)]
  rw [ite_eq_left_iff.mpr (fun h' => absurd h₂ h')]
  simp [List.getD_eq_getElem?_getD, h₂]

/-- Two addresses of disjoint regions differ. -/
theorem ne_of_disjoint {p q : Addr} {n k : Nat} (hd : (⟨p, n⟩ : Region).Disjoint ⟨q, k⟩) (hn : n ≤ 2 ^ 64)
    (hk : k ≤ 2 ^ 64) {j i : Nat} (hj : j < n) (hi : i < k) :
    p + BitVec.ofNat 64 j ≠ q + BitVec.ofNat 64 i := by
  intro h
  refine hd (p + BitVec.ofNat 64 j) ?_ ?_
  · simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]; omega
  · rw [h]; simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]; omega

end VG.Proof.RsaPkcs1Sig.X86_64
