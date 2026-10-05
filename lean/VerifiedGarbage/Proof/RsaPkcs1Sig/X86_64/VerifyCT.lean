import VerifiedGarbage.Impl.RsaPkcs1Sig.X86_64.Encode
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Ct.Common
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.Pub
import VerifiedGarbage.Proof.RsaPkcs1Sig.Recover
import VerifiedGarbage.Proof.Bignum.X86_64.AdxCT

/- Proofs formerly in `VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.Encode`. -/
section

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
  VG.Proof.MlKem.X86_64.Keep VG.Proof.RsaPkcs1Sig.X86_64.clob s₀ s ∧ s.mem = VG.WriteBytes.writeBytes s₀.mem (s₀.gpr .r8) acc ∧
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

theorem putByte_ok {s₀ s : State} {k : Nat} (hb : VG.Proof.RsaPkcs1Sig.X86_64.Buf s₀ k) {acc : List Byte} (hl : acc.length < k)
    (hk : k < 2 ^ 64) (b : Byte) (h : VG.Proof.RsaPkcs1Sig.X86_64.W s₀ acc s) :
    WP isa (.block (putByte b)) s fun t => VG.Proof.RsaPkcs1Sig.X86_64.W s₀ (acc ++ [b]) t ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rdi] s t := by
  obtain ⟨hK, hm, hdi⟩ := h
  have hA : InRegions s.wr (s.gpr .rdi) 1 := by
    rw [hdi, hK.2.2]; exact hb _ hl
  refine WP.mono (WP.keep [.rax, .rdi] (Q := fun t => t.mem = (s.mem.writeW (s.gpr .rdi) b) ∧
      t.gpr .rdi = s.gpr .rdi + 1) (by
    xrun [putByte, VG.Proof.RsaPkcs1Sig.X86_64.ea0, hA, VG.Proof.RsaPkcs1Sig.X86_64.byte_setWidth]) rfl) fun t ⟨⟨hm', hdi'⟩, hK'⟩ => ⟨⟨(hK.trans hK').mono
      (by simp [VG.Proof.RsaPkcs1Sig.X86_64.clob]), ?_, ?_⟩, hK'⟩
  · rw [hm', hm, hdi, VG.WriteBytes.writeBytes_snoc _ _ _ _ (by omega)]
  · rw [hdi', hdi, List.length_append, List.length_singleton, VG.Proof.RsaPkcs1Sig.X86_64.ofNat_succ]

theorem putBytes_ok {s₀ : State} {k : Nat} (hb : VG.Proof.RsaPkcs1Sig.X86_64.Buf s₀ k) (hk : k < 2 ^ 64) (bs : List Byte) :
    ∀ {acc : List Byte} {s : State}, acc.length + bs.length ≤ k → VG.Proof.RsaPkcs1Sig.X86_64.W s₀ acc s →
      WP isa (.block (putBytes bs)) s fun t => VG.Proof.RsaPkcs1Sig.X86_64.W s₀ (acc ++ bs) t ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rdi] s t := by
  induction bs with
  | nil => intro acc s _ h; exact WP.block_nil ⟨by simpa using h, Keep.refl _ _⟩
  | cons b bs ih =>
    intro acc s hl h
    simp only [putBytes, List.flatMap_cons] at ih ⊢
    rw [WP.block_append_iff]
    refine WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.putByte_ok hb (by simp at hl; omega) hk b h) fun t ⟨ht, hk₁⟩ => ?_
    refine WP.mono (ih (acc := acc ++ [b]) (s := t) (by simp at hl ⊢; omega) ht) fun u ⟨hu, hk₂⟩ =>
      ⟨by simpa using hu, (hk₁.trans hk₂).mono (by simp)⟩

/-- `PS`: `n` bytes `b` (in `rax`; `0xff` for `PS`), counted down in `r10`. -/
theorem psLoop_ok {s₀ s : State} {k : Nat} (hb : VG.Proof.RsaPkcs1Sig.X86_64.Buf s₀ k) (hk : k < 2 ^ 64) {acc : List Byte}
    {n : Nat} (hn : 0 < n) (hl : acc.length + n ≤ k) (h : VG.Proof.RsaPkcs1Sig.X86_64.W s₀ acc s) (b : Byte)
    (hax : s.gpr .rax = b.setWidth 64) (hc : s.gpr .r10 = BitVec.ofNat 64 n) :
    WP isa psLoop s fun t => VG.Proof.RsaPkcs1Sig.X86_64.W s₀ (acc ++ List.replicate n b) t ∧ VG.Proof.MlKem.X86_64.Keep [.rdi, .r10] s t := by
  refine wp_countdown (cnt := .r10) (by omega) hn
    (fun i t => VG.Proof.RsaPkcs1Sig.X86_64.W s₀ (acc ++ List.replicate i b) t ∧ t.gpr .rax = b.setWidth 64 ∧ VG.Proof.MlKem.X86_64.Keep [.rdi, .r10] s t) ?_
    (fun _ h => ⟨h.1, h.2.2⟩) ⟨by simpa using h, hax, Keep.refl _ _⟩ hc
  intro i hi t ⟨⟨hK, hm, hdi⟩, hax, hKs⟩ _
  have hA : InRegions t.wr (t.gpr .rdi) 1 := by
    rw [hdi, hK.2.2]; exact hb _ (by simp; omega)
  refine WP.mono (WP.keep [.rdi, .r10] (Q := fun t' => t'.mem = (t.mem.writeW (t.gpr .rdi) b) ∧
      t'.gpr .rdi = t.gpr .rdi + 1 ∧ t'.gpr .rax = b.setWidth 64 ∧ t'.gpr .r10 = t.gpr .r10 - 1 ∧
      t'.zf = some (t.gpr .r10 - 1 == 0)) (by
    xrun [psLoop, VG.Proof.RsaPkcs1Sig.X86_64.ea0, hA, hax, VG.Proof.RsaPkcs1Sig.X86_64.byte_setWidth64]) rfl) fun t' ⟨⟨hm', hdi', hax', hc', hz⟩, hK'⟩ =>
      ⟨⟨⟨(hK.trans hK').mono (by simp [VG.Proof.RsaPkcs1Sig.X86_64.clob]), ?_, ?_⟩, hax', (hKs.trans hK').mono (by simp)⟩, hc', hz⟩
  · rw [hm', hm, hdi, List.replicate_succ', ← List.append_assoc,
      VG.WriteBytes.writeBytes_snoc _ _ _ _ (by simp; omega)]
  · rw [hdi', hdi, VG.Proof.RsaPkcs1Sig.X86_64.ofNat_succ]; simp [List.replicate_succ', Nat.add_assoc]

theorem bytesAt_take_succ (m : Mem) (p : Addr) {n i : Nat} (hi : i < n) :
    (Spec.Rsa.bytesAt m p n).take (i + 1) =
      (Spec.Rsa.bytesAt m p n).take i ++ [m (p + BitVec.ofNat 64 i)] := by
  simp only [Spec.Rsa.bytesAt]
  rw [← List.map_take, ← List.map_take, List.take_range, List.take_range, Nat.min_eq_left (by omega),
    Nat.min_eq_left (by omega), List.range_succ, List.map_append]
  rfl

/-- The byte at `a`, outside the buffer, is kept by writing it. -/
theorem writeBytes_out (m : Mem) (q a : Addr) (xs : List Byte) (k : Nat)
    (hd : ∀ i < k, a ≠ q + BitVec.ofNat 64 i) (hl : xs.length ≤ k) : VG.WriteBytes.writeBytes m q xs a = m a := by
  simp only [VG.WriteBytes.writeBytes]
  split
  · rename_i h
    exact absurd (show a = q + BitVec.ofNat 64 (a - q).toNat by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega) (hd _ (by omega))
  · rfl

/-- The hash value: `n` bytes from `rsi`, counted down in `r9`. -/
theorem copyLoop_ok {s₀ s : State} {k : Nat} (hb : VG.Proof.RsaPkcs1Sig.X86_64.Buf s₀ k) (hk : k < 2 ^ 64) {acc : List Byte}
    {n : Nat} (hn : 0 < n) (hl : acc.length + n ≤ k) (h : VG.Proof.RsaPkcs1Sig.X86_64.W s₀ acc s)
    (hsi : s.gpr .rsi = s₀.gpr .rsi) (hc : s.gpr .r9 = BitVec.ofNat 64 n)
    (hr : ∀ j < n, InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rsi + BitVec.ofNat 64 j) 1)
    (hd : ∀ j < n, ∀ i < k, s₀.gpr .rsi + BitVec.ofNat 64 j ≠ s₀.gpr .r8 + BitVec.ofNat 64 i) :
    WP isa copyLoop s (VG.Proof.RsaPkcs1Sig.X86_64.W s₀ (acc ++ Spec.Rsa.bytesAt s₀.mem (s₀.gpr .rsi) n)) := by
  have hn' : n < 2 ^ 64 := by omega
  refine wp_countdown (cnt := .r9) hn' hn
    (fun i t => VG.Proof.RsaPkcs1Sig.X86_64.W s₀ (acc ++ (Spec.Rsa.bytesAt s₀.mem (s₀.gpr .rsi) n).take i) t ∧
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
      rw [hm, hsi', VG.Proof.RsaPkcs1Sig.X86_64.writeBytes_out _ _ _ _ k (hd i hi) (by omega)]
    refine WP.mono (WP.keep [.rax, .rsi, .rdi, .r9] (Q := fun t' =>
        t'.mem = (t.mem.writeW (t.gpr .rdi) (s₀.mem (s₀.gpr .rsi + BitVec.ofNat 64 i))) ∧
        t'.gpr .rdi = t.gpr .rdi + 1 ∧ t'.gpr .rsi = t.gpr .rsi + 1 ∧ t'.gpr .r9 = t.gpr .r9 - 1 ∧
        t'.zf = some (t.gpr .r9 - 1 == 0)) (by
      xrun [copyLoop, VG.Proof.RsaPkcs1Sig.X86_64.ea0, hA, hR, hv, VG.Proof.RsaPkcs1Sig.X86_64.byte_setWidth64]) rfl)
      fun t' ⟨⟨hm', hdi', hsi'', hc', hz⟩, hK'⟩ =>
        ⟨⟨⟨(hK.trans hK').mono (by simp [VG.Proof.RsaPkcs1Sig.X86_64.clob]), ?_, ?_⟩, ?_⟩, hc', hz⟩
    · rw [hm', hm, hdi, VG.Proof.RsaPkcs1Sig.X86_64.bytesAt_take_succ _ _ hi, ← List.append_assoc,
        VG.WriteBytes.writeBytes_snoc _ _ _ _ (by omega)]
    · rw [hdi', hdi, VG.Proof.RsaPkcs1Sig.X86_64.ofNat_succ, VG.Proof.RsaPkcs1Sig.X86_64.bytesAt_take_succ _ _ hi]
      simp only [List.length_append, List.length_take, List.length_singleton, Spec.Rsa.bytesAt,
        List.length_map, List.length_range]
      congr 2
    · rw [hsi'', hsi', VG.Proof.RsaPkcs1Sig.X86_64.ofNat_succ]
  · rw [List.take_of_length_le (by simp [Spec.Rsa.bytesAt])] at h
    exact h.1

theorem sub_beq32 (a b : BitVec 32) : (a - b == 0) = (a == b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  bv_omega

/-- `s'` is `s` but for the flags. -/
def SameF (s s' : State) : Prop := s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr

theorem cmp_ok (s : State) (i : Nat) :
    WP isa (.block [.alu32 .cmp .rdx (.imm (BitVec.ofNat 32 i))]) s fun t => VG.Proof.RsaPkcs1Sig.X86_64.SameF s t ∧
      t.zf = some ((s.gpr .rdx).setWidth 32 == BitVec.ofNat 32 i) := by
  xrun
  exact ⟨⟨rfl, rfl, rfl, rfl⟩, VG.Proof.RsaPkcs1Sig.X86_64.sub_beq32 _ _⟩

/-- `dispatch c d hs i`: `c (i + j) h` if `rdx`'s low 32 bits are `i + j`
for the `j`-th function `h` of `hs`, `d` if they are none of them, from a
state but for the flags. -/
theorem dispatch_ok (c : Nat → Hash → Prog isa) (d : Prog isa) {Q : State → Prop} {s₀ : State}
    (x : BitVec 32) (hx : (s₀.gpr .rdx).setWidth 32 = x) :
    ∀ (hs : List Hash) (i : Nat), i + hs.length < 2 ^ 32 →
      (∀ j (h : j < hs.length), x.toNat = i + j → ∀ s, VG.Proof.RsaPkcs1Sig.X86_64.SameF s₀ s → WP isa (c (i + j) hs[j]) s Q) →
      ((∀ j < hs.length, x.toNat ≠ i + j) → ∀ s, VG.Proof.RsaPkcs1Sig.X86_64.SameF s₀ s → WP isa d s Q) →
      ∀ s, VG.Proof.RsaPkcs1Sig.X86_64.SameF s₀ s → WP isa (dispatch c d hs i) s Q := by
  intro hs
  induction hs with
  | nil => intro i _ _ hd s hs; exact hd (fun _ h => absurd h (Nat.not_lt_zero _)) s hs
  | cons h hs ih =>
    intro i hi hc hd s hs₀
    refine WP.seq (WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.cmp_ok s i) fun t ⟨ht, hz⟩ => ?_)
    have hst : VG.Proof.RsaPkcs1Sig.X86_64.SameF s₀ t := ⟨ht.1.trans hs₀.1, ht.2.1.trans hs₀.2.1, ht.2.2.1.trans hs₀.2.2.1,
      ht.2.2.2.trans hs₀.2.2.2⟩
    have hrdx : (s.gpr .rdx).setWidth 32 = x := by rw [hs₀.1]; exact hx
    rw [hrdx] at hz
    by_cases he : x.toNat = i
    · have hxe : x = BitVec.ofNat 32 i := by
        apply BitVec.eq_of_toNat_eq; rw [he, BitVec.toNat_ofNat]; simp at hi; omega
      refine WP.ite true (by simp [VG.X86_64.eval, hz, hxe]) (fun _ => ?_) (by simp)
      exact hc 0 (by simp) (by simpa using he) t hst
    · have hxe : x ≠ BitVec.ofNat 32 i := by
        intro h'; apply he; rw [h', BitVec.toNat_ofNat]; simp at hi; omega
      refine WP.ite false (by simp [VG.X86_64.eval, hz, hxe]) (by simp) (fun _ => ?_)
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
    WP isa (lens h) s fun t => t.mem = s.mem ∧ VG.Proof.MlKem.X86_64.Keep [.r10, .r11] s t ∧
      t.gpr .r10 = BitVec.ofNat 64 (h.prefix.length + h.len) ∧ t.gpr .r11 = BitVec.ofNat 64 h.len := by
  have := VG.Proof.RsaPkcs1Sig.X86_64.prefix_length_le h
  refine WP.mono (WP.keep [.r10, .r11] (Q := fun t => t.mem = s.mem ∧
      t.gpr .r10 = BitVec.ofNat 64 (h.prefix.length + h.len) ∧ t.gpr .r11 = BitVec.ofNat 64 h.len) (by
    xrun [lens, VG.Proof.RsaPkcs1Sig.X86_64.setWidth_ofNat32 (show h.prefix.length + h.len < 2 ^ 32 by omega),
      VG.Proof.RsaPkcs1Sig.X86_64.setWidth_ofNat32 (show h.len < 2 ^ 32 by omega)]) rfl) fun t ⟨⟨hm, h10, h11⟩, hK⟩ =>
    ⟨hm, hK, h10, h11⟩

theorem W_sameF {s₀ s t : State} {acc : List Byte} (h : VG.Proof.RsaPkcs1Sig.X86_64.W s₀ acc s) (ht : VG.Proof.RsaPkcs1Sig.X86_64.SameF s t) : VG.Proof.RsaPkcs1Sig.X86_64.W s₀ acc t :=
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
  keep : VG.Proof.MlKem.X86_64.Keep VG.Proof.RsaPkcs1Sig.X86_64.clob s₀ s
  mem : s.mem = s₀.mem
  rsi : s.gpr .rsi = s₀.gpr .rsi
  r9 : s.gpr .r9 = BitVec.ofNat 64 h.len
  r10 : s.gpr .r10 = BitVec.ofNat 64 (h.prefix.length + h.len)
  rdx : (s₀.gpr .rdx).setWidth 32 = x
  id : Hash.ofId x.toNat = some h
  hk : (s₀.gpr .rcx).toNat = k
  len : h.prefix.length + h.len + 11 ≤ k
  kle : k ≤ 1024

theorem write_ok {s₀ s : State} {x : BitVec 32} {h : Hash} {k : Nat} (hb : VG.Proof.RsaPkcs1Sig.X86_64.Buf s₀ k)
    (hp : VG.Proof.RsaPkcs1Sig.X86_64.WPre s₀ x h k s)
    (hr : ∀ j < h.len, InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rsi + BitVec.ofNat 64 j) 1)
    (hd : ∀ j < h.len, ∀ i < k, s₀.gpr .rsi + BitVec.ofNat 64 j ≠ s₀.gpr .r8 + BitVec.ofNat 64 i) :
    WP isa write s fun t => VG.Proof.MlKem.X86_64.Keep VG.Proof.RsaPkcs1Sig.X86_64.clob s₀ t ∧ t.gpr .rax = 1 ∧
      t.mem = VG.WriteBytes.writeBytes s₀.mem (s₀.gpr .r8) ([0x00, 0x01] ++
        List.replicate (k - (h.prefix.length + h.len) - 3) 0xff ++ [0x00] ++ h.prefix ++
        Spec.Rsa.bytesAt s₀.mem (s₀.gpr .rsi) h.len) := by
  have hkk : k < 2 ^ 64 := by have := hp.kle; omega
  have hlen := hp.len
  have hcx : s.gpr .rcx = s₀.gpr .rcx := hp.keep.gpr (by decide)
  have h8 : s.gpr .r8 = s₀.gpr .r8 := hp.keep.gpr (by decide)
  -- `rdi := r8`
  have w0 : WP isa (.block [.mov .rdi (.reg .r8)]) s fun t => VG.Proof.RsaPkcs1Sig.X86_64.W s₀ [] t ∧ VG.Proof.MlKem.X86_64.Keep [.rdi] s t := by
    refine WP.mono (WP.keep [.rdi] (Q := fun t => t.mem = s.mem ∧ t.gpr .rdi = s.gpr .r8) (by xrun) rfl)
      fun t ⟨⟨hm, hdi⟩, hK⟩ => ⟨⟨(hp.keep.trans hK).mono (by simp [VG.Proof.RsaPkcs1Sig.X86_64.clob]), by
        rw [hm, hp.mem, VG.WriteBytes.writeBytes_nil], by rw [hdi, h8]; simp⟩, hK⟩
  unfold write VG.Impl.RsaPkcs1Sig.X86_64.head
  rw [WP.seq_iff, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono w0 fun t₀ ⟨hw₀, hK₀⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.putByte_ok hb (by simp; omega) hkk 0x00 hw₀) fun t₁ ⟨hw₁, hK₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.putByte_ok hb (by simp; omega) hkk 0x01 hw₁) fun t₂ ⟨hw₂, hK₂⟩ => ?_
  have hK₂' : VG.Proof.MlKem.X86_64.Keep [.rax, .rdi] s t₂ := ((hK₀.trans hK₁).trans hK₂).mono (by simp)
  have h10 : t₂.gpr .r10 = BitVec.ofNat 64 (h.prefix.length + h.len) := by rw [hK₂'.gpr (by decide), hp.r10]
  have hc2 : t₂.gpr .rcx = BitVec.ofNat 64 k := by rw [hK₂'.gpr (by decide), hcx, ← hp.hk]; simp
  -- `r10 := k - tLen - 3`, `rax := 0xff`
  refine WP.mono (WP.keep [.rax, .r10] (Q := fun t => t.mem = t₂.mem ∧
      t.gpr .r10 = BitVec.ofNat 64 (k - (h.prefix.length + h.len) - 3) ∧ t.gpr .rax = 0xff) (by
    xrun [h10, hc2, VG.Proof.RsaPkcs1Sig.X86_64.ofNat_sub3 hlen hkk]) rfl) fun t₃ ⟨⟨hm₃, h10₃, hax₃⟩, hK₃⟩ => ?_
  have hw₃ : VG.Proof.RsaPkcs1Sig.X86_64.W s₀ ([] ++ [0x00] ++ [0x01]) t₃ :=
    ⟨(hw₂.1.trans hK₃).mono (by simp [VG.Proof.RsaPkcs1Sig.X86_64.clob]), hm₃.trans hw₂.2.1, by rw [hK₃.gpr (by decide)]; exact hw₂.2.2⟩
  -- `PS`
  refine WP.seq (WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.psLoop_ok hb hkk (n := k - (h.prefix.length + h.len) - 3) (by omega)
    (by simp; omega) hw₃ 0xff (by rw [hax₃]; rfl) h10₃) fun t₄ ⟨hw₄, hK₄⟩ => ?_)
  -- `0x00`
  refine WP.seq (WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.putByte_ok hb (by simp; omega) hkk 0x00 hw₄) fun t₅ ⟨hw₅, hK₅⟩ => ?_)
  have hK₅' : VG.Proof.MlKem.X86_64.Keep [.rax, .rdi, .r10] s t₅ := ((((hK₂'.trans hK₃).trans hK₄).trans hK₅)).mono (by simp)
  -- the prefix
  have hrdx₅ : (t₅.gpr .rdx).setWidth 32 = x := by rw [hw₅.1.gpr (by decide)]; exact hp.rdx
  have hcase : ∀ j (hj : j < hashes.length), x.toNat = 0 + j → ∀ u, VG.Proof.RsaPkcs1Sig.X86_64.SameF t₅ u →
      WP isa (prefixBytes hashes[j]) u fun t => VG.Proof.RsaPkcs1Sig.X86_64.W s₀ ([] ++ [0x00] ++ [0x01] ++
        List.replicate (k - (h.prefix.length + h.len) - 3) 0xff ++ [0x00] ++ h.prefix) t ∧
        VG.Proof.MlKem.X86_64.Keep [.rax, .rdi, .r10] s t := by
    intro j hj hxj u hu
    rw [Nat.zero_add] at hxj
    have hhj : hashes[j] = h := by
      have := hp.id; rw [hxj, VG.Proof.RsaPkcs1Sig.X86_64.ofId_hashes j hj] at this; exact Option.some.inj this
    rw [hhj]
    refine WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.putBytes_ok hb hkk h.prefix (by simp; omega) (VG.Proof.RsaPkcs1Sig.X86_64.W_sameF hw₅ hu)) fun v ⟨hv, hKv⟩ =>
      ⟨hv, ?_⟩
    exact ⟨fun r hr => by
        rw [hKv.gpr (by simp at hr ⊢; exact ⟨hr.1, hr.2.1⟩), hu.1]; exact hK₅'.gpr hr,
      hKv.2.1.trans (hu.2.2.1.trans hK₅'.2.1), hKv.2.2.trans (hu.2.2.2.trans hK₅'.2.2)⟩
  have hdef : (∀ j < hashes.length, x.toNat ≠ 0 + j) → ∀ u, VG.Proof.RsaPkcs1Sig.X86_64.SameF t₅ u →
      WP isa (.block []) u fun t => VG.Proof.RsaPkcs1Sig.X86_64.W s₀ ([] ++ [0x00] ++ [0x01] ++
        List.replicate (k - (h.prefix.length + h.len) - 3) 0xff ++ [0x00] ++ h.prefix) t ∧
        VG.Proof.MlKem.X86_64.Keep [.rax, .rdi, .r10] s t := by
    intro hn u hu
    exfalso
    have hlt : x.toNat < hashes.length := by
      by_contra hc; have := hp.id; rw [VG.Proof.RsaPkcs1Sig.X86_64.ofId_ge (by omega)] at this; cases this
    exact hn _ hlt (by omega)
  refine WP.seq (WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.dispatch_ok (fun _ h => prefixBytes h) (.block []) (s₀ := t₅) x hrdx₅ hashes 0
    (by decide) hcase hdef t₅ ⟨rfl, rfl, rfl, rfl⟩) fun t₆ ⟨hw₆, hK₆⟩ => ?_)
  have hlen0 : 0 < h.len := by cases h <;> decide
  refine WP.seq (WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.copyLoop_ok hb hkk hlen0 (by simp; omega) hw₆
    (by rw [hK₆.gpr (by decide), hp.rsi]) (by rw [hK₆.gpr (by decide), hp.r9]) hr hd) fun t₇ hw₇ => ?_)
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = t₇.mem ∧ t.gpr .rax = 1) (by xrun) rfl)
    fun t ⟨⟨hm, hax⟩, hK⟩ => ⟨(hw₇.1.trans hK).mono (by simp [VG.Proof.RsaPkcs1Sig.X86_64.clob]), hax, ?_⟩
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
    WP isa VG.Impl.RsaPkcs1Sig.X86_64.fail s fun t => VG.Proof.MlKem.X86_64.Keep [.rax] s t ∧ t.mem = s.mem ∧ t.gpr .rax = 0 := by
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s.mem ∧ t.gpr .rax = 0) (by xrun [VG.Impl.RsaPkcs1Sig.X86_64.fail]) rfl)
    fun t ⟨h, hK⟩ => ⟨hK, h⟩

theorem Keep.sameF {rs : List Reg} {s t u : State} (h : VG.Proof.MlKem.X86_64.Keep rs s t) (ht : VG.Proof.RsaPkcs1Sig.X86_64.SameF t u) : VG.Proof.MlKem.X86_64.Keep rs s u :=
  ⟨fun r hr => by rw [ht.1]; exact h.1 r hr, ht.2.2.1.trans h.2.1, ht.2.2.2.trans h.2.2⟩

theorem ite_both {c : Cond} {th el : Prog isa} {s : State} {Q : State → Prop} (b : Bool)
    (hc : isa.eval c s = some b) (h₁ : WP isa th s Q) (h₂ : WP isa el s Q) : WP isa (.ite c th el) s Q := by
  cases b
  · exact WP.ite false hc (by simp) (fun _ => h₂)
  · exact WP.ite true hc (fun _ => h₁) (by simp)

theorem cmpLen_ok (s : State) :
    WP isa (.block [.alu .cmp .r9 (.reg .r11)]) s fun t => VG.Proof.RsaPkcs1Sig.X86_64.SameF s t ∧
      t.zf = some (s.gpr .r9 == s.gpr .r11) := by
  xrun
  exact ⟨⟨rfl, rfl, rfl, rfl⟩, VG.Proof.RsaPkcs1Sig.X86_64.sub_beq64 _ _⟩

theorem sx11 : BitVec.signExtend 64 (11 : BitVec 32) = 11 := by decide

theorem cmpK_ok (s : State) :
    WP isa (.block [.mov .rax (.reg .r10), .alu .add .rax (.imm 11), .alu .cmp .rcx (.reg .rax)]) s
      fun t => VG.Proof.MlKem.X86_64.Keep [.rax] s t ∧ t.mem = s.mem ∧
        t.cf = some (decide ((s.gpr .rcx).toNat < (s.gpr .r10 + 11).toNat)) := by
  refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t => t.mem = s.mem ∧ t.gpr .rcx = s.gpr .rcx ∧
        t.cf = some (decide ((s.gpr .rcx).toNat < (s.gpr .r10 + 11).toNat))) (by xrun [VG.Proof.RsaPkcs1Sig.X86_64.sx11]) (by rfl))
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
  buf : VG.Proof.RsaPkcs1Sig.X86_64.Buf s₀ k
  rd : ∀ j < (s₀.gpr .r9).toNat, InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rsi + BitVec.ofNat 64 j) 1
  sep : ∀ j < (s₀.gpr .r9).toNat, ∀ i < k,
    s₀.gpr .rsi + BitVec.ofNat 64 j ≠ s₀.gpr .r8 + BitVec.ofNat 64 i

/-- The result `o` of `encode` in the state `t` it ends in: 1 and the
encoding in the buffer, or 0 and memory as it was. -/
def EOut (s₀ t : State) : Option (List Byte) → Prop
  | some em => t.gpr .rax = 1 ∧ t.mem = VG.WriteBytes.writeBytes s₀.mem (s₀.gpr .r8) em
  | none => t.gpr .rax = 0 ∧ t.mem = s₀.mem

/-- The result of `encode`. -/
def EPost (s₀ : State) (x : BitVec 32) (k : Nat) (t : State) : Prop :=
  VG.Proof.MlKem.X86_64.Keep VG.Proof.RsaPkcs1Sig.X86_64.clob s₀ t ∧ VG.Proof.RsaPkcs1Sig.X86_64.EOut s₀ t (VG.Proof.RsaPkcs1Sig.X86_64.encodeId x (Spec.Rsa.bytesAt s₀.mem (s₀.gpr .rsi) (s₀.gpr .r9).toNat) k)

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (Spec.Rsa.bytesAt m p n).length = n := by
  simp [Spec.Rsa.bytesAt]

theorem encode_ok {s₀ : State} {x : BitVec 32} {k : Nat} (hp : VG.Proof.RsaPkcs1Sig.X86_64.EPre s₀ x k) :
    WP isa Impl.RsaPkcs1Sig.X86_64.encode s₀ (VG.Proof.RsaPkcs1Sig.X86_64.EPost s₀ x k) := by
  have hkk : k < 2 ^ 64 := by have := hp.kle; omega
  have hk := hp.hk
  have hkle := hp.kle
  let dl := (s₀.gpr .r9).toNat
  let H := Spec.Rsa.bytesAt s₀.mem (s₀.gpr .rsi) dl
  unfold Impl.RsaPkcs1Sig.X86_64.encode
  cases hid : Hash.ofId x.toNat with
  | none =>
    have hE : VG.Proof.RsaPkcs1Sig.X86_64.encodeId x H k = none := by simp [VG.Proof.RsaPkcs1Sig.X86_64.encodeId, hid]
    -- No hash function: `tLen := 2048`, and the length check fails.
    have hcase : ∀ j (hj : j < hashes.length), x.toNat = 0 + j → ∀ u, VG.Proof.RsaPkcs1Sig.X86_64.SameF s₀ u →
        WP isa (lens hashes[j]) u fun t => VG.Proof.MlKem.X86_64.Keep VG.Proof.RsaPkcs1Sig.X86_64.clob s₀ t ∧ t.mem = s₀.mem ∧ t.gpr .r10 = 2048 := by
      intro j hj hxj; rw [Nat.zero_add] at hxj; rw [hxj, VG.Proof.RsaPkcs1Sig.X86_64.ofId_hashes j hj] at hid; cases hid
    have hdef : (∀ j < hashes.length, x.toNat ≠ 0 + j) → ∀ u, VG.Proof.RsaPkcs1Sig.X86_64.SameF s₀ u →
        WP isa noLens u fun t => VG.Proof.MlKem.X86_64.Keep VG.Proof.RsaPkcs1Sig.X86_64.clob s₀ t ∧ t.mem = s₀.mem ∧ t.gpr .r10 = 2048 := by
      intro _ u hu
      refine WP.mono (WP.keep [.r10, .r11] (Q := fun t => t.mem = u.mem ∧ t.gpr .r10 = 2048)
        (by xrun [noLens]) rfl) fun t ⟨⟨hm, h10⟩, hK⟩ => ⟨⟨fun r hr => by
          rw [hK.gpr (by simp [VG.Proof.RsaPkcs1Sig.X86_64.clob] at hr ⊢; exact ⟨hr.2.2.2.2.1, hr.2.2.2.2.2⟩), hu.1],
          hK.2.1.trans hu.2.2.1, hK.2.2.trans hu.2.2.2⟩, hm.trans hu.2.1, h10⟩
    refine WP.seq (WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.dispatch_ok (fun _ h => lens h) noLens x hp.rdx hashes 0 (by decide) hcase hdef s₀
      ⟨rfl, rfl, rfl, rfl⟩) fun t₁ ⟨hK₁, hm₁, h10⟩ => ?_)
    refine WP.seq (WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.cmpLen_ok t₁) fun t₂ ⟨hs₂, hz₂⟩ => ?_)
    have hK₂ : VG.Proof.MlKem.X86_64.Keep VG.Proof.RsaPkcs1Sig.X86_64.clob s₀ t₂ := Keep.sameF hK₁ hs₂
    have hfail : ∀ u, VG.Proof.MlKem.X86_64.Keep VG.Proof.RsaPkcs1Sig.X86_64.clob s₀ u → u.mem = s₀.mem → WP isa VG.Impl.RsaPkcs1Sig.X86_64.fail u (VG.Proof.RsaPkcs1Sig.X86_64.EPost s₀ x k) := fun u hKu hmu =>
      WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.fail_ok u) fun t ⟨hK, hm, hax⟩ => ⟨(hKu.trans hK).mono (by simp [VG.Proof.RsaPkcs1Sig.X86_64.clob]), by
        rw [show VG.Proof.RsaPkcs1Sig.X86_64.encodeId x _ k = none from hE]; exact ⟨hax, hm.trans hmu⟩⟩
    refine VG.Proof.RsaPkcs1Sig.X86_64.ite_both (!(t₁.gpr .r9 == t₁.gpr .r11)) (by simp only [VG.X86_64.eval, hz₂]; rfl)
      (hfail t₂ hK₂ (hs₂.2.1.trans hm₁)) ?_
    refine WP.seq (WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.cmpK_ok t₂) fun t₃ ⟨hK₃, hm₃, hcf⟩ => ?_)
    have hcx : t₂.gpr .rcx = s₀.gpr .rcx := hK₂.gpr (by decide)
    have h10' : t₂.gpr .r10 = 2048 := by rw [hs₂.1]; exact h10
    rw [hcx, h10', hk] at hcf
    refine WP.ite true (by
      simp only [VG.X86_64.eval, hcf, show ((2048 : BitVec 64) + 11).toNat = 2059 from rfl]; simp; omega) (fun _ => hfail t₃
      ((hK₂.trans hK₃).mono (by simp [VG.Proof.RsaPkcs1Sig.X86_64.clob])) (hm₃.trans (hs₂.2.1.trans hm₁))) (by simp)
  | some h =>
    have hcase : ∀ j (hj : j < hashes.length), x.toNat = 0 + j → ∀ u, VG.Proof.RsaPkcs1Sig.X86_64.SameF s₀ u →
        WP isa (lens hashes[j]) u fun t => VG.Proof.MlKem.X86_64.Keep VG.Proof.RsaPkcs1Sig.X86_64.clob s₀ t ∧ t.mem = s₀.mem ∧
          t.gpr .rsi = s₀.gpr .rsi ∧ t.gpr .r9 = s₀.gpr .r9 ∧
          t.gpr .r10 = BitVec.ofNat 64 (h.prefix.length + h.len) ∧ t.gpr .r11 = BitVec.ofNat 64 h.len := by
      intro j hj hxj u hu
      rw [Nat.zero_add] at hxj
      have hhj : hashes[j] = h := by rw [hxj, VG.Proof.RsaPkcs1Sig.X86_64.ofId_hashes j hj] at hid; exact Option.some.inj hid
      rw [hhj]
      refine WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.lens_ok h u) fun t ⟨hm, hK, h10, h11⟩ => ⟨⟨fun r hr => by
          rw [hK.gpr (by simp [VG.Proof.RsaPkcs1Sig.X86_64.clob] at hr ⊢; exact ⟨hr.2.2.2.2.1, hr.2.2.2.2.2⟩), hu.1],
          hK.2.1.trans hu.2.2.1, hK.2.2.trans hu.2.2.2⟩, hm.trans hu.2.1,
        by rw [hK.gpr (by decide), hu.1], by rw [hK.gpr (by decide), hu.1], h10, h11⟩
    have hdef : (∀ j < hashes.length, x.toNat ≠ 0 + j) → ∀ u, VG.Proof.RsaPkcs1Sig.X86_64.SameF s₀ u →
        WP isa noLens u fun t => VG.Proof.MlKem.X86_64.Keep VG.Proof.RsaPkcs1Sig.X86_64.clob s₀ t ∧ t.mem = s₀.mem ∧
          t.gpr .rsi = s₀.gpr .rsi ∧ t.gpr .r9 = s₀.gpr .r9 ∧
          t.gpr .r10 = BitVec.ofNat 64 (h.prefix.length + h.len) ∧ t.gpr .r11 = BitVec.ofNat 64 h.len := by
      intro hn
      exfalso
      have hlt : x.toNat < hashes.length := by
        by_contra hc; rw [VG.Proof.RsaPkcs1Sig.X86_64.ofId_ge (by omega)] at hid; cases hid
      exact hn _ hlt (by omega)
    refine WP.seq (WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.dispatch_ok (fun _ h => lens h) noLens x hp.rdx hashes 0 (by decide) hcase hdef s₀
      ⟨rfl, rfl, rfl, rfl⟩) fun t₁ ⟨hK₁, hm₁, hsi₁, h9₁, h10, h11⟩ => ?_)
    refine WP.seq (WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.cmpLen_ok t₁) fun t₂ ⟨hs₂, hz₂⟩ => ?_)
    have hK₂ : VG.Proof.MlKem.X86_64.Keep VG.Proof.RsaPkcs1Sig.X86_64.clob s₀ t₂ := Keep.sameF hK₁ hs₂
    have hHl : H.length = dl := VG.Proof.RsaPkcs1Sig.X86_64.bytesAt_length _ _ _
    have hfail : ∀ u, VG.Proof.MlKem.X86_64.Keep VG.Proof.RsaPkcs1Sig.X86_64.clob s₀ u → u.mem = s₀.mem → Spec.RsaPkcs1Sig.encode h H k = none →
        WP isa VG.Impl.RsaPkcs1Sig.X86_64.fail u (VG.Proof.RsaPkcs1Sig.X86_64.EPost s₀ x k) := fun u hKu hmu hE =>
      WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.fail_ok u) fun t ⟨hK, hm, hax⟩ => ⟨(hKu.trans hK).mono (by simp [VG.Proof.RsaPkcs1Sig.X86_64.clob]), by
        rw [show VG.Proof.RsaPkcs1Sig.X86_64.encodeId x _ k = none by simp only [VG.Proof.RsaPkcs1Sig.X86_64.encodeId, hid]; exact hE]; exact ⟨hax, hm.trans hmu⟩⟩
    have h9 : t₁.gpr .r9 = BitVec.ofNat 64 dl := by rw [h9₁]; simp [dl]
    by_cases hdl : dl = h.len
    · refine WP.ite false (by simp [VG.X86_64.eval, hz₂, h9, h11, hdl]) (by simp) (fun _ => ?_)
      refine WP.seq (WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.cmpK_ok t₂) fun t₃ ⟨hK₃, hm₃, hcf⟩ => ?_)
      have hcx : t₂.gpr .rcx = s₀.gpr .rcx := hK₂.gpr (by decide)
      have h10' : t₂.gpr .r10 = BitVec.ofNat 64 (h.prefix.length + h.len) := by rw [hs₂.1]; exact h10
      have hpl := VG.Proof.RsaPkcs1Sig.X86_64.prefix_length_le h
      rw [hcx, h10', hk, show (BitVec.ofNat 64 (h.prefix.length + h.len) + 11).toNat =
        h.prefix.length + h.len + 11 by simp; omega] at hcf
      by_cases hkl : k < h.prefix.length + h.len + 11
      · refine WP.ite true (by simp [VG.X86_64.eval, hcf, hkl]) (fun _ => hfail t₃ ((hK₂.trans hK₃).mono
          (by simp [VG.Proof.RsaPkcs1Sig.X86_64.clob])) (hm₃.trans (hs₂.2.1.trans hm₁)) ?_) (by simp)
        simp only [Spec.RsaPkcs1Sig.encode, digestInfo, List.length_append, hHl, hdl]
        simp [hkl]
      · refine WP.ite false (by simp [VG.X86_64.eval, hcf, hkl]) (by simp) (fun _ => ?_)
        have hw : VG.Proof.RsaPkcs1Sig.X86_64.WPre s₀ x h k t₃ := {
          keep := (hK₂.trans hK₃).mono (by simp [VG.Proof.RsaPkcs1Sig.X86_64.clob])
          mem := hm₃.trans (hs₂.2.1.trans hm₁)
          rsi := by rw [hK₃.gpr (by decide), hs₂.1, hsi₁]
          r9 := by rw [hK₃.gpr (by decide), hs₂.1, h9, hdl]
          r10 := by rw [hK₃.gpr (by decide), h10']
          rdx := hp.rdx
          id := hid
          hk := hk
          len := by omega
          kle := hkle }
        refine WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.write_ok hp.buf hw (fun j hj => hp.rd j (by omega))
          (fun j hj => hp.sep j (by omega))) fun t ⟨hK, hax, hm⟩ => ⟨hK, ?_⟩
        have hE : VG.Proof.RsaPkcs1Sig.X86_64.encodeId x (Spec.Rsa.bytesAt s₀.mem (s₀.gpr .rsi) (s₀.gpr .r9).toNat) k =
            some ([0x00, 0x01] ++ List.replicate (k - (h.prefix.length + h.len) - 3) 0xff ++ [0x00] ++
              h.prefix ++ Spec.Rsa.bytesAt s₀.mem (s₀.gpr .rsi) h.len) := by
          show VG.Proof.RsaPkcs1Sig.X86_64.encodeId x H k = _
          simp only [VG.Proof.RsaPkcs1Sig.X86_64.encodeId, hid, Spec.RsaPkcs1Sig.encode, digestInfo, List.length_append, hHl, hdl]
          simp [hkl, H, dl, hdl]
        rw [hE]
        exact ⟨hax, hm⟩
    · have hne : ¬ (BitVec.ofNat 64 dl == BitVec.ofNat 64 h.len) = true := by
        simp only [beq_iff_eq]; intro h'
        have := congrArg BitVec.toNat h'
        have hdl' : dl < 2 ^ 64 := (s₀.gpr .r9).isLt
        have : h.len < 2 ^ 64 := by have := VG.Proof.RsaPkcs1Sig.X86_64.prefix_length_le h; omega
        simp only [BitVec.toNat_ofNat] at *; omega
      have hev : isa.eval .ne t₂ = some true := by
        simp only [VG.X86_64.eval, hz₂, h9, h11, Bool.eq_false_iff.mpr hne]; rfl
      refine WP.ite true hev (fun _ => hfail t₂ hK₂ (hs₂.2.1.trans hm₁) ?_) (by simp)
      simp [Spec.RsaPkcs1Sig.encode, hHl, hdl]

/-! ## The buffer after `encode` -/

/-- Writing `xs` at `q` changes memory only there. -/
theorem frame_writeBytes (m : Mem) (q : Addr) (xs : List Byte) :
    Frame [⟨q, xs.length⟩] m (VG.WriteBytes.writeBytes m q xs) := by
  intro x hx
  have h := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at h
  simp only [VG.WriteBytes.writeBytes]
  rw [ite_eq_right_iff.mpr (fun h' => absurd h' (by omega))]

/-- The bytes written. -/
theorem bytesAt_writeBytes (m : Mem) (q : Addr) (xs : List Byte) (hl : xs.length < 2 ^ 64) :
    Spec.Rsa.bytesAt (VG.WriteBytes.writeBytes m q xs) q xs.length = xs := by
  apply List.ext_getElem (by simp [Spec.Rsa.bytesAt])
  intro i h₁ h₂
  simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, VG.WriteBytes.writeBytes,
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

end

/- Proofs formerly in `VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.Compare`. -/
section

/-!
# Comparing two buffers on x86-64

`compare_ok`: `compare` leaves in `rdx` the OR of the differences of the
`n` bytes at `rdi` and `rsi` (`Proof.Ct.diff`), which is zero exactly when
they are equal, and changes neither memory nor any register but `rax`,
`rdx`, `r10` and `r11`.
-/

namespace VG.Proof.RsaPkcs1Sig.X86_64

open VG VG.X86_64 VG.Impl.RsaPkcs1Sig.X86_64
open VG.Proof.MlKem.X86_64 VG.Proof.Ct

/-- The registers `compare` writes. -/
def cmpClob : List Reg := [.rax, .rdx, .r10, .r11]

/-- After `i` bytes. -/
def CInv (s₀ : State) (i : Nat) (s : State) : Prop :=
  VG.Proof.MlKem.X86_64.Keep VG.Proof.RsaPkcs1Sig.X86_64.cmpClob s₀ s ∧ s.mem = s₀.mem ∧ s.gpr .r11 = BitVec.ofNat 64 i ∧
    s.gpr .rdx = (diff s₀.mem (s₀.gpr .rdi) (s₀.gpr .rsi) i).setWidth 64

theorem ea_ix (s : State) (b i : Reg) :
    s.ea { base := b, index := some i } = s.gpr b + s.gpr i := by
  simp [State.ea]

theorem compare_step {s₀ s : State} {n : Nat}
    (hr : ∀ i < n, InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rdi + BitVec.ofNat 64 i) 1 ∧
      InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rsi + BitVec.ofNat 64 i) 1)
    (i : Nat) (hi : i < n) (h : VG.Proof.RsaPkcs1Sig.X86_64.CInv s₀ i s) :
    WP isa (.block [.movzx8 .rax { base := .rdi, index := some .r11 },
      .movzx8 .r10 { base := .rsi, index := some .r11 }, .alu .xor .rax (.reg .r10),
      .alu .or .rdx (.reg .rax), .alu .add .r11 (.imm 1), .alu .cmp .r11 (.reg .rcx)]) s fun t =>
      VG.Proof.RsaPkcs1Sig.X86_64.CInv s₀ (i + 1) t ∧ t.zf = some (BitVec.ofNat 64 (i + 1) == s₀.gpr .rcx) := by
  obtain ⟨hk, hm, hx, ha⟩ := h
  have hdi := hk.gpr (r := .rdi) (by decide)
  have hsi := hk.gpr (r := .rsi) (by decide)
  have hcx := hk.gpr (r := .rcx) (by decide)
  have hA : InRegions (s.rd ++ s.wr) (s₀.gpr .rdi + BitVec.ofNat 64 i) 1 := by
    rw [hk.2.1, hk.2.2]; exact (hr i hi).1
  have hB : InRegions (s.rd ++ s.wr) (s₀.gpr .rsi + BitVec.ofNat 64 i) 1 := by
    rw [hk.2.1, hk.2.2]; exact (hr i hi).2
  have hadd : BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) := by
    rw [BitVec.ofNat_add]; rfl
  refine WP.mono (WP.keep VG.Proof.RsaPkcs1Sig.X86_64.cmpClob (Q := fun t => t.mem = s₀.mem ∧
      t.gpr .r11 = BitVec.ofNat 64 (i + 1) ∧
      t.gpr .rdx = (diff s₀.mem (s₀.gpr .rdi) (s₀.gpr .rsi) (i + 1)).setWidth 64 ∧
      t.zf = some (BitVec.ofNat 64 (i + 1) == s₀.gpr .rcx)) ?_ (by rfl)) ?_
  · xrun [VG.Proof.RsaPkcs1Sig.X86_64.ea_ix, hA, hB, hm, ha, hx, hdi, hsi, hcx, hadd, VG.Proof.RsaPkcs1Sig.X86_64.sub_beq64, ← BitVec.setWidth_xor,
      ← BitVec.setWidth_or, diff]
  · intro t ⟨⟨hm', hx', ha', hz⟩, hk'⟩
    exact ⟨⟨(hk.trans hk').mono (by simp [VG.Proof.RsaPkcs1Sig.X86_64.cmpClob]), hm', hx', ha'⟩, hz⟩

theorem compare_ok {s₀ : State} {n : Nat} (hn : n = (s₀.gpr .rcx).toNat) (hn0 : 0 < n)
    (hr : ∀ i < n, InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rdi + BitVec.ofNat 64 i) 1 ∧
      InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rsi + BitVec.ofNat 64 i) 1) :
    WP isa compare s₀ fun t => VG.Proof.MlKem.X86_64.Keep VG.Proof.RsaPkcs1Sig.X86_64.cmpClob s₀ t ∧ t.mem = s₀.mem ∧
      t.gpr .rdx = (diff s₀.mem (s₀.gpr .rdi) (s₀.gpr .rsi) n).setWidth 64 := by
  have start : WP isa (.block [.mov32 .r11 (.imm 0), .mov32 .rdx (.imm 0)]) s₀ (VG.Proof.RsaPkcs1Sig.X86_64.CInv s₀ 0) := by
    refine WP.mono (WP.keep VG.Proof.RsaPkcs1Sig.X86_64.cmpClob (Q := fun t => t.mem = s₀.mem ∧ t.gpr .r11 = 0 ∧ t.gpr .rdx = 0)
      (by xrun) (by rfl)) fun t ⟨⟨hm, h11, hdx⟩, hk⟩ => ⟨hk, hm, h11, by rw [hdx]; rfl⟩
  refine WP.seq (WP.mono start fun t h0 => ?_)
  refine WP.mono (Q := VG.Proof.RsaPkcs1Sig.X86_64.CInv s₀ n) ?_ fun u hu => ⟨hu.1, hu.2.1, hu.2.2.2⟩
  refine WP.loop (M := isa) (fun rem u => ∃ j, j < n ∧ rem = n - j ∧ VG.Proof.RsaPkcs1Sig.X86_64.CInv s₀ j u) ?_ n t
    ⟨0, hn0, rfl, h0⟩
  intro rem u ⟨j, hj, hrem, hinv⟩
  refine WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.compare_step hr j hj hinv) fun u' ⟨hout, hz⟩ => ?_
  by_cases he : j + 1 = n
  · left
    refine ⟨?_, (by simpa only [he] using hout)⟩
    have : BitVec.ofNat 64 (j + 1) = s₀.gpr .rcx := by rw [he, hn]; simp
    simp [VG.X86_64.eval, hz, this]
  · right
    have hne : BitVec.ofNat 64 (j + 1) ≠ s₀.gpr .rcx := by
      intro hh
      have := congrArg BitVec.toNat hh
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := (s₀.gpr .rcx).isLt; omega)] at this
      exact he (by omega)
    refine ⟨?_, n - (j + 1), by omega, j + 1, by omega, rfl, hout⟩
    simp [VG.X86_64.eval, hz, hne]

end VG.Proof.RsaPkcs1Sig.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCorrect`. -/
section

/-!
# `vg_rsa_pkcs1_verify` on x86-64: correctness

After the call (`afterPub_ok`): the encoding of the hash value into `EM₂`
(`encode_ok`) and the comparison with `EM₁` (`compare_ok`), which is RFC 8017
§8.2.2's verification (`verify_eq_verifyRfc`). With the length check, the
frame's push, the call (`pub_call`) and the pop: `code_correct`.
-/

namespace VG.Proof.RsaPkcs1Sig.X86_64.Ver

open VG VG.X86_64 VG.Impl.RsaPkcs1Sig.X86_64 VG.Impl.RsaPkcs1Sig.X86_64.Verify
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Sig.X86_64 VG.WriteBytes
open Spec.RsaPkcs1Sig

/-! ## Memory in the frame -/

/-- `Env` past changes of the registers but `rsp`, and of memory in the
frame from `EM₁` on. -/
theorem Env.of {s t u : State} (he : VG.Proof.RsaPkcs1Sig.X86_64.Ver.Env s t) (hsp : u.gpr .rsp = t.gpr .rsp) (hrd : u.rd = t.rd)
    (hwr : u.wr = t.wr) {rs : List Region} (hf : Frame rs t.mem u.mem)
    (hs : ∀ r ∈ rs, ∃ d n, r = ⟨VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) d, n⟩ ∧ oEM1 ≤ d ∧ d + n ≤ VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes) : VG.Proof.RsaPkcs1Sig.X86_64.Ver.Env s u := by
  have hsl : ∀ {d}, 32 ≤ d → d + 8 ≤ oEM1 → VG.Proof.Bignum.X86_64.word u.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) d = VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) d := fun hd hd' =>
    slot_keep hf fun r hr => by
      obtain ⟨d', n, rfl, h₁, h₂⟩ := hs r hr
      exact Offset.disjoint _ (.inl (by omega)) (by unfold VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes at *; omega)
        (by unfold VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes at *; omega)
  refine ⟨hsp.trans he.rsp, hrd.trans he.rd, hwr.trans he.wr, frame_call he.mem hf fun r hr => ?_,
    (hsl (by decide) (by decide)).trans he.sN, (hsl (by decide) (by decide)).trans he.sK,
    (hsl (by decide) (by decide)).trans he.sE, (hsl (by decide) (by decide)).trans he.sEl,
    (hsl (by decide) (by decide)).trans he.sH, (hsl (by decide) (by decide)).trans he.sD⟩
  obtain ⟨d, n, rfl, -, h₂⟩ := hs r hr
  exact .inl (VG.Proof.RsaPkcs1Sig.X86_64.Ver.frame_sub s h₂)

/-- `Env` past changes of the registers but `rsp`. -/
theorem Env.regs {s t u : State} (he : VG.Proof.RsaPkcs1Sig.X86_64.Ver.Env s t) (hsp : u.gpr .rsp = t.gpr .rsp) (hm : u.mem = t.mem)
    (hrd : u.rd = t.rd) (hwr : u.wr = t.wr) : VG.Proof.RsaPkcs1Sig.X86_64.Ver.Env s u :=
  ⟨hsp.trans he.rsp, hrd.trans he.rd, hwr.trans he.wr, hm ▸ he.mem, hm ▸ he.sN, hm ▸ he.sK, hm ▸ he.sE,
    hm ▸ he.sEl, hm ▸ he.sH, hm ▸ he.sD⟩

theorem frame_bytes {s : State} {d n : Nat} (hp : PreV s) (h : d + n ≤ VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes) :
    ∀ i < n, InRegions (⟨VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s, VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes⟩ :: s.wr) (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) d + BitVec.ofNat 64 i) 1 := by
  have := VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb_toNat hp
  intro i hi
  refine ⟨_, List.mem_cons_self .., ?_⟩
  rw [show VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) d + BitVec.ofNat 64 i = VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) (d + i) from off_off _ _ _]
  exact Offset.contains_base _ (by omega) (by unfold VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes at *; omega)

/-! ## The blocks after the call -/

theorem test0_ok (t : State) :
    WP isa (.block test0) t fun u => VG.Proof.RsaPkcs1Sig.X86_64.SameF t u ∧ u.zf = some ((t.gpr .rax).setWidth 32 == 0) := by
  xrun [test0]
  exact ⟨⟨rfl, rfl, rfl, rfl⟩, by rw [VG.Proof.RsaPkcs1Sig.X86_64.sub_beq32]⟩

theorem ret0_ok (t : State) : WP isa ret0 t fun u => VG.Proof.MlKem.X86_64.Keep [.rax] t u ∧ u.mem = t.mem ∧ u.gpr .rax = 0 := by
  refine WP.mono (WP.keep [.rax] (Q := fun u => u.mem = t.mem ∧ u.gpr .rax = 0) (by xrun [ret0]) rfl)
    fun u ⟨h, hK⟩ => ⟨hK, h⟩

theorem result_ok (t : State) :
    WP isa (.block VG.Impl.RsaPkcs1Sig.X86_64.Verify.result) t fun u => VG.Proof.MlKem.X86_64.Keep [.rax] t u ∧ u.mem = t.mem ∧
      u.gpr .rax = if t.gpr .rdx = 0 then 1 else 0 := by
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun u => u.mem = t.mem ∧ u.gpr .rdx = t.gpr .rdx ∧
      u.gpr .rax = if t.gpr .rdx = 0 then 1 else 0) (by
    xrun [VG.Impl.RsaPkcs1Sig.X86_64.Verify.result]
    by_cases h : t.gpr .rdx = 0
    · rw [h]; decide
    · have hz : ¬ (t.gpr .rdx).toNat < (1 : BitVec 64).toNat := by
        intro h'; apply h; apply BitVec.eq_of_toNat_eq; simp at h' ⊢; omega
      rw [decide_eq_false hz, ite_eq_right_iff.mpr (fun h' => absurd h' h)]
      decide) rfl) fun u ⟨⟨hm, hdx, ha⟩, hK⟩ => ⟨⟨fun r hr => by
      by_cases h : r = .rdx
      · subst h; exact hdx
      · exact hK.gpr (by simp at hr ⊢; exact ⟨hr, h⟩), hK.2⟩, hm, ha⟩

theorem encArgs_ok {s t : State} (hp : PreV s) (he : VG.Proof.RsaPkcs1Sig.X86_64.Ver.Env s t) :
    WP isa (.block encArgs) t fun u => VG.Proof.MlKem.X86_64.Keep [.r8, .rcx, .rdx, .rsi, .r9] t u ∧ u.mem = t.mem ∧
      u.gpr .r8 = VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM2 ∧ u.gpr .rcx = s.gpr .rsi ∧ u.gpr .rdx = ((s.gpr .r8).setWidth 32).setWidth 64 ∧
      u.gpr .rsi = s.gpr .r9 ∧ u.gpr .r9 = stackArg s 0 := by
  have hs := he.scr hp
  refine WP.mono (WP.keep [.r8, .rcx, .rdx, .rsi, .r9] (Q := fun u => u.mem = t.mem ∧
      u.gpr .r8 = VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM2 ∧ u.gpr .rcx = s.gpr .rsi ∧ u.gpr .rdx = ((s.gpr .r8).setWidth 32).setWidth 64 ∧
      u.gpr .rsi = s.gpr .r9 ∧ u.gpr .r9 = stackArg s 0) (by
    xrun [encArgs, VG.Impl.RsaPkcs1Sig.X86_64.Verify.lea, List.cons_append, List.nil_append, @arg_ea s, VG.Proof.RsaPkcs1Sig.X86_64.Ver.ea_sp, he.rsp,
      sx_ofNat (show oEM2 < 2 ^ 31 by decide), hs.ld (d := VG.Impl.RsaPkcs1Sig.X86_64.Verify.oK) (by decide), hs.ld (d := oH) (by decide),
      hs.ld (d := oD) (by decide), arg_in hp he.rd (show 0 < 5 by decide), he.arg hp (show 0 < 5 by decide),
      he.sK, he.sH, he.sD]) rfl) fun u ⟨h, hK⟩ => ⟨hK, h⟩

theorem cmpArgs_ok {s t : State} (he : VG.Proof.RsaPkcs1Sig.X86_64.Ver.Env s t) :
    WP isa (.block VG.Impl.RsaPkcs1Sig.X86_64.Verify.cmpArgs) t fun u => VG.Proof.MlKem.X86_64.Keep [.rdi, .rsi] t u ∧ u.mem = t.mem ∧
      u.gpr .rdi = VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM1 ∧ u.gpr .rsi = VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM2 := by
  refine WP.mono (WP.keep [.rdi, .rsi] (Q := fun u => u.mem = t.mem ∧
      u.gpr .rdi = VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM1 ∧ u.gpr .rsi = VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM2) (by
    xrun [VG.Impl.RsaPkcs1Sig.X86_64.Verify.cmpArgs, VG.Impl.RsaPkcs1Sig.X86_64.Verify.lea, List.cons_append, List.nil_append, he.rsp,
      sx_ofNat (show oEM1 < 2 ^ 31 by decide), sx_ofNat (show oEM2 < 2 ^ 31 by decide)]) rfl)
    fun u ⟨h, hK⟩ => ⟨hK, h⟩

theorem bytesAt_eq_iff (m : Mem) (a b : Addr) (n : Nat) :
    Spec.Rsa.bytesAt m a n = Spec.Rsa.bytesAt m b n ↔
      ∀ i < n, m (a + BitVec.ofNat 64 i) = m (b + BitVec.ofNat 64 i) := by
  simp only [Spec.Rsa.bytesAt]
  rw [List.map_inj_left]
  simp only [List.mem_range]

theorem setWidth_byte_eq_zero (d : Byte) : d.setWidth 64 = 0 ↔ d = 0 := by
  constructor
  · intro h; apply BitVec.eq_of_toNat_eq; have := congrArg BitVec.toNat h; have := d.isLt; simp at *; omega
  · rintro rfl; rfl

/-! ## Verification by encoding -/

/-- Verification, for a signature of `k` bytes: RSAVP1, then the encoding,
then their comparison. -/
theorem verifyId_eq (nB eB : List Byte) (x : BitVec 32) (H sig : List Byte) (hs : sig.length = nB.length) :
    verifyId nB eB x.toNat H sig =
      match Spec.Rsa.publicOpChecked nB eB sig, VG.Proof.RsaPkcs1Sig.X86_64.encodeId x H nB.length with
      | some em, some em' => em == em'
      | _, _ => false := by
  unfold verifyId VG.Proof.RsaPkcs1Sig.X86_64.encodeId
  cases hid : Hash.ofId x.toNat with
  | none => simp only; split <;> simp_all
  | some h =>
    simp only
    rw [verify_eq_verifyRfc]
    unfold verifyRfc
    rw [ite_eq_left hs]
    cases Spec.Rsa.publicOpChecked nB eB sig <;> cases Spec.RsaPkcs1Sig.encode h H nB.length <;> rfl

theorem afterPub_ok {s t : State} (hp : PreV s) (he : VG.Proof.RsaPkcs1Sig.X86_64.Ver.Env s t)
    (hw : Spec.Rsa.written t.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM1) (s.gpr .rsi).toNat ((t.gpr .rax).setWidth 32)
      (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 1) (s.gpr .rsi).toNat))) :
    WP isa afterPub t fun u => VG.Proof.RsaPkcs1Sig.X86_64.Ver.Env s u ∧ (u.gpr .rax).setWidth 32 =
      if verifyId (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
          (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) ((s.gpr .r8).setWidth 32).toNat
          (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (stackArg s 0).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 1) (s.gpr .rsi).toNat) then 1 else 0 := by
  have hk1 := hp.k1
  have hk2 := hp.k2
  have hF := VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb_toNat hp
  set k := (s.gpr .rsi).toNat with hkdef
  set nB := Spec.Rsa.bytesAt s.mem (s.gpr .rdi) k
  set eB := Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat
  set gB := Spec.Rsa.bytesAt s.mem (stackArg s 1) k
  set dB := Spec.Rsa.bytesAt s.mem (s.gpr .r9) (stackArg s 0).toNat
  set x := (s.gpr .r8).setWidth 32
  have hnl : nB.length = k := VG.Proof.RsaPkcs1Sig.X86_64.bytesAt_length _ _ _
  have hgl : gB.length = nB.length := by rw [hnl]; exact VG.Proof.RsaPkcs1Sig.X86_64.bytesAt_length _ _ _
  rw [VG.Proof.RsaPkcs1Sig.X86_64.Ver.verifyId_eq nB eB x dB gB hgl, hnl]
  unfold afterPub
  refine WP.seq (WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.Ver.test0_ok t) fun t₁ ⟨hs₁, hz₁⟩ => ?_)
  have he₁ : VG.Proof.RsaPkcs1Sig.X86_64.Ver.Env s t₁ := he.regs (by rw [hs₁.1]) hs₁.2.1 hs₁.2.2.1 hs₁.2.2.2
  have hret0 : ∀ u, VG.Proof.RsaPkcs1Sig.X86_64.Ver.Env s u → (∀ o, Spec.Rsa.publicOpChecked nB eB gB = o →
      (match o, VG.Proof.RsaPkcs1Sig.X86_64.encodeId x dB k with | some em, some em' => em == em' | _, _ => false) = false) →
      WP isa ret0 u fun v => VG.Proof.RsaPkcs1Sig.X86_64.Ver.Env s v ∧ (v.gpr .rax).setWidth 32 =
        if (match Spec.Rsa.publicOpChecked nB eB gB, VG.Proof.RsaPkcs1Sig.X86_64.encodeId x dB k with
          | some em, some em' => em == em' | _, _ => false) = true then 1 else 0 := fun u hu hf =>
    WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.Ver.ret0_ok u) fun v ⟨hK, hm, hax⟩ => ⟨hu.regs (hK.gpr (by decide)) hm hK.2.1 hK.2.2, by
      rw [hf _ rfl, hax]; rfl⟩
  cases hpo : Spec.Rsa.publicOpChecked nB eB gB with
  | none =>
    rw [hpo] at hw
    obtain ⟨hr, -⟩ := hw
    refine WP.ite true (by simp [VG.X86_64.eval, hz₁, hr]) (fun _ => ?_) (by simp)
    refine WP.mono (hret0 t₁ he₁ fun o ho => ?_) fun v hv => by rw [hpo] at hv; exact hv
    rw [← ho, hpo]
  | some em =>
    rw [hpo] at hw
    obtain ⟨hr, hem⟩ := hw
    refine WP.ite false (by simp [VG.X86_64.eval, hz₁, hr]) (by simp) (fun _ => ?_)
    refine WP.seq (WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.Ver.encArgs_ok hp he₁) fun t₂ ⟨hK₂, hm₂, h8₂, hcx₂, hdx₂, hsi₂, h9₂⟩ => ?_)
    have he₂ : VG.Proof.RsaPkcs1Sig.X86_64.Ver.Env s t₂ := he₁.regs (hK₂.gpr (by decide)) hm₂ hK₂.2.1 hK₂.2.2
    have sE2 : Region.Sub ⟨VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM2, k⟩ (VG.Proof.RsaPkcs1Sig.X86_64.Ver.stkR s) := VG.Proof.RsaPkcs1Sig.X86_64.Ver.frame_sub s (by unfold oEM2 VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes; omega)
    have hdl := hp.wD
    have hpre : VG.Proof.RsaPkcs1Sig.X86_64.EPre t₂ x k := {
      rdx := by rw [hdx₂]; apply BitVec.eq_of_toNat_eq; simp [x]
      hk := by rw [hcx₂]
      kle := hk2
      buf := fun i hi => by
        rw [h8₂, he₂.wr]; exact VG.Proof.RsaPkcs1Sig.X86_64.Ver.frame_bytes hp (by unfold oEM2 VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes; omega) i hi
      rd := fun j hj => by
        rw [hsi₂, he₂.rd, he₂.wr]
        rw [h9₂] at hj
        exact ⟨⟨s.gpr .r9, (stackArg s 0).toNat⟩, List.mem_append_left _ (by rw [hp.hrd]; simp),
          Offset.contains_base _ (by omega) (by omega)⟩
      sep := fun j hj i hi => by
        rw [hsi₂, h8₂]
        rw [h9₂] at hj
        exact VG.Proof.RsaPkcs1Sig.X86_64.ne_of_disjoint (hp.dKd.sub_left sE2).symm (by omega) (by omega) hj hi }
    have hdB : Spec.Rsa.bytesAt t₂.mem (t₂.gpr .rsi) (t₂.gpr .r9).toNat = dB := by
      rw [hsi₂, h9₂, hm₂, hs₁.2.1]
      exact bytes_of_frame he.mem hp.dKd hp.dds.symm (by omega)
    refine WP.seq (WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.encode_ok hpre) fun t₃ ⟨hK₃, hpost⟩ => ?_)
    rw [hdB] at hpost
    unfold VG.Impl.RsaPkcs1Sig.X86_64.Verify.tail
    refine WP.seq (WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.Ver.test0_ok t₃) fun t₄ ⟨hs₄, hz₄⟩ => ?_)
    cases hE : VG.Proof.RsaPkcs1Sig.X86_64.encodeId x dB k with
    | none =>
      rw [hE] at hpost
      obtain ⟨hax, hm₃⟩ := hpost
      have he₄ : VG.Proof.RsaPkcs1Sig.X86_64.Ver.Env s t₄ := he₂.regs (by rw [hs₄.1, hK₃.gpr (by decide)]) (hs₄.2.1.trans hm₃)
        (hs₄.2.2.1.trans hK₃.2.1) (hs₄.2.2.2.trans hK₃.2.2)
      refine WP.ite true (by simp [VG.X86_64.eval, hz₄, hax]) (fun _ => ?_) (by simp)
      refine WP.mono (hret0 t₄ he₄ fun o ho => ?_) fun v hv => by rw [hpo, hE] at hv; exact hv
      rw [← ho, hpo, hE]
    | some em' =>
      rw [hE] at hpost
      obtain ⟨hax, hm₃⟩ := hpost
      have hl' : em'.length = k := by
        unfold VG.Proof.RsaPkcs1Sig.X86_64.encodeId at hE
        split at hE
        · exact VG.Proof.RsaPkcs1Sig.encode_length hE
        · cases hE
      have he₃ : VG.Proof.RsaPkcs1Sig.X86_64.Ver.Env s t₃ := Env.of he₂ (hK₃.gpr (by decide)) hK₃.2.1 hK₃.2.2 (hm₃ ▸ VG.Proof.RsaPkcs1Sig.X86_64.frame_writeBytes _ _ _)
        fun r hr => ⟨oEM2, k, by rw [List.mem_singleton.mp hr, h8₂, hl'], by decide, by unfold oEM2 VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes; omega⟩
      have he₄ : VG.Proof.RsaPkcs1Sig.X86_64.Ver.Env s t₄ := he₃.regs (by rw [hs₄.1]) hs₄.2.1 hs₄.2.2.1 hs₄.2.2.2
      refine WP.ite false (by simp [VG.X86_64.eval, hz₄, hax]) (by simp) (fun _ => ?_)
      refine WP.seq (WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.Ver.cmpArgs_ok he₄) fun t₅ ⟨hK₅, hm₅, hdi₅, hsi₅⟩ => ?_)
      have hcx₅ : t₅.gpr .rcx = s.gpr .rsi := by
        rw [hK₅.gpr (by decide), hs₄.1, hK₃.gpr (by decide), hcx₂]
      have he₅ : VG.Proof.RsaPkcs1Sig.X86_64.Ver.Env s t₅ := he₄.regs (hK₅.gpr (by decide)) hm₅ hK₅.2.1 hK₅.2.2
      have hr5 : ∀ i < k, InRegions (t₅.rd ++ t₅.wr) (t₅.gpr .rdi + BitVec.ofNat 64 i) 1 ∧
          InRegions (t₅.rd ++ t₅.wr) (t₅.gpr .rsi + BitVec.ofNat 64 i) 1 := fun i hi => by
        rw [hdi₅, hsi₅, he₅.wr]
        obtain ⟨r₁, h₁, c₁⟩ := VG.Proof.RsaPkcs1Sig.X86_64.Ver.frame_bytes hp (d := oEM1) (n := k) (by unfold oEM1 VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes; omega) i hi
        obtain ⟨r₂, h₂, c₂⟩ := VG.Proof.RsaPkcs1Sig.X86_64.Ver.frame_bytes hp (d := oEM2) (n := k) (by unfold oEM2 VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes; omega) i hi
        exact ⟨⟨r₁, List.mem_append_right _ h₁, c₁⟩, ⟨r₂, List.mem_append_right _ h₂, c₂⟩⟩
      refine WP.seq (WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.compare_ok (by rw [hcx₅]) (by omega) hr5) fun t₆ ⟨hK₆, hm₆, hdx₆⟩ => ?_)
      refine WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.Ver.result_ok t₆) fun u ⟨hK, hm, hax'⟩ => ⟨?_, ?_⟩
      · exact (he₅.regs (hK₆.gpr (by decide)) hm₆ hK₆.2.1 hK₆.2.2).regs (hK.gpr (by decide)) hm hK.2.1 hK.2.2
      · have sE1 : (⟨VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM1, k⟩ : Region).Disjoint ⟨VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM2, em'.length⟩ := by
          rw [hl']; exact Offset.disjoint _ (.inl (by unfold oEM1 oEM2; omega)) (by unfold oEM1 VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes at *; omega)
            (by unfold oEM2 VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes at *; omega)
        have h1 : Spec.Rsa.bytesAt t₃.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM1) k = em := by
          rw [← hem, hm₃, h8₂]
          simp only [Spec.Rsa.bytesAt]
          refine List.map_congr_left fun i hi => ?_
          refine ((VG.Proof.RsaPkcs1Sig.X86_64.frame_writeBytes t₂.mem _ em').bytes (R := ⟨VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM1, k⟩) (fun r hr => ?_) (by show k ≤ 2 ^ 64; omega)
            (List.mem_range.mp hi)).trans ?_
          · rw [List.mem_singleton.mp hr]; exact sE1
          · rw [hm₂, hs₁.2.1]
        have h2 : Spec.Rsa.bytesAt t₃.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM2) k = em' := by
          have := VG.Proof.RsaPkcs1Sig.X86_64.bytesAt_writeBytes t₂.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM2) em' (by omega)
          rw [hl'] at this
          rw [hm₃, h8₂]; exact this
        have hm6 : t₆.mem = t₃.mem := by rw [hm₆, hm₅, hs₄.2.1]
        rw [hax', hdx₆, hdi₅, hsi₅]
        simp only [VG.Proof.RsaPkcs1Sig.X86_64.Ver.setWidth_byte_eq_zero, VG.Proof.Ct.diff_zero, ← VG.Proof.RsaPkcs1Sig.X86_64.Ver.bytesAt_eq_iff, hm₅, hs₄.2.1, h1, h2]
        by_cases hq : em = em' <;> simp [hq]

/-! ## The arguments and the frame -/

theorem word_wo0 (m : Mem) (base : Addr) (v : BitVec 64) {d' : Nat} (h : 8 ≤ d') (hd' : d' + 8 ≤ 4096) :
    VG.Proof.Bignum.X86_64.word (m.writeW base v) base d' = VG.Proof.Bignum.X86_64.word m base d' := by
  have := VG.Proof.RsaPkcs1Sig.X86_64.Ver.word_wo m base v (d := 0) (d' := d') (.inl (by omega)) (by decide) hd'
  simpa only [Bignum.X86_64.word, VG.Proof.Bignum.X86_64.off, BitVec.add_zero] using this

theorem word_self0 (m : Mem) (base : Addr) (v : BitVec 64) : VG.Proof.Bignum.X86_64.word (m.writeW base v) base 0 = v := by
  have := VG.Proof.Bignum.X86_64.word_writeW_self m base 0 v
  simpa only [VG.Proof.Bignum.X86_64.off, BitVec.add_zero] using this

/-- The frame's push and the arguments of the call. -/
theorem pubArgs_ok {s A : State} (hp : PreV s) (hA : VG.Proof.MlKem.X86_64.Keep [.rax] (allocState VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes s) A)
    (hAm : A.mem = s.mem) :
    WP isa (.block pubArgs) A fun t => VG.Proof.RsaPkcs1Sig.X86_64.Ver.Env s t ∧
      VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) 0 = stackArg s 1 ∧ VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) 8 = s.gpr .rsi ∧
      VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) 16 = stackArg s 3 ∧ VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) 24 = stackArg s 4 ∧
      t.gpr .rdi = VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM1 ∧ t.gpr .rsi = s.gpr .rsi ∧ t.gpr .rdx = s.gpr .rdi ∧
      t.gpr .rcx = s.gpr .rsi ∧ t.gpr .r8 = s.gpr .rdx ∧ t.gpr .r9 = s.gpr .rcx ∧
      (∀ r ∈ calleeSaved, r ≠ .rsp → t.gpr r = s.gpr r) := by
  have hF := VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb_toNat hp
  rw [pubArgs_eq, WP.block_append_iff]
  refine WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.Ver.slotStores_ok hp hA hAm) fun t₁ ⟨k₁, ho₁, hN, hK, hE, hEl, hH, hD⟩ => ?_
  refine WP.mono (callArgs_ok hp k₁ ho₁) fun t ⟨k, hm, hdi, hsi, hdx, hcx, h8, h9⟩ => ?_
  have k' := k₁.trans k
  have hw : ∀ d, 32 ≤ d → d + 8 ≤ VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes → VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) d = VG.Proof.Bignum.X86_64.word t₁.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) d := fun d hd hd' => by
    unfold VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes at hd'
    rw [hm, VG.Proof.RsaPkcs1Sig.X86_64.Ver.word_wo _ _ _ (d := 24) (.inl (by omega)) (by decide) (by omega),
      VG.Proof.RsaPkcs1Sig.X86_64.Ver.word_wo _ _ _ (d := 16) (.inl (by omega)) (by decide) (by omega),
      VG.Proof.RsaPkcs1Sig.X86_64.Ver.word_wo _ _ _ (d := 8) (.inl (by omega)) (by decide) (by omega), VG.Proof.RsaPkcs1Sig.X86_64.Ver.word_wo0 _ _ _ (by omega) (by omega)]
  refine ⟨⟨(k'.gpr (by decide)).trans rfl, k'.2.1, k'.2.2, VG.Proof.RsaPkcs1Sig.X86_64.Ver.frame_of_outside ?_,
      (hw _ (by decide) (by decide)).trans hN, (hw _ (by decide) (by decide)).trans hK,
      (hw _ (by decide) (by decide)).trans hE, (hw _ (by decide) (by decide)).trans hEl,
      (hw _ (by decide) (by decide)).trans hH, (hw _ (by decide) (by decide)).trans hD⟩, ?_, ?_, ?_, ?_,
    hdi, hsi, hdx, hcx, h8, h9, fun r hr hr' => ?_⟩
  · rw [hm]
    intro x hx
    have hx' : VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes ≤ VG.Proof.Bignum.X86_64.ofs (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) x := by unfold VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes at hx ⊢; omega
    unfold VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes at hx hx'
    rw [VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (d := 24) (by omega) x (by omega), VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (d := 16) (by omega) x (by omega),
      VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (d := 8) (by omega) x (by omega)]
    have := VG.Proof.Bignum.X86_64.writeW_outside t₁.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) (stackArg s 1) (d := 0) (by omega) x (by omega)
    simp only [VG.Proof.Bignum.X86_64.off, BitVec.add_zero] at this
    rw [this]; exact ho₁ x hx
  · rw [hm]; simp (disch := decide) only [VG.Proof.RsaPkcs1Sig.X86_64.Ver.word_wo]; exact VG.Proof.RsaPkcs1Sig.X86_64.Ver.word_self0 _ _ _
  · rw [hm]; simp (disch := decide) only [VG.Proof.RsaPkcs1Sig.X86_64.Ver.word_wo, VG.Proof.Bignum.X86_64.word_writeW_self]
  · rw [hm]; simp (disch := decide) only [VG.Proof.RsaPkcs1Sig.X86_64.Ver.word_wo, VG.Proof.Bignum.X86_64.word_writeW_self]
  · rw [hm]; exact VG.Proof.Bignum.X86_64.word_writeW_self _ _ _ _
  · rw [k'.gpr (by simp [calleeSaved] at hr ⊢; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all)]
    simp [VG.Proof.RsaPkcs1Sig.X86_64.Ver.allocState_gpr, hr']

/-! ## The whole function -/

/-- The state after the frame's pop, from the state `s₂` its body ends in. -/
def freed (bytes : Nat) (s₂ : State) : State :=
  { s₂.setReg .rsp (s₂.gpr .rsp + BitVec.ofNat 64 bytes) with wr := s₂.wr.tail }

/-- The frame: its body runs from `allocState frameBytes s` and ends with
`rsp` and the writable regions as the push left them. -/
theorem wp_alloc {body : Prog isa} {s : State} {Q : State → Prop} (hsp : VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes ≤ (s.gpr .rsp).toNat)
    (hb : WP isa body (allocState VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes s) fun s₂ => s₂.gpr .rsp = VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s ∧
      s₂.wr = (allocState VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes s).wr ∧ Q (VG.Proof.RsaPkcs1Sig.X86_64.Ver.freed VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes s₂)) :
    WP isa (.frame (.alloc VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes) body (.free VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes)) s Q := by
  obtain ⟨t, s₂, he, hsp₂, hw, hq⟩ := hb
  have ha : isa.push (.alloc VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes) s = some (allocState VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes s) := by
    simp only [isa, push, allocState]
    exact ite_eq_left ⟨by decide, by decide, by decide, hsp⟩
  have hf : isa.pop (.free VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes) (allocState VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes s) s₂ = some (VG.Proof.RsaPkcs1Sig.X86_64.Ver.freed VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes s₂) := by
    simp only [isa, pop]
    exact ite_eq_left ⟨by decide, by decide, by decide, hsp₂, hw, rfl⟩
  exact ⟨_, _, Exec.frame ha he hf, hq⟩

/-- The return address is outside everything the function writes. -/
theorem ret_frame {s : State} (hp : PreV s) {m : Mem} (h : Frame [VG.Proof.RsaPkcs1Sig.X86_64.Ver.stkR s, VG.Proof.RsaPkcs1Sig.X86_64.Ver.scrR s] s.mem m) :
    m.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64 := by
  have hsp2 := hp.sp2
  refine h.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · have := Offset.disjoint_below (s.gpr .rsp) (n := verStack) (d := 0) (k := 8)
      (by unfold verStack; omega)
    simpa only [VG.Proof.RsaPkcs1Sig.X86_64.Ver.stkR, VG.Proof.RsaPkcs1Sig.X86_64.Ver.kb, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this
  · exact hp.dRs

theorem arg0_ea (t : State) (j : Nat) : t.ea (arg0 j) = stackArgAddr t j := by
  rw [arg0, VG.Proof.RsaPkcs1Sig.X86_64.Ver.ea_sp, stackArgAddr]; congr 2; omega

theorem lenCheck_ok {s : State} (hp : PreV s) :
    WP isa (.block lenCheck) s fun t => VG.Proof.MlKem.X86_64.Keep [.rax] s t ∧ t.mem = s.mem ∧
      t.zf = some (stackArg s 2 == s.gpr .rsi) := by
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s.mem ∧ t.zf = some (stackArg s 2 == s.gpr .rsi)) (by
    xrun [lenCheck, VG.Proof.RsaPkcs1Sig.X86_64.Ver.arg0_ea, arg_in hp rfl (show 2 < 5 by decide), VG.Proof.RsaPkcs1Sig.X86_64.sub_beq64]
    rfl) rfl) fun t ⟨h, hK⟩ => ⟨hK, h⟩

theorem verifyId_len {nB eB H sig : List Byte} (x : Nat) (h : sig.length ≠ nB.length) :
    verifyId nB eB x H sig = false := by
  unfold verifyId
  split
  · unfold verify; rw [ite_eq_right_iff.mpr (fun h' => absurd h'.1 h)]
  · rfl

theorem code_correct (v : PubImpl) (s : State) (h : verContract.pre s) :
    ∃ t s', Exec isa (VG.Impl.RsaPkcs1Sig.X86_64.Verify.code v.name v.code) s t s' ∧ abiPreserved s s' ∧ verContract.post s s' := by
  have hp := preV_of h
  have hk2 := hp.k2
  suffices hw : WP isa (VG.Impl.RsaPkcs1Sig.X86_64.Verify.code v.name v.code) s fun s' => abiPreserved s s' ∧ verContract.post s s' by
    obtain ⟨t, s', he, hq⟩ := hw
    exact ⟨t, s', he, hq⟩
  unfold VG.Impl.RsaPkcs1Sig.X86_64.Verify.code
  refine WP.seq (WP.mono_mx (by decide) (VG.Proof.RsaPkcs1Sig.X86_64.Ver.lenCheck_ok hp) fun t₀ ⟨k₀, hm₀, hz₀⟩ hmx₀ => ?_)
  by_cases hsig : stackArg s 2 = s.gpr .rsi
  · refine WP.ite false (by simp [VG.X86_64.eval, hz₀, hsig]) (by simp) (fun _ => ?_)
    have g₀ : ∀ r, r ≠ .rax → t₀.gpr r = s.gpr r := fun r h => k₀.gpr (by simpa using h)
    have hsp₀ : t₀.gpr .rsp = s.gpr .rsp := g₀ _ (by decide)
    have hA : VG.Proof.MlKem.X86_64.Keep [.rax] (allocState VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes s) (allocState VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes t₀) :=
      ⟨fun r hr => by
        simp only [VG.Proof.RsaPkcs1Sig.X86_64.Ver.allocState_gpr, VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb, hsp₀]
        split
        · rfl
        · exact g₀ r (by simpa using hr), k₀.2.1, by simp only [allocState, hsp₀, k₀.2.2]⟩
    have hfb : VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb t₀ = VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s := by simp only [VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb, hsp₀]
    refine VG.Proof.RsaPkcs1Sig.X86_64.Ver.wp_alloc (s := t₀) (by rw [hsp₀]; have := hp.sp1; unfold verStack at this; unfold VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes; omega) ?_
    unfold VG.Impl.RsaPkcs1Sig.X86_64.Verify.body
    refine WP.seq (WP.mono_mx (by decide) (VG.Proof.RsaPkcs1Sig.X86_64.Ver.pubArgs_ok hp hA hm₀)
      fun t₁ ⟨he₁, hw0, hw1, hw2, hw3, hdi, hsi, hdx, hcx, h8, h9, hcs₁⟩ hmx₁ => ?_)
    refine WP.seq (WP.mono (pub_call v hp hsig he₁ hw0 hw1 hw2 hw3 hdi hsi hdx hcx h8 h9)
      fun t₂ ⟨he₂, hw, hcs₂, hmx₂⟩ => ?_)
    refine WP.mono_mx (by decide +kernel) (WP.keep [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11]
      (VG.Proof.RsaPkcs1Sig.X86_64.Ver.afterPub_ok hp he₂ hw) (by decide +kernel)) fun t₃ ⟨⟨he₃, hax⟩, k₃⟩ hmx₃ => ?_
    refine ⟨he₃.rsp.trans hfb.symm, by rw [he₃.wr]; simp only [allocState, hsp₀, k₀.2.2],
      ⟨fun r hr => ?_, VG.Proof.RsaPkcs1Sig.X86_64.Ver.ret_frame hp he₃.mem, ?_⟩, ?_⟩
    · by_cases hr' : r = .rsp
      · subst hr'
        show t₃.gpr .rsp + BitVec.ofNat 64 VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes = s.gpr .rsp
        rw [he₃.rsp, BitVec.sub_add_cancel]
      · show (if r = .rsp then _ else t₃.gpr r) = s.gpr r
        simp only [hr', ↓reduceIte]
        have hr'' : r ∉ [Reg.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11] := by
          simp [calleeSaved] at hr ⊢; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
        rw [k₃.gpr hr'', hcs₂ r hr, hcs₁ r hr hr']
    · show t₃.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10
      rw [hmx₃, hmx₂, hmx₁]; exact congrArg _ hmx₀
    · have hfr : (VG.Proof.RsaPkcs1Sig.X86_64.Ver.freed VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes t₃).gpr .rax = t₃.gpr .rax := rfl
      simp only [verContract, hfr, hax, hsig]
  · refine WP.ite true (by simp [VG.X86_64.eval, hz₀, hsig]) (fun _ => ?_) (by simp)
    refine WP.mono_mx (by decide) (VG.Proof.RsaPkcs1Sig.X86_64.Ver.ret0_ok t₀) fun u ⟨hK, hm, hax⟩ hmx =>
      ⟨⟨fun r hr => ?_, by rw [hm, hm₀], by rw [hmx, hmx₀]⟩, ?_⟩
    · rw [hK.gpr (by simp [calleeSaved] at hr ⊢; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp),
        k₀.gpr (by simp [calleeSaved] at hr ⊢; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)]
    · simp only [verContract, hax]
      rw [VG.Proof.RsaPkcs1Sig.X86_64.Ver.verifyId_len _ (by
        simp only [VG.Proof.RsaPkcs1Sig.X86_64.bytesAt_length]
        intro h'; exact hsig (BitVec.eq_of_toNat_eq h'))]
      rfl

end VG.Proof.RsaPkcs1Sig.X86_64.Ver

end

/- Proofs formerly in `VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCT`. -/
section

/-!
# `vg_rsa_pkcs1_verify` on x86-64: constant time

Two runs from entry states that agree on the public data (`verContract.pub`:
the pointers and lengths, `hash` and the bytes of `n`, `e`, the hash value
and the signature) leak the same trace. Each point of the code is described,
in each run, by what correctness says of it from that run's entry state,
which agrees with an anchor `a` on the public data (`At`): the blocks
between the call and the branches are checked by the taint analysis from the
registers this fixes, each branch's condition is fixed by it too, and the
call is constant time for its callee's contract, whose public data it fixes.
-/

namespace VG.Proof.RsaPkcs1Sig.X86_64.Ver

open VG VG.X86_64 VG.Impl.RsaPkcs1Sig.X86_64 VG.Impl.RsaPkcs1Sig.X86_64.Verify
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Sig.X86_64

/-! ## Entry states and the anchor -/

/-- An entry state meeting the precondition with the anchor's public data. -/
def Sib (a s : State) : Prop := verContract.pre s ∧ verContract.pub a s

theorem pub_refl (s : State) : verContract.pub s s := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Sib.gpr {a s : State} (h : VG.Proof.RsaPkcs1Sig.X86_64.Ver.Sib a s) {r : Reg} (hr : r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r9, .rsp]) :
    s.gpr r = a.gpr r := (h.2.1 r hr).symm

theorem Sib.r8 {a s : State} (h : VG.Proof.RsaPkcs1Sig.X86_64.Ver.Sib a s) : (s.gpr .r8).setWidth 32 = (a.gpr .r8).setWidth 32 := h.2.2.1.symm

theorem Sib.arg {a s : State} (h : VG.Proof.RsaPkcs1Sig.X86_64.Ver.Sib a s) {i : Nat} (hi : i < 5) : stackArg s i = stackArg a i :=
  ((List.map_inj_left.mp h.2.2.2.1) i (List.mem_range.mpr hi)).symm

theorem Sib.n {a s : State} (h : VG.Proof.RsaPkcs1Sig.X86_64.Ver.Sib a s) :
    Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .rdi) (a.gpr .rsi).toNat :=
  h.2.2.2.2.1.symm

theorem Sib.e {a s : State} (h : VG.Proof.RsaPkcs1Sig.X86_64.Ver.Sib a s) :
    Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .rdx) (a.gpr .rcx).toNat :=
  h.2.2.2.2.2.1.symm

theorem Sib.g {a s : State} (h : VG.Proof.RsaPkcs1Sig.X86_64.Ver.Sib a s) :
    Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat =
      Spec.Rsa.bytesAt a.mem (stackArg a 1) (stackArg a 2).toNat :=
  h.2.2.2.2.2.2.2.symm

theorem Sib.fb {a s : State} (h : VG.Proof.RsaPkcs1Sig.X86_64.Ver.Sib a s) : VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s = VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb a := by
  show s.gpr .rsp - _ = a.gpr .rsp - _
  rw [h.gpr (r := .rsp) (by decide)]

/-- A point of a run, described by `J` from the run's entry state. -/
def At (J : State → State → Prop) (a t : State) : Prop := ∃ s, VG.Proof.RsaPkcs1Sig.X86_64.Ver.Sib a s ∧ J s t

/-- A register `J` gives as a function of the public data. -/
theorem pin {J : State → State → Prop} {r : Reg} (f : State → BitVec 64) (hf : ∀ s t, J s t → t.gpr r = f s)
    (hs : ∀ a s, VG.Proof.RsaPkcs1Sig.X86_64.Ver.Sib a s → f s = f a) {a t₁ t₂ : State} (h₁ : VG.Proof.RsaPkcs1Sig.X86_64.Ver.At J a t₁) (h₂ : VG.Proof.RsaPkcs1Sig.X86_64.Ver.At J a t₂) :
    t₁.gpr r = t₂.gpr r := by
  obtain ⟨s₁, S₁, j₁⟩ := h₁
  obtain ⟨s₂, S₂, j₂⟩ := h₂
  rw [hf _ _ j₁, hf _ _ j₂, hs _ _ S₁, hs _ _ S₂]

/-- A condition `J` gives as a function of the public data. -/
theorem pinEval {J : State → State → Prop} {c : Cond} (f : State → Option Bool)
    (hf : ∀ s t, J s t → isa.eval c t = f s) (hs : ∀ a s, VG.Proof.RsaPkcs1Sig.X86_64.Ver.Sib a s → f s = f a) :
    ∀ a t₁ t₂, VG.Proof.RsaPkcs1Sig.X86_64.Ver.At J a t₁ → VG.Proof.RsaPkcs1Sig.X86_64.Ver.At J a t₂ → isa.eval c t₁ = isa.eval c t₂ := by
  rintro a t₁ t₂ ⟨s₁, S₁, j₁⟩ ⟨s₂, S₂, j₂⟩
  rw [hf _ _ j₁, hf _ _ j₂, hs _ _ S₁, hs _ _ S₂]

/-- In the frame, `rsp` is public. -/
theorem pins_rsp {J : State → State → Prop} (hJ : ∀ s t, J s t → t.gpr .rsp = VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) : Pins (VG.Proof.RsaPkcs1Sig.X86_64.Ver.At J) [.rsp] :=
  fun _ _ _ h₁ h₂ r hr => by
    rw [List.mem_singleton.mp hr]
    exact VG.Proof.RsaPkcs1Sig.X86_64.Ver.pin VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb hJ (fun _ _ h => h.fb) h₁ h₂

theorem written_r {m : Mem} {o : Addr} {n : Nat} {r : BitVec 32} {v : Option (List Byte)}
    (h : Spec.Rsa.written m o n r v) : r = if v.isSome then 1 else 0 := by
  cases v <;> simp only [Spec.Rsa.written] at h <;> simp [h.1]

/-! ## The taint checks -/

theorem lenCheck_taint {Φ : State → State → Prop} (h : Pins (Φ) [.rsp]) :
    RelCT isa (Two Φ) (.block lenCheck) fun _ _ => True := two_taint [.rsp] h (by taint_decide)

theorem pubArgs_taint {Φ : State → State → Prop} (h : Pins (Φ) [.rsp]) :
    RelCT isa (Two Φ) (.block pubArgs) fun _ _ => True := two_taint [.rsp] h (by taint_decide)

theorem encArgs_taint {Φ : State → State → Prop} (h : Pins (Φ) [.rsp]) :
    RelCT isa (Two Φ) (.block encArgs) fun _ _ => True := two_taint [.rsp] h (by taint_decide)

theorem encTail_taint {Φ : State → State → Prop} (h : Pins (Φ) [.rsp, .r8, .rcx, .rdx, .rsi, .r9]) :
    RelCT isa (Two Φ) (.seq encode VG.Impl.RsaPkcs1Sig.X86_64.Verify.tail) fun _ _ => True :=
  two_taint [.rsp, .r8, .rcx, .rdx, .rsi, .r9] h (by taint_decide)

/-! ## The points of the code -/

def J0 (s t : State) : Prop := t = s

def JL (s t : State) : Prop := VG.Proof.MlKem.X86_64.Keep [.rax] s t ∧ t.mem = s.mem ∧ t.zf = some (stackArg s 2 == s.gpr .rsi)

def JA (s t : State) : Prop :=
  ∃ t₀, VG.Proof.RsaPkcs1Sig.X86_64.Ver.JL s t₀ ∧ stackArg s 2 = s.gpr .rsi ∧ t = allocState VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes t₀

def J1 (s t : State) : Prop :=
  VG.Proof.RsaPkcs1Sig.X86_64.Ver.Env s t ∧ VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) 0 = stackArg s 1 ∧ VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) 8 = s.gpr .rsi ∧
    VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) 16 = stackArg s 3 ∧ VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) 24 = stackArg s 4 ∧
    t.gpr .rdi = VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM1 ∧ t.gpr .rsi = s.gpr .rsi ∧ t.gpr .rdx = s.gpr .rdi ∧
    t.gpr .rcx = s.gpr .rsi ∧ t.gpr .r8 = s.gpr .rdx ∧ t.gpr .r9 = s.gpr .rcx ∧ stackArg s 2 = s.gpr .rsi

/-- RSAVP1 of the signature, as the entry state gives it. -/
def pubOut (s : State) : Option (List Byte) :=
  Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 1) (s.gpr .rsi).toNat)

theorem pubOut_sib {a s : State} (S : VG.Proof.RsaPkcs1Sig.X86_64.Ver.Sib a s) (hs : stackArg s 2 = s.gpr .rsi) : VG.Proof.RsaPkcs1Sig.X86_64.Ver.pubOut s = VG.Proof.RsaPkcs1Sig.X86_64.Ver.pubOut a := by
  have ha : stackArg a 2 = a.gpr .rsi := by rw [← S.arg (by decide), hs, S.gpr (by decide)]
  have hg := S.g
  rw [hs, ha] at hg
  simp only [VG.Proof.RsaPkcs1Sig.X86_64.Ver.pubOut, S.n, S.e, hg]

def J2 (s t : State) : Prop :=
  VG.Proof.RsaPkcs1Sig.X86_64.Ver.Env s t ∧ Spec.Rsa.written t.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM1) (s.gpr .rsi).toNat ((t.gpr .rax).setWidth 32) (VG.Proof.RsaPkcs1Sig.X86_64.Ver.pubOut s) ∧
    stackArg s 2 = s.gpr .rsi

def J3 (s t : State) : Prop :=
  VG.Proof.RsaPkcs1Sig.X86_64.Ver.J2 s t ∧ t.zf = some (!(VG.Proof.RsaPkcs1Sig.X86_64.Ver.pubOut s).isSome)

def J4 (s t : State) : Prop :=
  VG.Proof.RsaPkcs1Sig.X86_64.Ver.Env s t ∧ t.gpr .r8 = VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM2 ∧ t.gpr .rcx = s.gpr .rsi ∧
    t.gpr .rdx = ((s.gpr .r8).setWidth 32).setWidth 64 ∧ t.gpr .rsi = s.gpr .r9 ∧ t.gpr .r9 = stackArg s 0

/-! ## The call -/

/-- The registers a callee sees, from the caller's. -/
theorem entry_regs (t : State) (rd wr : List Region) :
    [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp].map (t.callEntry.withRegions rd wr).gpr =
      [t.gpr .rdi, t.gpr .rsi, t.gpr .rdx, t.gpr .rcx, t.gpr .r8, t.gpr .r9, t.gpr .rsp - 8] := by
  simp only [List.map_cons, List.map_nil, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide)]

theorem regs_eq {s₁ s₂ : State}
    (h : [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp].map s₁.gpr = [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp].map s₂.gpr) :
    ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₁.gpr r = s₂.gpr r :=
  List.map_inj_left.mp h

/-- A caller's buffer, read by the callee: the same as at the entry. -/
theorem entryBytes {s t : State} (he : VG.Proof.RsaPkcs1Sig.X86_64.Ver.Env s t) (rd wr : List Region) {p : Addr} {len : Nat}
    (hk : (VG.Proof.RsaPkcs1Sig.X86_64.Ver.stkR s).Disjoint ⟨p, len⟩) (hs : (VG.Proof.RsaPkcs1Sig.X86_64.Ver.scrR s).Disjoint ⟨p, len⟩) (hl : len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt (t.callEntry.withRegions rd wr).mem p len = Spec.Rsa.bytesAt s.mem p len := by
  rw [State.withRegions_mem]
  exact bytes_of_frame (frame_call he.mem (callEntry_frame he.rsp) fun r hr => by
    rw [List.mem_singleton.mp hr]; exact .inl (below_sub s)) hk hs hl

/-- What `vg_rsa_public_checked`'s contract makes public. -/
theorem pub_view {a s t : State} (S : VG.Proof.RsaPkcs1Sig.X86_64.Ver.Sib a s) (h : VG.Proof.RsaPkcs1Sig.X86_64.Ver.J1 s t) :
    [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp].map (t.callEntry.withRegions (pubRd s) (pubWr s)).gpr =
      [VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb a) oEM1, a.gpr .rsi, a.gpr .rdi, a.gpr .rsi, a.gpr .rdx, a.gpr .rcx, VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb a - 8] ∧
    stackArg (t.callEntry.withRegions (pubRd s) (pubWr s)) 0 = stackArg a 1 ∧
    stackArg (t.callEntry.withRegions (pubRd s) (pubWr s)) 1 = a.gpr .rsi ∧
    stackArg (t.callEntry.withRegions (pubRd s) (pubWr s)) 2 = stackArg a 3 ∧
    stackArg (t.callEntry.withRegions (pubRd s) (pubWr s)) 3 = stackArg a 4 ∧
    Spec.Rsa.bytesAt (t.callEntry.withRegions (pubRd s) (pubWr s)).mem
      ((t.callEntry.withRegions (pubRd s) (pubWr s)).gpr .rdx)
      ((t.callEntry.withRegions (pubRd s) (pubWr s)).gpr .rcx).toNat =
      Spec.Rsa.bytesAt a.mem (a.gpr .rdi) (a.gpr .rsi).toNat ∧
    Spec.Rsa.bytesAt (t.callEntry.withRegions (pubRd s) (pubWr s)).mem
      ((t.callEntry.withRegions (pubRd s) (pubWr s)).gpr .r8)
      ((t.callEntry.withRegions (pubRd s) (pubWr s)).gpr .r9).toNat =
      Spec.Rsa.bytesAt a.mem (a.gpr .rdx) (a.gpr .rcx).toNat := by
  obtain ⟨he, hw0, hw1, hw2, hw3, hdi, hsi, hdx, hcx, h8, h9, -⟩ := h
  have hp := preV_of S.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [VG.Proof.RsaPkcs1Sig.X86_64.Ver.entry_regs, hdi, hsi, hdx, hcx, h8, h9, he.rsp, S.fb, S.gpr (r := .rsi) (by decide),
      S.gpr (r := .rdi) (by decide), S.gpr (r := .rdx) (by decide), S.gpr (r := .rcx) (by decide)]
  · rw [stackArg_entry he.rsp _ _ (by decide), ← S.arg (by decide)]; exact hw0
  · rw [stackArg_entry he.rsp _ _ (by decide), ← S.gpr (r := .rsi) (by decide)]; exact hw1
  · rw [stackArg_entry he.rsp _ _ (by decide), ← S.arg (by decide)]; exact hw2
  · rw [stackArg_entry he.rsp _ _ (by decide), ← S.arg (by decide)]; exact hw3
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), hdx, hcx]
    rw [VG.Proof.RsaPkcs1Sig.X86_64.Ver.entryBytes he _ _ hp.dKn hp.dns.symm (by have := hp.wN; omega), S.n]
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide), h8, h9]
    rw [VG.Proof.RsaPkcs1Sig.X86_64.Ver.entryBytes he _ _ hp.dKe hp.des.symm (by have := hp.wE; omega), S.e]

theorem call_ct (v : PubImpl) : RelCT isa (Two (VG.Proof.RsaPkcs1Sig.X86_64.Ver.At VG.Proof.RsaPkcs1Sig.X86_64.Ver.J1)) (.call v.name v.code) fun _ _ => True := by
  refine RelCT.callEx (k := pubChk) v.ok v.ct fun t₁ t₂ ⟨a, ⟨s₁, S₁, j₁⟩, ⟨s₂, S₂, j₂⟩⟩ => ?_
  obtain ⟨r₁, a0₁, a1₁, a2₁, a3₁, n₁, e₁⟩ := VG.Proof.RsaPkcs1Sig.X86_64.Ver.pub_view S₁ j₁
  obtain ⟨r₂, a0₂, a1₂, a2₂, a3₂, n₂, e₂⟩ := VG.Proof.RsaPkcs1Sig.X86_64.Ver.pub_view S₂ j₂
  obtain ⟨c₁, w₁⟩ := pub_covers (preV_of S₁.1) j₁.2.2.2.2.2.2.2.2.2.2.2 j₁.1
  obtain ⟨c₂, w₂⟩ := pub_covers (preV_of S₂.1) j₂.2.2.2.2.2.2.2.2.2.2.2 j₂.1
  obtain ⟨he₁, hw0₁, hw1₁, hw2₁, hw3₁, hdi₁, hsi₁, hdx₁, hcx₁, h8₁, h9₁, hg₁⟩ := j₁
  obtain ⟨he₂, hw0₂, hw1₂, hw2₂, hw3₂, hdi₂, hsi₂, hdx₂, hcx₂, h8₂, h9₂, hg₂⟩ := j₂
  have p₁ := pub_pre (preV_of S₁.1) hg₁ he₁.rsp hw0₁ hw1₁ hw2₁ hw3₁ hdi₁ hsi₁ hdx₁ hcx₁ h8₁ h9₁
  have p₂ := pub_pre (preV_of S₂.1) hg₂ he₂.rsp hw0₂ hw1₂ hw2₂ hw3₂ hdi₂ hsi₂ hdx₂ hcx₂ h8₂ h9₂
  have hpub : pubChk.pub (t₁.callEntry.withRegions (pubRd s₁) (pubWr s₁))
      (t₂.callEntry.withRegions (pubRd s₂) (pubWr s₂)) :=
    ⟨VG.Proof.RsaPkcs1Sig.X86_64.Ver.regs_eq (r₁.trans r₂.symm), a0₁.trans a0₂.symm, a1₁.trans a1₂.symm, a2₁.trans a2₂.symm,
      a3₁.trans a3₂.symm, n₁.trans n₂.symm, e₁.trans e₂.symm⟩
  exact ⟨pubRd s₁, pubWr s₁, pubRd s₂, pubWr s₂, p₁, p₂, hpub, c₁, w₁, c₂, w₂,
    by rw [he₁.rsp, he₂.rsp, S₁.fb, S₂.fb]⟩

/-! ## The pieces -/

theorem lenCheck_two : RelCT isa (Two (VG.Proof.RsaPkcs1Sig.X86_64.Ver.At VG.Proof.RsaPkcs1Sig.X86_64.Ver.J0)) (.block lenCheck) (Two (VG.Proof.RsaPkcs1Sig.X86_64.Ver.At VG.Proof.RsaPkcs1Sig.X86_64.Ver.JL)) :=
  two_piece [.rsp] (fun _ _ _ h₁ h₂ r hr => by
      rw [List.mem_singleton.mp hr]
      exact VG.Proof.RsaPkcs1Sig.X86_64.Ver.pin (fun s => s.gpr .rsp) (fun s t h => by rw [h]) (fun _ _ S => S.gpr (by decide)) h₁ h₂)
    (by taint_decide)
    fun _ t ⟨s, S, ht⟩ => by
      rw [show t = s from ht]
      exact WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.Ver.lenCheck_ok (preV_of S.1)) fun _ h => ⟨s, S, h⟩

theorem pubArgs_two : RelCT isa (Two (VG.Proof.RsaPkcs1Sig.X86_64.Ver.At VG.Proof.RsaPkcs1Sig.X86_64.Ver.JA)) (.block pubArgs) (Two (VG.Proof.RsaPkcs1Sig.X86_64.Ver.At VG.Proof.RsaPkcs1Sig.X86_64.Ver.J1)) :=
  two_piece [.rsp] (VG.Proof.RsaPkcs1Sig.X86_64.Ver.pins_rsp fun s t ⟨t₀, ⟨k₀, _, _⟩, _, ht⟩ => by
      subst ht; show t₀.gpr .rsp - _ = _; rw [k₀.gpr (by decide)]) (by taint_decide)
    fun _ t ⟨s, S, t₀, ⟨k₀, hm₀, _⟩, hg, ht⟩ => by
      subst ht
      have g₀ : ∀ r, r ≠ .rax → t₀.gpr r = s.gpr r := fun r h => k₀.gpr (by simpa using h)
      have hsp₀ : t₀.gpr .rsp = s.gpr .rsp := g₀ _ (by decide)
      have hA : VG.Proof.MlKem.X86_64.Keep [.rax] (allocState VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes s) (allocState VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes t₀) :=
        ⟨fun r hr => by
          simp only [VG.Proof.RsaPkcs1Sig.X86_64.Ver.allocState_gpr, VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb, hsp₀]
          split
          · rfl
          · exact g₀ r (by simpa using hr), k₀.2.1, by simp only [allocState, hsp₀, k₀.2.2]⟩
      exact WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.Ver.pubArgs_ok (preV_of S.1) hA hm₀)
        fun _ ⟨he, hw0, hw1, hw2, hw3, hdi, hsi, hdx, hcx, h8, h9, _⟩ =>
          ⟨s, S, he, hw0, hw1, hw2, hw3, hdi, hsi, hdx, hcx, h8, h9, hg⟩

theorem call_two (v : PubImpl) : RelCT isa (Two (VG.Proof.RsaPkcs1Sig.X86_64.Ver.At VG.Proof.RsaPkcs1Sig.X86_64.Ver.J1)) (.call v.name v.code) (Two (VG.Proof.RsaPkcs1Sig.X86_64.Ver.At VG.Proof.RsaPkcs1Sig.X86_64.Ver.J2)) :=
  two_post (VG.Proof.RsaPkcs1Sig.X86_64.Ver.call_ct v) fun _ _ ⟨s, S, he, hw0, hw1, hw2, hw3, hdi, hsi, hdx, hcx, h8, h9, hg⟩ =>
    WP.mono (pub_call v (preV_of S.1) hg he hw0 hw1 hw2 hw3 hdi hsi hdx hcx h8 h9) fun _ h =>
      ⟨s, S, h.1, h.2.1, hg⟩

theorem test0_two : RelCT isa (Two (VG.Proof.RsaPkcs1Sig.X86_64.Ver.At VG.Proof.RsaPkcs1Sig.X86_64.Ver.J2)) (.block test0) (Two (VG.Proof.RsaPkcs1Sig.X86_64.Ver.At VG.Proof.RsaPkcs1Sig.X86_64.Ver.J3)) :=
  two_piece [] (fun _ _ _ _ _ _ h => absurd h List.not_mem_nil) (by taint_decide)
    fun _ t ⟨s, S, he, hw, hg⟩ => WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.Ver.test0_ok t) fun u ⟨hs, hz⟩ =>
      ⟨s, S, ⟨he.regs (by rw [hs.1]) hs.2.1 hs.2.2.1 hs.2.2.2, by rw [hs.2.1, hs.1]; exact hw, hg⟩, by
        rw [hz, VG.Proof.RsaPkcs1Sig.X86_64.Ver.written_r hw]; cases (VG.Proof.RsaPkcs1Sig.X86_64.Ver.pubOut s).isSome <;> rfl⟩

theorem ret0_ct {Φ : State → State → Prop} : RelCT isa (Two Φ) ret0 fun _ _ => True :=
  two_taint [] (fun _ _ _ _ _ _ h => absurd h List.not_mem_nil) (by taint_decide)

theorem encArgs_two : RelCT isa (Two fun a t => VG.Proof.RsaPkcs1Sig.X86_64.Ver.At VG.Proof.RsaPkcs1Sig.X86_64.Ver.J3 a t ∧ isa.eval .e t = some false) (.block encArgs)
    (Two (VG.Proof.RsaPkcs1Sig.X86_64.Ver.At VG.Proof.RsaPkcs1Sig.X86_64.Ver.J4)) :=
  two_piece [.rsp] (fun _ _ _ h₁ h₂ r hr => by
      rw [List.mem_singleton.mp hr]
      exact VG.Proof.RsaPkcs1Sig.X86_64.Ver.pins_rsp (J := VG.Proof.RsaPkcs1Sig.X86_64.Ver.J3) (fun _ _ h => h.1.1.rsp) _ _ _ h₁.1 h₂.1 _ (List.mem_singleton_self _))
    (by taint_decide)
    fun _ t ⟨⟨s, S, ⟨he, _, _⟩, _⟩, _⟩ => WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.Ver.encArgs_ok (preV_of S.1) he)
      fun u ⟨hK, hm, h8, hcx, hdx, hsi, h9⟩ =>
        ⟨s, S, he.regs (hK.gpr (by decide)) hm hK.2.1 hK.2.2, h8, hcx, hdx, hsi, h9⟩

theorem encTail_ct : RelCT isa (Two (VG.Proof.RsaPkcs1Sig.X86_64.Ver.At VG.Proof.RsaPkcs1Sig.X86_64.Ver.J4)) (.seq encode VG.Impl.RsaPkcs1Sig.X86_64.Verify.tail) fun _ _ => True :=
  VG.Proof.RsaPkcs1Sig.X86_64.Ver.encTail_taint fun _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact VG.Proof.RsaPkcs1Sig.X86_64.Ver.pin VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb (fun _ _ h => h.1.rsp) (fun _ _ S => S.fb) h₁ h₂
    · exact VG.Proof.RsaPkcs1Sig.X86_64.Ver.pin (fun s => VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM2) (fun _ _ h => h.2.1) (fun _ _ S => by rw [S.fb]) h₁ h₂
    · exact VG.Proof.RsaPkcs1Sig.X86_64.Ver.pin (fun s => s.gpr .rsi) (fun _ _ h => h.2.2.1) (fun _ _ S => S.gpr (by decide)) h₁ h₂
    · exact VG.Proof.RsaPkcs1Sig.X86_64.Ver.pin (fun s => ((s.gpr .r8).setWidth 32).setWidth 64) (fun _ _ h => h.2.2.2.1)
        (fun _ _ S => by rw [S.r8]) h₁ h₂
    · exact VG.Proof.RsaPkcs1Sig.X86_64.Ver.pin (fun s => s.gpr .r9) (fun _ _ h => h.2.2.2.2.1) (fun _ _ S => S.gpr (by decide)) h₁ h₂
    · exact VG.Proof.RsaPkcs1Sig.X86_64.Ver.pin (fun s => stackArg s 0) (fun _ _ h => h.2.2.2.2.2) (fun _ _ S => S.arg (by decide)) h₁ h₂

theorem afterPub_ct : RelCT isa (Two (VG.Proof.RsaPkcs1Sig.X86_64.Ver.At VG.Proof.RsaPkcs1Sig.X86_64.Ver.J2)) afterPub fun _ _ => True := by
  unfold afterPub
  refine RelCT.seq VG.Proof.RsaPkcs1Sig.X86_64.Ver.test0_two (two_ite ?_ VG.Proof.RsaPkcs1Sig.X86_64.Ver.ret0_ct (RelCT.seq VG.Proof.RsaPkcs1Sig.X86_64.Ver.encArgs_two VG.Proof.RsaPkcs1Sig.X86_64.Ver.encTail_ct))
  refine VG.Proof.RsaPkcs1Sig.X86_64.Ver.pinEval (fun s => if stackArg s 2 = s.gpr .rsi then some (!(VG.Proof.RsaPkcs1Sig.X86_64.Ver.pubOut s).isSome) else none)
    (fun s t h => by simp only [VG.X86_64.eval, h.2, h.1.2.2, ↓reduceIte]) ?_
  intro a s S
  have he : (stackArg s 2 = s.gpr .rsi) = (stackArg a 2 = a.gpr .rsi) := by
    rw [S.arg (by decide), S.gpr (by decide)]
  by_cases hs : stackArg s 2 = s.gpr .rsi
  · have ha : stackArg a 2 = a.gpr .rsi := he ▸ hs
    simp only [hs, ha, ↓reduceIte, VG.Proof.RsaPkcs1Sig.X86_64.Ver.pubOut_sib S hs]
  · have ha : ¬ stackArg a 2 = a.gpr .rsi := he ▸ hs
    simp only [hs, ha, ↓reduceIte]

theorem body_ct (v : PubImpl) : RelCT isa (Two (VG.Proof.RsaPkcs1Sig.X86_64.Ver.At VG.Proof.RsaPkcs1Sig.X86_64.Ver.JA)) (VG.Impl.RsaPkcs1Sig.X86_64.Verify.body v.name v.code) fun _ _ => True :=
  RelCT.seq VG.Proof.RsaPkcs1Sig.X86_64.Ver.pubArgs_two (RelCT.seq (VG.Proof.RsaPkcs1Sig.X86_64.Ver.call_two v) VG.Proof.RsaPkcs1Sig.X86_64.Ver.afterPub_ct)

/-! ## The frame -/

theorem alloc_push {s s₁ : State} (h : isa.push (.alloc VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes) s = some s₁) : s₁ = allocState VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes s := by
  simp only [isa, push] at h
  split at h
  · cases h; rfl
  · cases h

/-- A frame of `frameBytes` bytes leaks what its body does. -/
theorem relCT_alloc {body : Prog isa} {P R : State → State → Prop}
    (hb : RelCT isa (fun a b => ∃ s₁ s₂, P s₁ s₂ ∧ a = allocState VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes s₁ ∧ b = allocState VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes s₂)
      body R) :
    RelCT isa P (.frame (.alloc VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes) body (.free VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes)) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | frame p₁ b₁ q₁ =>
    cases e₂ with
    | frame p₂ b₂ q₂ =>
      obtain rfl := VG.Proof.RsaPkcs1Sig.X86_64.Ver.alloc_push p₁
      obtain rfl := VG.Proof.RsaPkcs1Sig.X86_64.Ver.alloc_push p₂
      obtain ⟨rfl, -⟩ := hb _ _ _ _ _ _ ⟨s₁, s₂, hp, rfl, rfl⟩ b₁ b₂
      exact ⟨rfl, trivial⟩

theorem code_ct (v : PubImpl) : RelCT isa (Two (VG.Proof.RsaPkcs1Sig.X86_64.Ver.At VG.Proof.RsaPkcs1Sig.X86_64.Ver.J0)) (VG.Impl.RsaPkcs1Sig.X86_64.Verify.code v.name v.code) fun _ _ => True := by
  unfold VG.Impl.RsaPkcs1Sig.X86_64.Verify.code
  refine RelCT.seq VG.Proof.RsaPkcs1Sig.X86_64.Ver.lenCheck_two (two_ite ?_ VG.Proof.RsaPkcs1Sig.X86_64.Ver.ret0_ct (VG.Proof.RsaPkcs1Sig.X86_64.Ver.relCT_alloc ((VG.Proof.RsaPkcs1Sig.X86_64.Ver.body_ct v).mono ?_ fun _ _ h => h)))
  · refine VG.Proof.RsaPkcs1Sig.X86_64.Ver.pinEval (fun s => some (!(stackArg s 2 == s.gpr .rsi))) (fun s t h => by simp only [VG.X86_64.eval, h.2.2, Option.map_some]) ?_
    intro a s S
    rw [S.arg (by decide), S.gpr (by decide)]
  · rintro _ _ ⟨t₁, t₂, ⟨a, ⟨⟨s₁, S₁, j₁⟩, e₁⟩, ⟨⟨s₂, S₂, j₂⟩, e₂⟩⟩, rfl, rfl⟩
    have hg : ∀ {s t}, VG.Proof.RsaPkcs1Sig.X86_64.Ver.JL s t → isa.eval .ne t = some false → stackArg s 2 = s.gpr .rsi := fun j e => by
      simp only [VG.X86_64.eval, j.2.2, Option.map_some, Option.some.injEq, Bool.not_eq_false', beq_iff_eq] at e
      exact e
    exact ⟨a, ⟨s₁, S₁, t₁, j₁, hg j₁ e₁, rfl⟩, ⟨s₂, S₂, t₂, j₂, hg j₂ e₂, rfl⟩⟩

theorem code_constantTime (v : PubImpl) :
    ConstantTime isa verContract.pre verContract.pub (VG.Impl.RsaPkcs1Sig.X86_64.Verify.code v.name v.code) :=
  RelCT.constantTime ((VG.Proof.RsaPkcs1Sig.X86_64.Ver.code_ct v).mono
    (fun s₁ s₂ ⟨h₁, h₂, hpub⟩ => ⟨s₁, ⟨s₁, ⟨h₁, VG.Proof.RsaPkcs1Sig.X86_64.Ver.pub_refl s₁⟩, rfl⟩, ⟨s₂, ⟨h₂, hpub⟩, rfl⟩⟩) fun _ _ h => h)

/-! ## `Verified` -/

/-- `vg_rsa_pkcs1_verify`, calling the implementation `v` of
`vg_rsa_public_checked`, meets the shared contract. -/
theorem code_verified (v : PubImpl) :
    Verified target (VG.Impl.RsaPkcs1Sig.X86_64.Verify.code v.name v.code) (Spec.RsaPkcs1Sig.verifyContract abi verStack) :=
  have hct : ConstantTime isa verContract.pre verContract.pub (VG.Impl.RsaPkcs1Sig.X86_64.Verify.code v.name v.code) := VG.Proof.RsaPkcs1Sig.X86_64.Ver.code_constantTime v
  Verified.of_correct (k := verContract) (VG.Proof.RsaPkcs1Sig.X86_64.Ver.code_correct v) hct verify_implies

/-- It writes `rsp` only in its frame's push and pop. -/
theorem code_spSafe (v : PubImpl) : (VG.Impl.RsaPkcs1Sig.X86_64.Verify.code v.name v.code).all (fun i => !isa.writesSp i) = true := by
  simp only [VG.Impl.RsaPkcs1Sig.X86_64.Verify.code, VG.Impl.RsaPkcs1Sig.X86_64.Verify.body, Code.all, v.spSafe, Bool.true_and]
  decide +kernel

end VG.Proof.RsaPkcs1Sig.X86_64.Ver

end
