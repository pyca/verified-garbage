module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Data
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Residue
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-! # FFDH parameter candidates on x86-64: the screen on p's octets

`outerScreen` decides `screen` from the octets of p in the output buffer,
before any workspace is set up: their sum is p modulo 255 (256 ≡ 1), and the
last octet is p modulo 256. -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Bignum.X86_64 (hdr at0)
open VG.Impl.Ffdh.X86_64.ParameterCandidate

private theorem bytesAt_snoc (m : Mem) (p : Addr) (n : Nat) :
    Spec.Rsa.bytesAt m p (n + 1) = Spec.Rsa.bytesAt m p n ++ [m (off p n)] := by
  simp [Spec.Rsa.bytesAt, List.range_succ, off]

private theorem os2ip_snoc' (l : List Byte) (b : Byte) :
    Spec.Rsa.os2ip (l ++ [b]) = 256 * Spec.Rsa.os2ip l + b.toNat := by
  simp only [Spec.Rsa.os2ip, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- After `j` octets of the sum. -/
structure SumInv (s₀ : State) (op : Addr) (n j : Nat) (t : State) : Prop where
  keep : Keep [.rax, .rsi, .r10, .rcx] s₀ t
  mem : t.mem = s₀.mem
  ptr : t.gpr .r10 = off op j
  count : t.gpr .rcx = BitVec.ofNat 64 (n - j)
  sum : (t.gpr .rsi).toNat % 255 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₀.mem op j) % 255
  small : (t.gpr .rsi).toNat ≤ 255 * j

theorem sumStep_ok {s₀ t : State} {op : Addr} {n j : Nat} (hn : n < 2 ^ 31) (hj : j < n)
    (hrd : ∀ i < n, InRegions (s₀.rd ++ s₀.wr) (off op i) 1) (h : SumInv s₀ op n j t) :
    WP isa (.block sumByte) t fun u => u.zf = some (decide (j + 1 = n)) ∧ SumInv s₀ op n (j + 1) u := by
  have hrd' : InRegions (t.rd ++ t.wr) (off op j) 1 := by rw [h.keep.2.1, h.keep.2.2]; exact hrd j hj
  have hb := (s₀.mem (off op j)).isLt
  refine WP.mono (WP.keep [.rax, .rsi, .r10, .rcx] (Q := fun u =>
    u.zf = some (decide (j + 1 = n)) ∧ u.gpr .r10 = off op (j + 1) ∧
      u.gpr .rcx = BitVec.ofNat 64 (n - (j + 1)) ∧
      (u.gpr .rsi).toNat = (t.gpr .rsi).toNat + (s₀.mem (off op j)).toNat ∧ u.mem = t.mem) ?_ rfl)
    fun u ⟨⟨hz, hp, hc, hs, hm⟩, k⟩ => ⟨hz, (h.keep.trans k).mono (by decide), hm.trans h.mem, hp, hc, ?_, ?_⟩
  · unfold sumByte
    have hsmall := h.small
    have hp1 : off op j + 1 = off op (j + 1) := by
      simp only [off, BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]
    have hz0 : BitVec.ofInt 64 0 = 0#64 := rfl
    xrun [State.ea, at0, h.ptr, hz0, BitVec.add_zero, hrd', h.mem, h.count, sx1, hp1]
    have hsub : BitVec.ofNat 64 (n - j) - 1 = BitVec.ofNat 64 (n - (j + 1)) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      have : (1 : BitVec 64).toNat = 1 := rfl
      rw [this]; omega
    rw [hsub]
    refine ⟨?_, rfl, ?_⟩
    · rw [show (BitVec.ofNat 64 (n - (j + 1)) == 0) = (BitVec.ofNat 64 (n - (j + 1)) - BitVec.ofNat 64 0 == 0)
        by rw [BitVec.sub_zero], ofNat_sub_beq (by omega) (by omega)]
      simp only [decide_eq_decide]
      omega
    · rw [BitVec.toNat_add, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : BitVec.toNat (s₀.mem (off op j)) < 2 ^ 64)]
      have := (t.gpr .rsi).isLt
      omega
  · rw [hs, bytesAt_snoc, os2ip_snoc', Nat.add_mod, h.sum, ← Nat.add_mod]
    omega
  · rw [hs]; have := h.small; omega

theorem sumLoop_ok {s : State} {op : Addr} {n : Nat} (hn1 : 1 ≤ n) (hn : n < 2 ^ 31)
    (hp : s.gpr .r10 = op) (hc : s.gpr .rcx = BitVec.ofNat 64 n) (hsi : s.gpr .rsi = 0)
    (hrd : ∀ i < n, InRegions (s.rd ++ s.wr) (off op i) 1) :
    WP isa (.loop (.block sumByte) .ne) s (SumInv s op n n) :=
  wp_upto (a := 0) (by omega) (SumInv s op n)
    (fun j _ hj t ht => sumStep_ok hn hj hrd ht) (fun _ h => h)
    ⟨Keep.refl _ _, rfl, by rw [hp]; simp [off], by rw [hc, Nat.sub_zero],
      by rw [hsi]; simp [Spec.Rsa.bytesAt, Spec.Rsa.os2ip], by rw [hsi]; simp⟩

private theorem os2ip_low {m : Mem} {op : Addr} {n k : Nat} (hn : 1 ≤ n) (hk : k ≤ 8) :
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt m op n) % 2 ^ k = (m (off op (n - 1))).toNat % 2 ^ k := by
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  rw [bytesAt_snoc, os2ip_snoc', Nat.add_sub_cancel]
  have hd : 2 ^ k ∣ 256 := by
    have := Nat.pow_dvd_pow 2 hk; simpa using this
  obtain ⟨c, hc⟩ := hd
  rw [hc, Nat.mul_assoc, Nat.mul_add_mod]

/-- `lowByte (2 ^ k - 1)`: ZF iff RAX is 1 and the octet before R10 is 3
modulo `2 ^ k`. -/
theorem lowByte_ok {s : State} {op : Addr} {n : Nat} {b : Bool} (k : Nat) (hk : 2 ≤ k) (hk' : k ≤ 8)
    (hn : 1 ≤ n) (hn' : n < 2 ^ 31) (hp : s.gpr .r10 = off op n)
    (hrd : InRegions (s.rd ++ s.wr) (off op (n - 1)) 1) (hax : s.gpr .rax = if b then 1 else 0) :
    WP isa (.block (lowByte (2 ^ k - 1))) s fun t =>
      t.zf = some (b && decide ((s.mem (off op (n - 1))).toNat % 2 ^ k = 3)) ∧ t.mem = s.mem ∧
        Keep [.rax, .rcx, .rdx] s t := by
  refine WP.mono (WP.keep [.rax, .rcx, .rdx] (Q := fun t =>
    t.zf = some (b && decide ((s.mem (off op (n - 1))).toNat % 2 ^ k = 3)) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨hz, hm⟩, kk⟩ => ⟨hz, hm, kk⟩
  have hm1 : BitVec.ofNat 64 n + BitVec.ofInt 64 (-1) = BitVec.ofNat 64 (n - 1) := by
    have : BitVec.ofInt 64 (-1) = BitVec.allOnes 64 := by decide
    rw [this]; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_allOnes]; omega
  have hea : off op n + BitVec.ofInt 64 (-1) = off op (n - 1) := by
    rw [off, BitVec.add_assoc, hm1]
  have h4 : 4 ≤ 2 ^ k := by
    have := Nat.pow_le_pow_right (n := 2) (by decide) hk; simpa using this
  have h8 : 2 ^ k ≤ 256 := by
    have := Nat.pow_le_pow_right (n := 2) (by decide) hk'; simpa using this
  have hmask : 2 ^ k - 1 < 2 ^ 31 := by omega
  generalize hx : s.mem (off op (n - 1)) = x
  have hlow : ((x.setWidth 64 &&& BitVec.signExtend 64 (BitVec.ofNat 32 (2 ^ k - 1))) -
      (3 : BitVec 64) == 0) = decide (x.toNat % 2 ^ k = 3) := by
    have hand : (x.setWidth 64 &&& BitVec.signExtend 64 (BitVec.ofNat 32 (2 ^ k - 1))).toNat = x.toNat % 2 ^ k := by
      rw [sx_ofNat hmask, BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by have := x.isLt; omega), Nat.mod_eq_of_lt (by omega),
        Nat.and_two_pow_sub_one_eq_mod]
    rw [sub_beq_zero]
    by_cases h : x.toNat % 2 ^ k = 3
    · simp only [h, decide_true, beq_iff_eq]
      apply BitVec.eq_of_toNat_eq; rw [hand, h]; rfl
    · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
      intro he; apply h; rw [← hand, he]; rfl
  unfold lowByte
  cases b <;> by_cases h : x.toNat % 2 ^ k = 3 <;>
    xrun [State.ea, hp, hea, hrd, hx, hax, sx_ofNat (show 3 < 2 ^ 31 by decide), hlow, h, execCmov, eval,
      Bool.not_true, Bool.not_false]

/-- p's octets in the output buffer: `outerScreen` decides `screen` from them. -/
abbrev outP (p : CandidateP) (m : Mem) : Nat := Spec.Rsa.os2ip (Spec.Rsa.bytesAt m p.op p.k)

theorem byteScreen_ok {p : CandidateP} {used : Nat} {s : State} {vals : List Nat} {k : Nat}
    (h : CandidateTape p used s) (hdi : s.gpr .rdi = p.B) (hvals : ∀ v ∈ vals, v < 2 ^ 31)
    (hk : 2 ≤ k) (hk' : k ≤ 8) :
    WP isa (byteScreen vals k) s fun t =>
      t.zf = some (decide (outP p s.mem % 255 ∈ vals) && decide (outP p s.mem % 2 ^ k = 3)) ∧
      t.mem = s.mem ∧ Keep [.rax, .rcx, .rdx, .rsi, .r10] s t := by
  have hrdh : ∀ j < 32, InRegions (s.rd ++ s.wr) (off p.B (8 * j)) 8 :=
    fun j hj => h.base.scr.ld (by omega_using [hj, h.base.header_room])
  have hOut := h.base.hdr (oOut, p.op) (by simp [CandidateP.headers])
  have hLen := h.base.hdr (oLen, BitVec.ofNat 64 p.k) (by simp [CandidateP.headers])
  have hw := h.base.widths
  have hout : ∀ i < p.k, InRegions (s.rd ++ s.wr) (off p.op i) 1 := fun i hi =>
    let ⟨r, hr, hc⟩ := h.base.out.wr i hi; ⟨r, List.mem_append_right _ hr, hc⟩
  unfold byteScreen
  refine WP.seq (WP.mono (WP.keep [.r10, .rcx, .rsi] (Q := fun u =>
    u.gpr .r10 = p.op ∧ u.gpr .rcx = BitVec.ofNat 64 p.k ∧ u.gpr .rsi = 0 ∧ u.mem = s.mem)
    (by xrun [State.ea, hdr, hdi, hdrOff, hOut, hLen, hrdh oOut (by decide), hrdh oLen (by decide)]) rfl)
    fun u ⟨⟨hp, hc, hsi, hm⟩, k₁⟩ => ?_)
  have hout' : ∀ i < p.k, InRegions (u.rd ++ u.wr) (off p.op i) 1 := fun i hi => by
    rw [k₁.2.1, k₁.2.2]; exact hout i hi
  refine WP.seq (WP.mono (sumLoop_ok (by omega) (by omega) hp hc hsi hout') fun v hv => ?_)
  refine WP.block_append (WP.block_append (WP.mono (reduce255_ok v) fun x ⟨hx, hmx, kx⟩ => ?_))
  have hr : (x.gpr .rsi).toNat = outP p s.mem % 255 := by
    rw [hx, hv.sum, hm]
  have hsi' : x.gpr .rsi = BitVec.ofNat 64 (outP p s.mem % 255) := by
    rw [← hr, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.mono (memberFlag_ok (by omega_arith) hvals hsi') fun y ⟨hy, hmy, ky⟩ => ?_
  have hp' : y.gpr .r10 = off p.op p.k := by rw [ky.gpr (by decide), kx.gpr (by decide), hv.ptr]
  have hrd' : InRegions (y.rd ++ y.wr) (off p.op (p.k - 1)) 1 := by
    rw [ky.2.1, ky.2.2, kx.2.1, kx.2.2, hv.keep.2.1, hv.keep.2.2]; exact hout' _ (by omega)
  refine WP.mono (lowByte_ok k hk hk' (by omega) (by omega) hp' hrd' hy) fun t ⟨hz, hmt, kt⟩ =>
    ⟨?_, hmt.trans (hmy.trans (hmx.trans (hv.mem.trans hm))), ?_⟩
  · rw [hz, hmy, hmx, hv.mem, hm, ← os2ip_low (by omega) hk']
  · exact ((((k₁.trans hv.keep).trans kx).trans ky).trans kt).mono (by decide)

/-- `outerScreen`: ZF is `screen` of p's octets. -/
theorem outerScreen_ok {p : CandidateP} {used : Nat} {s : State}
    (h : CandidateTape p used s) (hdi : s.gpr .rdi = p.B) :
    WP isa outerScreen s fun t => t.zf = some (screen p.gen (outP p s.mem)) ∧ t.mem = s.mem ∧
      Keep [.rax, .rcx, .rdx, .rsi, .r10] s t := by
  have hrdh : ∀ j < 32, InRegions (s.rd ++ s.wr) (off p.B (8 * j)) 8 :=
    fun j hj => h.base.scr.ld (by omega_using [hj, h.base.header_room])
  have hGen := h.base.hdr (oGen, BitVec.ofNat 64 p.gen) (by simp [CandidateP.headers])
  unfold outerScreen
  refine WP.seq (WP.mono (WP.keep [.rdx] (Q := fun u => u.zf = some (decide (p.gen = 2)) ∧ u.mem = s.mem)
    (by
      xrun [State.ea, hdr, hdi, hdrOff, hGen, hrdh oGen (by decide)]
      exact ofNat_sub_beq (N := 2) (by rcases h.base.gen with h | h <;> rw [h] <;> decide) (by decide)) rfl)
    fun u ⟨⟨hz, hm⟩, k₁⟩ => ?_)
  have hu : CandidateTape p used u := (h.same_mem hm k₁ (by decide)).1
  have hdu : u.gpr .rdi = p.B := (k₁.gpr (by decide)).trans hdi
  refine WP.ite (decide (p.gen = 2)) (by simp [eval, hz]) (fun hg => ?_) (fun hg => ?_)
  · have hg' : p.gen = 2 := of_decide_eq_true hg
    refine WP.mono (byteScreen_ok hu hdu allowed2_lt (by decide) (by decide)) fun t ⟨hz', hmt, kt⟩ =>
      ⟨?_, hmt.trans hm, (k₁.trans kt).mono (by decide)⟩
    rw [hz', hm]; simp only [screen, hg', ite_true, Bool.and_comm, show (2 : Nat) ^ 3 = 8 from rfl]
  · have hg' : ¬ p.gen = 2 := of_decide_eq_false hg
    refine WP.mono (byteScreen_ok hu hdu allowed5_lt (by decide) (by decide)) fun t ⟨hz', hmt, kt⟩ =>
      ⟨?_, hmt.trans hm, (k₁.trans kt).mono (by decide)⟩
    rw [hz', hm]; simp only [screen, hg', ite_false, Bool.and_comm, show (2 : Nat) ^ 2 = 4 from rfl]

end VG.Proof.Ffdh.X86_64.ParameterCandidate
