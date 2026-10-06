import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.NFin
import VerifiedGarbage.Proof.Bignum.X86_64.CrtEntry

/-!
# An RSA key from its primes on x86-64: the entry and the head

`entry` saves the callee-saved registers and the arguments in the header,
with its base in `rdi` (`keyEntry_ok`); `head` sets up the working space
for `W = n_len / 8` words (`keyHead_ok`).
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate (kE kElen)

theorem keyEntry_eq : entry = ([.mov .r11 (.mem { base := .rsp, disp := 88 }),
    .store (hdr11 0) .rbx, .store (hdr11 1) .rbp, .store (hdr11 2) .r12, .store (hdr11 3) .r13,
    .store (hdr11 4) .r14, .store (hdr11 5) .r15,
    .store (hdr11 kNo) .rdi, .store (hdr11 kNl) .rsi, .store (hdr11 kDo) .rdx, .store (hdr11 kPp) .r8,
    .store (hdr11 kPl) .r9] : List Instr) ++
    (crtPairs [(0, kQp), (2, kDp), (4, kDq), (6, kQi), (8, kE), (9, kElen)] ++
      ([.mov .rdi (.reg .r11)] : List Instr)) := rfl

/-- The header after the stores from registers. -/
def keyEntryMemA (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 vno vnl vdo vpp vpl : BitVec 64) : Mem :=
  ((((((((((m.writeW (off B (8 * 0)) v0).writeW (off B (8 * 1)) v1).writeW (off B (8 * 2)) v2).writeW
    (off B (8 * 3)) v3).writeW (off B (8 * 4)) v4).writeW (off B (8 * 5)) v5).writeW (off B (8 * kNo)) vno).writeW
    (off B (8 * kNl)) vnl).writeW (off B (8 * kDo)) vdo).writeW (off B (8 * kPp)) vpp).writeW (off B (8 * kPl)) vpl

/-- The header after the entry's stores. -/
def keyEntryMem (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 vno vnl vdo vpp vpl vqp vdp vdq vqi ve vel : BitVec 64) :
    Mem :=
  ((((((keyEntryMemA m B v0 v1 v2 v3 v4 v5 vno vnl vdo vpp vpl).writeW (off B (8 * kQp)) vqp).writeW
    (off B (8 * kDp)) vdp).writeW (off B (8 * kDq)) vdq).writeW (off B (8 * kQi)) vqi).writeW
    (off B (8 * kE)) ve).writeW (off B (8 * kElen)) vel

theorem keyEntryMemA_outside (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 vno vnl vdo vpp vpl : BitVec 64) :
    Outside B 0 (8 * 32) m (keyEntryMemA m B v0 v1 v2 v3 v4 v5 vno vnl vdo vpp vpl) := by
  unfold keyEntryMemA
  repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _)

theorem keyEntryMem_facts (m : Mem) (B : Addr)
    (v0 v1 v2 v3 v4 v5 vno vnl vdo vpp vpl vqp vdp vdq vqi ve vel : BitVec 64) :
    let m' := keyEntryMem m B v0 v1 v2 v3 v4 v5 vno vnl vdo vpp vpl vqp vdp vdq vqi ve vel
    word m' B (8 * 0) = v0 ∧ word m' B (8 * 1) = v1 ∧ word m' B (8 * 2) = v2 ∧ word m' B (8 * 3) = v3 ∧
    word m' B (8 * 4) = v4 ∧ word m' B (8 * 5) = v5 ∧ word m' B (8 * kNo) = vno ∧ word m' B (8 * kNl) = vnl ∧
    word m' B (8 * kDo) = vdo ∧ word m' B (8 * kPp) = vpp ∧ word m' B (8 * kPl) = vpl ∧
    word m' B (8 * kQp) = vqp ∧ word m' B (8 * kDp) = vdp ∧ word m' B (8 * kDq) = vdq ∧
    word m' B (8 * kQi) = vqi ∧ word m' B (8 * kE) = ve ∧ word m' B (8 * kElen) = vel ∧
    Outside B 0 (8 * 32) m m' := by
  intro m'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    unfold m' keyEntryMem keyEntryMemA
  all_goals first
    | (repeat (first | refine word_skip ?_ (by decide) (by decide) (by decide) |
        exact word_writeW_self _ _ _ _)); done
    | (repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _))

/-- What `entry` leaves. -/
structure KeyEntryPost (s t : State) (B : Addr) : Prop where
  rdi : t.gpr .rdi = B
  saved : ∀ i < 6, word t.mem B (8 * i) = s.gpr (saved.getD i .rax)
  no : word t.mem B (8 * kNo) = s.gpr .rdi
  nl : word t.mem B (8 * kNl) = s.gpr .rsi
  dd : word t.mem B (8 * kDo) = s.gpr .rdx
  pp : word t.mem B (8 * kPp) = s.gpr .r8
  pl : word t.mem B (8 * kPl) = s.gpr .r9
  qp : word t.mem B (8 * kQp) = stackArg s 0
  dp : word t.mem B (8 * kDp) = stackArg s 2
  dq : word t.mem B (8 * kDq) = stackArg s 4
  qi : word t.mem B (8 * kQi) = stackArg s 6
  e : word t.mem B (8 * kE) = stackArg s 8
  el : word t.mem B (8 * kElen) = stackArg s 9
  frame : Outside B 0 (8 * 32) s.mem t.mem
  keep : Keep [.r11, .rax, .rdi] s t

/-- `entry`: the header, from the arguments, and the working space's base
(stack argument 10) in `rdi`. -/
theorem keyEntry_ok {s : State} {B : Addr} (hB : stackArg s 10 = B)
    (hw : ∀ i < 32, InRegions s.wr (off B (8 * i)) 8)
    (ha : ∀ j < 11, InRegions (s.rd ++ s.wr) (stackArgAddr s j) 8)
    (hsep : ∀ j < 11, ∀ m', Outside B 0 (8 * 32) s.mem m' → m'.readW (stackArgAddr s j) 64 = stackArg s j) :
    WP isa (.block entry) s (KeyEntryPost s · B) := by
  have e10 : s.gpr .rsp + BitVec.ofInt 64 88 = stackArgAddr s 10 := rfl
  have hB' : s.mem.readW (stackArgAddr s 10) 64 = B := hB
  have ha10 := ha 10 (by decide)
  rw [keyEntry_eq, WP.block_append_iff]
  refine WP.mono (WP.keep [.r11] (Q := fun t => t.gpr .r11 = B ∧
      t.mem = keyEntryMemA s.mem B (s.gpr .rbx) (s.gpr .rbp) (s.gpr .r12) (s.gpr .r13) (s.gpr .r14)
        (s.gpr .r15) (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rdx) (s.gpr .r8) (s.gpr .r9)) ?_ rfl)
    fun t₁ ⟨⟨h11, hm₁⟩, k₁⟩ => ?_
  · xrun [State.ea, hdr11, e10, ha10, hB', hdrOff, hw 0 (by decide), hw 1 (by decide),
      hw 2 (by decide), hw 3 (by decide), hw 4 (by decide), hw 5 (by decide), hw kNo (by decide),
      hw kNl (by decide), hw kDo (by decide), hw kPp (by decide), hw kPl (by decide)]
    rfl
  rw [WP.block_append_iff]
  refine WP.mono (crtPairs_ok _ t₁ ?_ h11 (k₁.gpr (by decide)) k₁.2.1 k₁.2.2
    (by rw [hm₁]; exact keyEntryMemA_outside _ _ _ _ _ _ _ _ _ _ _ _ _)) fun t₂ ⟨hm₂, k₂⟩ => ?_
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by decide, ha _ (by decide), hsep _ (by decide), hw _ (by decide)⟩
  have h11₂ : t₂.gpr .r11 = B := (k₂.gpr (by decide)).trans h11
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = B ∧ t.mem = t₂.mem) (by xrun [h11₂]) rfl)
    fun t ⟨⟨hdi, hm⟩, k₃⟩ => ?_
  have hmem : t.mem = keyEntryMem s.mem B (s.gpr .rbx) (s.gpr .rbp) (s.gpr .r12) (s.gpr .r13) (s.gpr .r14)
      (s.gpr .r15) (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rdx) (s.gpr .r8) (s.gpr .r9) (stackArg s 0) (stackArg s 2)
      (stackArg s 4) (stackArg s 6) (stackArg s 8) (stackArg s 9) := by
    rw [hm, hm₂, hm₁]; rfl
  obtain ⟨h0, h1, h2, h3, h4, h5, hNo, hNl, hDo, hPp, hPl, hQp, hDp, hDq, hQi, hE, hEl, ho⟩ :=
    keyEntryMem_facts s.mem B (s.gpr .rbx) (s.gpr .rbp) (s.gpr .r12) (s.gpr .r13) (s.gpr .r14)
      (s.gpr .r15) (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rdx) (s.gpr .r8) (s.gpr .r9) (stackArg s 0) (stackArg s 2)
      (stackArg s 4) (stackArg s 6) (stackArg s 8) (stackArg s 9)
  rw [← hmem] at h0 h1 h2 h3 h4 h5 hNo hNl hDo hPp hPl hQp hDp hDq hQi hE hEl ho
  refine ⟨hdi, fun i hi => ?_, hNo, hNl, hDo, hPp, hPl, hQp, hDp, hDq, hQi, hE, hEl, ho,
    ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

theorem ofNat_shr3 {k : Nat} (hk : k < 2 ^ 64) : BitVec.ofNat 64 k >>> 3 = BitVec.ofNat 64 (k / 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk,
    Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow]

/-- `head`: `W = n_len / 8`, the arrays' bases and the stride. -/
theorem keyHead_ok {s : State} {B : Addr} {Z nl : Nat} (hs : Scr s B Z) (hdi : s.gpr .rdi = B)
    (hnl : word s.mem B (8 * kNl) = BitVec.ofNat 64 nl) (h16 : 16 ≤ nl) (hnl' : nl < 2 ^ 27)
    (hZ : slot (nl / 8) 16 ≤ Z) :
    WP isa (.block head) s fun t =>
      Ws t B Z (nl / 8) ∧ Frm B [(8 * sW, 8), (8 * sArr 0, 64), (8 * sStride, 8)] s.mem t.mem ∧
        Keep [.rax, .rcx, .rdx, .r12] s t := by
  have hn := hs.nowrap
  have h8 := hdr_lt_slot (nl / 8) 8 (show 31 < 32 by decide)
  have eW : sW = 6 := rfl
  have eA : sArr 0 = 8 := rfl
  have eS : sStride = 28 := rfl
  have eN : kNl = 17 := rfl
  have hl8 : slot (nl / 8) 8 ≤ slot (nl / 8) 16 := by unfold slot; omega
  unfold head
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.rcx, .r12] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 (nl / 8) ∧
      t.mem = s.mem.writeW (off B (8 * sW)) (BitVec.ofNat 64 (nl / 8))) ?_ rfl)
    fun t₁ ⟨⟨h12, hm₁⟩, k₁⟩ => ?_
  · xrun [State.ea, hdr, hdi, hdrOff, hs.ld (d := 8 * kNl) (by omega),
      hs.st (d := 8 * sW) (by omega), hnl, ofNat_shr3 (show nl < 2 ^ 64 by omega)]
  have hs₁ := hs.congr k₁.2.2
  refine WP.mono (setBases_ok hs₁ ((k₁.gpr (by decide)).trans hdi) h12 (by unfold sArr; omega))
    fun t₂ ⟨hb₂, ho₂, k₂⟩ => ?_
  have hs₂ := hs₁.congr k₂.2.2
  have hdi₂ : t₂.gpr .rdi = B := (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hdi)
  have h12₂ : t₂.gpr .r12 = BitVec.ofNat 64 (nl / 8) := (k₂.gpr (by decide)).trans h12
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = t₂.mem.writeW (off B (8 * sStride))
      (BitVec.ofNat 64 (8 * (nl / 8 + 2)))) (by
    xrun [State.ea, hdr, hdi₂, hdrOff, h12₂, hs₂.st (d := 8 * sStride) (by omega), ofNat_dbl]
    congr 1
    rw [show (2 : BitVec 64) = BitVec.ofNat 64 2 from rfl, ← BitVec.ofNat_add, ofNat_dbl, ofNat_dbl, ofNat_dbl]
    congr 1; omega) rfl) fun t ⟨hm, k₃⟩ => ?_
  have o1 := writeW_outside t₂.mem B (BitVec.ofNat 64 (8 * (nl / 8 + 2))) (d := 8 * sStride) (by omega)
  have hw : ∀ i < 32, i ≠ sStride → word t.mem B (8 * i) = word t₂.mem B (8 * i) :=
    fun i hi h1 => by rw [hm, o1.word (by omega) (by omega)]
  have kk := ((k₁.trans k₂).trans k₃)
  refine ⟨⟨hs₂.congr k₃.2.2, (k₃.gpr (by decide)).trans hdi₂, ?_, ?_, fun j hj => ?_, hZ, by omega,
    by omega⟩, ?_, kk.mono (by simp)⟩
  · rw [hw sW (by decide) (by decide), ho₂.word (by omega) (by omega), hm₁, word_writeW_self]
  · rw [hm, word_writeW_self]
  · rw [hw (sArr j) (by unfold sArr; omega) (by unfold sArr sStride sFn; omega)]
    exact hb₂ j hj
  · intro x hx
    have a := hx (8 * sW, 8) (by simp)
    have b := hx (8 * sArr 0, 64) (by simp)
    have c := hx (8 * sStride, 8) (by simp)
    dsimp only at a b c
    rw [hm, o1 x c, ho₂ x b, hm₁, writeW_outside s.mem B _ (by omega) x a]

end VG.Proof.RsaKeyGen.X86_64.Key
