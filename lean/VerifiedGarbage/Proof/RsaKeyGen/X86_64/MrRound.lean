import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrWitAll

/-!
# A candidate on x86-64: one round of Miller–Rabin

`roundPre_ok`: the witness `b`, `b R mod c` into `aXm` and `aB`, and
`y := 1` (`R mod c` into `aY`).
-/

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- The octets of `rand` from `a`. -/
theorem Src.seg {s : State} {B : Addr} {Z : Nat} {rp : Addr} {r : List Byte} (h : Src s B Z rp r) {a n : Nat}
    (ha : a + n ≤ r.length) : Src s B Z (rp + BitVec.ofNat 64 a) (VG.Proof.RsaKeyGen.seg r a n) := by
  have hl : (VG.Proof.RsaKeyGen.seg r a n).length = n := by
    simp only [VG.Proof.RsaKeyGen.seg, List.length_take, List.length_drop]; omega_using [ha]
  have he : ∀ i, rp + BitVec.ofNat 64 a + BitVec.ofNat 64 i = rp + BitVec.ofNat 64 (a + i) := fun i => by
    rw [BitVec.add_assoc, BitVec.ofNat_add]
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [he]; exact h.rd (a + i) (by omega_using [ha, hl, hi])
  · rw [he, h.val (a + i) (by omega_using [ha, hl, hi])]
    simp only [VG.Proof.RsaKeyGen.seg, List.getElem_take, List.getElem_drop]
  · rw [he]; exact h.out (a + i) (by omega_using [ha, hl, hi])

/-- What the start of a round changes. -/
def preRanges (w : Nat) : List (Nat × Nat) :=
  witRanges w ++ [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aXm, 8 * (w + 2)),
    (slot w aB, 8 * (w + 2)), (slot w aY, 8 * (w + 2))]

theorem roundPre_eq (mul : Nat → Nat → Nat → Prog isa) :
    mrWitness ++ [mul aXm aX aR2,
      .block (([.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aXm)))] : List Instr) ++ extBase aB .rbx), copyWords,
      .block (([.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aY)))] : List Instr) ++ extBase aR1 .rsi), copyWords] =
    mrWitness ++ ([mul aXm aX aR2] ++
      (([.block (([.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aXm)))] : List Instr) ++ extBase aB .rbx), copyWords] : List (Prog isa)) ++
      ([.block (([.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aY)))] : List Instr) ++ extBase aR1 .rsi), copyWords] : List (Prog isa)))) := rfl

/-- `MrCtx` with a new witness. -/
theorem MrCtx.setB {s t : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} {c bm bm' : Nat} {rs : List (Nat × Nat)}
    (hc : MrCtx s B Z w mi c bm) (hd : MrDims B Z w) (hf : Frm B rs s.mem t.mem) (hs : Scr t B Z)
    (hdi : t.gpr .rdi = B) (hh : ∀ r ∈ rs, 128 ≤ r.1)
    (dN : ∀ r ∈ rs, slot w aN + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w aN)
    (d1 : ∀ r ∈ rs, slot w aR1 + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w aR1)
    (dm : ∀ r ∈ rs, slot w aRm1 + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w aRm1)
    (hb : wv t.mem B (slot w aB) w = bm') : MrCtx t B Z w mi c bm' := by
  have hn := hc.good.scr.nowrap
  have hx := hd.x
  have hb1 : slot w aRm1 + 8 * (w + 2) ≥ slot w aR1 + 8 * w := by unfold slot aRm1 aR1; omega_using []
  have hb0 : slot w aRm1 + 8 * (w + 2) ≥ slot w aN + 8 * w := by unfold slot aRm1 aN; omega_using []
  have := hd.w4
  refine ⟨⟨hs, hdi, Hdr.of_frm hc.good.hdr hf hh⟩, ?_, ?_, hb, ?_, ?_⟩
  · rw [hf.word_eq (d := slot w aN) (fun r hr => by have := dN r hr; omega_arith) (by omega_using [hn, hx, hb0, this])]; exact hc.inv
  · rw [hf.wv_eq dN (by omega_using [hn, hx, hb0])]; exact hc.n
  · rw [hf.wv_eq d1 (by omega_using [hn, hx, hb1])]; exact hc.r1
  · rw [hf.wv_eq dm (by omega_using [hn, hx])]; exact hc.rm1

/-- The start of a round. -/
theorem roundPre_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} {c bm : Nat}
    (hd : MrDims B Z w) (hc : MrCtx s B Z w mi c bm)
    (hR2 : wv s.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c) (hodd : c % 2 = 1) (hc1 : 1 < c)
    (hb : Spec.RsaKeyGen.bitLength (c - 1) = 64 * w)
    {rp : Addr} {used : Nat} {r : List Byte} (hR : word s.mem B (8 * kRand) = rp)
    (hU : word s.mem B (8 * kUsed) = BitVec.ofNat 64 used) (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w))
    (hsrc : Src s B Z rp r) (hlen : used + 8 * w ≤ r.length) :
    WP isa (seqs (mrWitness ++ [M.mm aXm aX aR2,
      .block (([.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aXm)))] : List Instr) ++ extBase aB .rbx), copyWords,
      .block (([.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aY)))] : List Instr) ++ extBase aR1 .rsi), copyWords])) s
      fun t =>
      MrCtx t B Z w mi c
        ((Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg r used (8 * w)))).1 *
          2 ^ (64 * w) % c) ∧
      wv t.mem B (slot w aY) w = 2 ^ (64 * w) % c ∧
      wv t.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c ∧
      word t.mem B (8 * kU) =
        mask (Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg r used (8 * w)))).2 ∧
      word t.mem B (8 * kUsed) = BitVec.ofNat 64 (used + 8 * w) ∧
      Frm B (preRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hg := hc.good
  have hZ := hd.z
  have hXZ := hd.x
  have hw4 := hd.w4
  have hw' : w < 2 ^ 31 := by have := hd.w64; omega_using [this]
  have hn := hg.scr.nowrap
  have hRc : Nat.Coprime (2 ^ (64 * w)) c := VG.Proof.Bignum.coprime_pow2 hodd _
  have hc0 : 0 < c := by omega_using [hc1]
  rw [roundPre_eq]
  refine wp_seqs_append (by simp [mrWitness]) (by simp) ?_
  refine WP.mono (mrWitness_ok hd hc hodd hb hR hU hK (VG.Proof.RsaKeyGen.X86_64.Src.seg hsrc hlen) (by
    simp only [VG.Proof.RsaKeyGen.seg, List.length_take, List.length_drop]; omega_using [hlen]))
    fun s₁ ⟨hc₁, hx₁, hu₁, hus₁, hf₁, k₁⟩ => ?_
  generalize hwt : Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg r used (8 * w))) = wt
    at hx₁ hu₁ ⊢
  have hR2₁ : wv s₁.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c := by
    rw [hf₁.wv_eq (d := slot w aR2) (k := w) (by simp only [witRanges]; rng_disj)
      (by have := slot_le (w := w) (show aR2 < 8 by decide); omega_using [hZ, hn, this])]; exact hR2
  -- `b R mod c` into `aXm`.
  refine wp_seqs_append (by simp) (by simp) ?_
  refine WP.mono (M.mm_ok hc₁.good hZ (by omega_using [hw4]) hw' (o := aXm) (a := aX) (b := aR2) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hc₁.inv
    (by rw [hR2₁, hc₁.n]; exact Nat.mod_lt _ hc0)) fun s₂ ⟨hg₂, hlt₂, hy₂, ha₂, k₂⟩ => ?_
  rw [hc₁.n] at hlt₂ hy₂
  rw [hx₁, hR2₁] at hy₂
  have hXm : wv s₂.mem B (slot w aXm) w = wt.1 * 2 ^ (64 * w) % c := by
    rw [← Nat.mod_eq_of_lt hlt₂]
    refine VG.Proof.Bignum.mont_cancel hRc ?_
    rw [hy₂, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_assoc]
  have hc₂ : MrCtx s₂ B Z w mi c bm := hc₁.of_frm hd (Frm.of_arrays ha₂
    (rs := [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aXm, 8 * (w + 2))]) (by simp))
    hg₂.scr hg₂.rdi (by rng_disj) (by rng_disj) (by rng_disj) (by rng_disj) (by rng_disj)
  -- `[aB] := b R mod c`.
  refine wp_seqs_append (by simp) (by simp) ?_
  refine WP.mono (copyToExt_ok hg₂ hZ (by omega_using [hw4]) hw' (a := aXm) (d := aB) (by decide) (by decide)
    (by unfold slot aB aRm1 at *; omega_arith)) fun s₃ ⟨hv₃, ho₃, k₃⟩ => ?_
  rw [hXm] at hv₃
  have hg₃ : Good s₃ B Z w mi := ⟨hg₂.scr.congr k₃.2.2, (k₃.gpr (by decide)).trans hg₂.rdi,
    Hdr.outside hg₂.hdr ho₃ (by unfold slot; omega_using [])⟩
  have hf₃ : Frm B [(slot w aB, 8 * (w + 2))] s₂.mem s₃.mem :=
    Frm.of_outside (ho₃.mono (o' := slot w aB) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega_using [])) (by simp)
  have hc₃ := hc₂.setB hd hf₃ hg₃.scr hg₃.rdi (by rng_disj) (by rng_disj) (by rng_disj) (by rng_disj) hv₃
  -- `[aY] := R mod c`.
  refine WP.mono (copyFromExt_ok hg₃ hZ (by omega_using [hw4]) hw' (a := aY) (d := aR1) (by decide) (by decide)
    (by unfold slot aR1 aRm1 at *; omega_arith)) fun t ⟨hv, ho, k⟩ => ?_
  rw [hc₃.r1] at hv
  have hgt : Good t B Z w mi := ⟨hg₃.scr.congr k.2.2, (k.gpr (by decide)).trans hg₃.rdi,
    Hdr.outside hg₃.hdr ho (by unfold slot; omega_using [])⟩
  have hft : Frm B [(slot w aY, 8 * (w + 2))] s₃.mem t.mem :=
    Frm.of_outside (ho.mono (o' := slot w aY) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega_using [])) (by simp)
  have hf23 : Frm B [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aXm, 8 * (w + 2)),
      (slot w aB, 8 * (w + 2)), (slot w aY, 8 * (w + 2))] s₁.mem t.mem :=
    ((Frm.of_arrays ha₂ (by simp)).trans (hf₃.mono (by simp))).trans (hft.mono (by simp))
  refine ⟨hc₃.of_frm hd hft hgt.scr hgt.rdi (by rng_disj) (by rng_disj) (by rng_disj) (by rng_disj) (by rng_disj),
    hv, ?_, ?_, ?_, ?_, ((((k₁.trans k₂).trans k₃).trans k).mono (by decide))⟩
  · rw [hf23.wv_eq (d := slot w aR2) (k := w) (by rng_disj)
      (by have := slot_le (w := w) (show aR2 < 8 by decide); omega_using [hZ, hn, this])]; exact hR2₁
  · rw [hf23.word_eq (d := 8 * kU) (by rng_disj) (by unfold kU sFn; omega_using [])]; exact hu₁
  · rw [hf23.word_eq (d := 8 * kUsed) (by rng_disj) (by unfold kUsed sFn; omega_using [])]; exact hus₁
  · exact (hf₁.mono fun r hr => List.mem_append_left _ hr).trans (hf23.mono (by simp))

theorem mask_and1' (c : Bool) : mask c &&& BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 c.toNat := by
  cases c <;> decide

theorem rcx_stat (a b : Bool) : ((mask a ||| mask b) &&& BitVec.signExtend 64 (3 : BitVec 32)) +
    BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 (if a || b then 4 else 1) := by
  cases a <;> cases b <;> decide

theorem rcx_stat2 (a b : Bool) : ((0#64 - (BitVec.ofBool a).setWidth 64 ||| 0#64 - (BitVec.ofBool b).setWidth 64) &&&
    (3 : BitVec 64)) + 1 = BitVec.ofNat 64 (if a || b then 4 else 1) := by
  cases a <;> cases b <;> decide

/-- The end of a round: `kStat := 3` if the witness proves `c` composite;
otherwise the witness counts, and `kStat := 4` to go on or 1. -/
theorem roundTail_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z)
    {f u : Bool} {i uni ch : Nat} (hF : word s.mem B (8 * kFlag) = mask f) (hI : word s.mem B (8 * kI) = BitVec.ofNat 64 i)
    (hU : word s.mem B (8 * kU) = mask u) (hN : word s.mem B (8 * kUni) = BitVec.ofNat 64 uni)
    (hC : word s.mem B (8 * kChecks) = BitVec.ofNat 64 ch) (hi : i < 2 ^ 62) (huni : uni < 2 ^ 62) (hch : ch < 2 ^ 62) :
    WP isa (seqs [.block [.mov32 .rcx (.imm 3), .mov .rax (.mem (hdr kFlag)), .alu .test .rax (.reg .rax)],
      .ite .e (.block [])
        (.block [.mov .rax (.mem (hdr kI)), .alu .add .rax (.imm 1), .store (hdr kI) .rax,
          .mov .rdx (.mem (hdr kU)), .alu .and .rdx (.imm 1), .alu .add .rdx (.mem (hdr kUni)), .store (hdr kUni) .rdx,
          .alu .cmp .rax (.imm 17), .alu .sbb .rcx (.reg .rcx), .alu .cmp .rdx (.mem (hdr kChecks)),
          .alu .sbb .rax (.reg .rax), .alu .or .rcx (.reg .rax), .alu .and .rcx (.imm 3), .alu .add .rcx (.imm 1)]),
      .block [.store (hdr kStat) .rcx]]) s fun t =>
      t.mem = (if f then ((s.mem.writeW (off B (8 * kI)) (BitVec.ofNat 64 (i + 1))).writeW (off B (8 * kUni))
          (BitVec.ofNat 64 (uni + u.toNat))).writeW (off B (8 * kStat))
          (BitVec.ofNat 64 (if i + 1 < 17 ∨ uni + u.toNat < ch then 4 else 1))
        else s.mem.writeW (off B (8 * kStat)) (BitVec.ofNat 64 3)) ∧ Keep [.rax, .rcx, .rdx] s t := by
  have hn := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega_using [hZ, this])
  have hs : ∀ i < 32, InRegions s.wr (off B (8 * i)) 8 := fun i hi =>
    hg.scr.st (by have := hdr_lt_slot w 8 hi; omega_using [hZ, this])
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.rcx, .rax] (Q := fun t => t.gpr .rcx = BitVec.ofNat 64 3 ∧
      t.zf = some (!f) ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl kFlag (by decide), hF, BitVec.and_self]
    cases f <;> decide) rfl) fun s₁ ⟨⟨hcx₁, hz₁, hm₁⟩, k₁⟩ => ?_)
  have hdi₁ : s₁.gpr .rdi = B := (k₁.gpr (by decide)).trans hg.rdi
  refine WP.seq (WP.ite (!f) (by simp [eval, hz₁]) (fun hf => ?_) (fun hf => ?_))
  · simp only [Bool.not_eq_true'] at hf
    refine WP.block_nil (WP.mono (WP.keep [] (Q := fun t => t.mem = s.mem.writeW (off B (8 * kStat))
      (BitVec.ofNat 64 3)) (by
      xrun [State.ea, hdr, hdi₁, hdrOff, show s₁.wr = s.wr from k₁.2.2 ▸ rfl, hs kStat (by decide), hcx₁, hm₁]
      ) rfl) fun t ⟨hm, k⟩ => ⟨by rw [hm, hf]; rfl, (k₁.trans k).mono (by decide)⟩)
  · simp only [Bool.not_eq_false'] at hf
    have hs₁ := hg.scr.congr k₁.2.2
    have hst : ∀ i < 32, InRegions s₁.wr (off B (8 * i)) 8 := fun i hi => by rw [k₁.2.2]; exact hs i hi
    have hld : ∀ i < 32, InRegions (s₁.rd ++ s₁.wr) (off B (8 * i)) 8 := fun i hi => by
      rw [k₁.2.1, k₁.2.2]; exact hl i hi
    refine WP.mono (WP.keep [.rax, .rdx, .rcx] (Q := fun t =>
        t.gpr .rcx = BitVec.ofNat 64 (if i + 1 < 17 ∨ uni + u.toNat < ch then 4 else 1) ∧
        t.mem = (s.mem.writeW (off B (8 * kI)) (BitVec.ofNat 64 (i + 1))).writeW (off B (8 * kUni))
          (BitVec.ofNat 64 (uni + u.toNat))) (by
      xrun [State.ea, hdr, hdi₁, hdrOff, hld kI (by decide), hld kU (by decide), hld kUni (by decide),
        hld kChecks (by decide), hst kI (by decide), hst kUni (by decide), hm₁, hI, ofNat_add_one,
        fun X => (hdrStore_hdr s.mem B X (show kI < 32 by decide) (show kU < 32 by decide) (by decide)).trans hU,
        fun X => (hdrStore_hdr s.mem B X (show kI < 32 by decide) (show kUni < 32 by decide) (by decide)).trans hN,
        fun X Y => (hdrStore_hdr _ B Y (show kUni < 32 by decide) (show kChecks < 32 by decide) (by decide)).trans
          ((hdrStore_hdr s.mem B X (show kI < 32 by decide) (show kChecks < 32 by decide) (by decide)).trans hC),
        mask_and1', sbb_self, cmp_imm_cf (show i + 1 < 2 ^ 63 by omega_using [hi]) (show 17 < 2 ^ 31 by decide)]
      have e1 : (mask u &&& 1) + BitVec.ofNat 64 uni = BitVec.ofNat 64 (uni + u.toNat) := by
        cases u
        · simp [mask_false]
        · simp [mask_true]; rw [← BitVec.ofNat_add, Nat.add_comm]
      rw [e1]
      refine ⟨?_, rfl⟩
      rw [show (BitVec.signExtend 64 (17 : BitVec 32)).toNat = 17 by decide, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i + 1 < 2 ^ 64 by omega_using [hi]),
        Nat.mod_eq_of_lt (show uni + u.toNat < 2 ^ 64 by cases u <;> simp <;> omega_using [huni]),
        Nat.mod_eq_of_lt (show ch < 2 ^ 64 by omega_using [hch]), rcx_stat2]
      by_cases h1 : i + 1 < 17 <;> by_cases h2 : uni + u.toNat < ch <;> simp [h1, h2]) rfl)
      fun s₂ ⟨⟨hcx₂, hm₂⟩, k₂⟩ => ?_
    refine WP.mono (WP.keep [] (Q := fun t => t.mem = s₂.mem.writeW (off B (8 * kStat))
      (BitVec.ofNat 64 (if i + 1 < 17 ∨ uni + u.toNat < ch then 4 else 1))) (by
      xrun [State.ea, hdr, (k₂.gpr (by decide) : s₂.gpr .rdi = s₁.gpr .rdi).trans hdi₁, hdrOff,
        show s₂.wr = s.wr from k₂.2.2.trans k₁.2.2, hs kStat (by decide), hcx₂]) rfl)
      fun t ⟨hm, k⟩ => ⟨by rw [hm, hm₂, hf]; rfl, ((k₁.trans k₂).trans k).mono (by decide)⟩

end VG.Proof.RsaKeyGen.X86_64
